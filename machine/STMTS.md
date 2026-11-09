# STMTS — L5 statements (pinned restart-loop call site)

Milestone L5(a) of the APSP port campaign. Statements land here; the
Task/Solves/SolvedIn wrapper (L5(b)) proves them from the landed `loop_ends`
without re-proving anything. File: `DenseRestartSelectionLoop.lean`,
namespace `Light.DenseRestartSelectionLoop`.

## The pinning problem (from the L4(c) handoff)

`Solves` carries ONE fixed program, but the restart unrolling is
instance-sized (`program x` appends `loopBody x.rounds (rounds x.rounds)`).
Resolution: the min-plus caller (`mpTask`-matching) pins the instance sizes
`(P, R)` at its call site, and the wrapper is stated at the pinned instance.

**Caller-pinning source** (upstream `ArrayCompositeAlgorithm`, thin-matrix-results
@ 225c3747): `stage` runs `greedy O active primes k 1 remaining blockSizes []` —
`R := k` restarts over the `P`-sized candidate pool (`primes : Counts P`), with
the greedy premise `hsize : M + k ≤ (pool primes remaining).card` and
`greedy_correct`'s `hk : k ≤ (pool primes remaining).card`. That premise is
exactly `enoughFlags`: `R ≤ (flagged P remaining).card`.

## Statements

```lean
theorem flagged_card_le (P : ℕ) (remaining : ℕ → Bool) :
    (flagged P remaining).card ≤ P

theorem maskCleared_empty (remaining : ℕ → Bool) (p : ℕ) :
    maskCleared ∅ remaining p = remaining p

def Post (x : Inst) (μ : ℕ → ℤ) (μ' : ℕ → ℤ) : Prop
  -- ∃ cs, cs.length = x.rounds ∧ cs.Nodup ∧
  --   (∀ c ∈ cs, c < x.candidates ∧ x.remaining c = true) ∧
  --   (∀ p < x.candidates, μ' (x.remainingBase + p) =
  --     DenseArgminPass.bit (maskCleared cs.toFinset x.remaining p)) ∧
  --   SameOutside3 μ μ' x.scoresBase x.candidates x.baseBase x.length
  --     x.remainingBase x.candidates ∧
  --   (x.rounds = 0 → μ' = μ) ∧
  --   (0 < x.rounds → ∃ c, cs.getLast? = some c ∧ (base row = rows c) ∧
  --     (scores are the active-incidence scores) ∧ (∀ k, IsArgmin over
  --     maskCleared (cs.take k).toFinset of scores at cs.getD k))

def pinnedTask (x : Inst) : Task
  -- Inst := { y : Inst // y = x };  size := instanceSize ∘ (·.1);
  -- bound := height;  args := argsOf;  Pre := Pre (·.1) ∅;  Post := Post (·.1)

def taskTime (n _U : ℕ) : ℕ := 100 * n * n + 98 * n

def callSite (P R I h : ℕ) (active remaining : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (ab rb sb mb bb : ℕ) : Inst
  -- rounds := R, candidates := P, length := I, height := h, the five regions

theorem callSite_enough (P R I h : ℕ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (ab rb sb mb bb : ℕ)
    (hR : R ≤ (flagged P remaining).card) :
    enoughFlags (callSite P R I h active remaining rows ab rb sb mb bb)

theorem pre_of_reads {x : Inst} {μ : ℕ → ℤ} {fr : ℕ}
    (hAR) (hRR) (hbound) (hfl : plain flag reads) (hR : x.rounds ≤ flagged-card)
    (hlay : InOrder fr [(ab,I),(rb,P*I),(sb,P),(bb,I),(mb,P)]) :
    Pre x ∅ μ fr

theorem taskTime_ge (x : Inst) (hrounds : x.rounds ≤ x.candidates) :
    driverTime x ≤ taskTime (instanceSize x) x.height
```

## L5(b) statements (proved by the wrapper, not yet landed)

```lean
theorem post_of_loop_ends (x : Inst) … (h : loop_ends' conclusion at S₀ = ∅) :
    Post x μ μ'

theorem pinnedTask_solved (x : Inst) :
    Solves (pinnedTask x) (program x) 6 taskTime need

theorem pinnedTask_solvedIn (x : Inst) :
    SolvedIn (pinnedTask x) (fun n _ => ((100 * n * n + 98 * n : ℕ) : ℝ))

theorem callSite_meets … : Meets lim (program cs ++ Prog) 6 d (argsOf cs ++ [fr]) μ
    (taskTime (instanceSize cs) cs.height) ((pinnedTask cs).Post μ fr)
```

## The take-vs-erase decision

`Post` keeps the **take** form: the per-round `IsArgmin` mask is
`maskCleared (cs.take k).toFinset x.remaining` — byte-equivalent to the
`loop_ends` conclusion instantiated at `S₀ = ∅` (the `S₀ ∪` union vanishes).
The erase form (masks obtained by erasing later choices from the remaining
flags) carries the same information through `cs.getD k` but is NOT what
`loop_ends` exposes; using it would add re-derivation for zero content.

## Clock derivation (why `taskTime` is the pinned shape)

`driverTime x = x.rounds * callTime P I` (L4), `driverTime_le` gives
`≤ x.rounds * (100 * instanceSize x + 98)` when `R ≤ P`, and `R ≤ P ≤ n`
gives `driverTime x ≤ n * (100*n + 98) = 100*n² + 98*n = taskTime n U`.

## Discipline

Statements touch no board-model text (D7 boundary stands). The wrapper will
refine `loop_ends`; the round's `task_solved`/`solvedIn` pattern is mirrored.
Receipts: `DenseRestartSelectionLoop.verification.txt` per milestone,
standard-3 axioms only, no sorry/native_decide.

Credits (constructions first, filer last): shresh (shreshth-s) — the
canonical greedy restart loop (thin-matrix-results @ 225c3747); Alman–
Vassilevska Williams — arXiv:2610.06783; Li Xuanji — the verified ten-term
construction and word-RAM compiler; Joshua Wharton (QFEX) — the checked
selection round and machine obligations; Hrishik Sai Bojnal — the verified
frontier being refined.
