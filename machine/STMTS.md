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

## FILL 3 composition shape (pinned 2026-11-09, piece 3)

The fixed-program shape for the `hsShape` target
(`Light.Solves Light.mpTask P p Tn need`), decided against the adapter
chain's evidence:

**The stage/cache/restore procedures ride INSIDE the caller's own program
`P`; the append direction is the upstream host's, after `P`.**

Evidence chain (all read at the pinned sources):
- `MachineAdapter.appendAPSP` consumes
  `hs : Light.Solves Light.mpTask P p Tn need` and hands it to
  `Light.Sec3.isHost_ap` (`Programs/Sec3/Theorem21b/Apsp/Host.lean:276`),
  which builds the host's four procedures AFTER the solver's program:
  `[apInitBody, clipBody, apOutBody, apBody p P.length (P.length + 1)
  (P.length + 2)]` at entry `P.length + 3` — the append direction belongs
  to the host, not to the caller's composition.
- `MachineAdapter.lean`'s own docstring: "The upstream host appends four
  finite procedures … These are composition lemmas. They do not supply an
  improved min-plus program."
- `Light.Solves.append` (Lang/Tasks.lean:108) extends a solver's program by
  trailing procedures with the entry index fixed — the chaining primitive
  while the port lands the caller's procedures.
- The fills' slots are conditional: `cacheReads_of_solves` /
  `restoreReads_of_solves` consume `Light.Solves` hypotheses; the cache and
  restore bodies still trail board-side (CacheFill.lean's header). The
  caller's product-round body is the named summit (MACHINE_OBLIGATIONS,
  "Min-plus caller: actual caller matching mpTask, including all arrays,
  scans, control flow, and word bounds"); `hdom` awaits that program's
  `completeCost` step-count bound. `Solves.append` cannot create a solver —
  no chaining closes the summit without the bodies.

Landed composition content (`CallerSolves.lean`, piece 3): the fill slots'
append persistence (`cacheSlot_append`, `restoreSlot_append`) and the
schedule threading's append persistence (`thread_step_append`, the
two-stage analog of piece 1's `stageEnds_behind_append`). The twin filing
statement — `Race.bound` at the conservative exponent `2994999/1000000`
via `ConservativeAdapter.conservativeStatementOfLedger` — is stated in its
own module (`TwinRaceBound.lean`); no root swap; the filing call is the
owner's.

## The universal body's status (L7 — the universal-body session, 2026-11-09)

`CallerUniversalBody.lean` lands the instance-free program term GREEN
(stages A–C): the fixed register map, the computed-index write pass
(`set IdxR (t·n) ;; set DstR (x.c + t·n) ;; pass J (v Nreg) (v DstR)
(v Tmp)`), the level-doubling `univWhile` (exactly `mpRounds W` rounds in
one fixed term), the nested-behind caller program (renumbering-consistent
where the per-instance skeleton's flat `++` is not), `univRowPass_runs`
and `univRound_runs` (the run-derivation green through the row pass and
the round slice, at the caller program), and the quadratic `univTn`.
STATED, not yet discharged (the lane's one open seam):
`WireUnivTarget` — the while induction over `Ends.while` with `UnivInv`
(the invariant def) and `UnivPins_set` (landed) as its bricks; the exit
arithmetic and the budget close by landed lemmas. When it discharges:
the entry assembly (prologue + wire), the `Light.Solves` packaging (the
named-premise bundle: hslot, hret, hflag, hok, hrows (FILL 1), hidentU,
hkeptU), and `twinUniv_of` fires `Race.bound` 2994999/1000000 — the
filing package assembles at THAT commit.

## The summit body's data-flow design (L7 — pinned 2026-11-09)

The design narrative is `DATAFLOW.md` (the per-round cell semantics: the
construction's refinement recurrence, the machine reading of the stage's
score table as the oracle's evidence, the named remaining sub-design —
the parameter concretization). The defs are `CallerDataflow.lean`
(`oracleAnswerOf`, `refineStep` — byte-shaped to `cert_scores` and
upstream `refine`). The remaining sessions: the reading lemma (the
machine-stage→oracle-answer correctness at one round, then all rounds),
the Seg-half assembly (discharging `SegTarget`, then `CallerTarget` via
the (b) packaging), and the step count for `CallerHdom`.

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
