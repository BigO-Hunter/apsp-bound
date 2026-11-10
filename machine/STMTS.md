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

## The universal body's status (L7) — CURE (b) landed, 2026-11-10

`CallerUniversalBody.lean` is GREEN with the WRITE SHAPE REWRITTEN
(exit 0, 0 errors, 0 sorryAx, standard-3 axioms, olean 3,539,248 B).

THE REVERSAL, RECORDED. Cure (a) landed a restricted task `mpTaskRounds`
(`Pre' := MatInst.Pre ∧ mpRounds U <= n`, commit 7b6ac0b) on the argument
that `hregion` was underivable from `mpTask.Pre`. That part is true and
stands: the row pass wrote round `t`'s row at `x.c + t*n`, escaping the
product region as soon as `mpRounds W > n` (n=1, U=100 gives mpRounds 100 =
16 > 1), and no `Need` can express the containment. But the restriction is
UNCONSUMABLE: the filing chain needs `IsHost mpTask apTask`, and Host.lean
instantiates the lower solver at bounds ~3nU where `mpRounds U' <= n'` fails
pointwise. A class argument justifies the bound's VALUE, never the pointwise
host premise.

CURE (b) — the body rewrite. The row broadcast was an implementation
choice, not mathematics: the only cell any landed conclusion consumes is
the product's head `x.c` (`MinPlusIdentity` takes `bracketCell x 0 0 = x.c`
as its hypothesis and concludes EVERY cell's minPlusEntry; `mpTask.Post`'s
Seg half follows from that premise). So `univRowPass` now writes ONE cell,
guarded to round 0 (rounds t >= 1 deliver the fold seeded at ROW t's head,
a different value):

    univRowPass := .ite (v Rt =' k 0) (.store (v Out) (v Tmp)) .skip

Write set `{x.c}`, for EVERY instance, inside `[x.c, x.c + n²)` for every
n >= 1. The certified stage post (`SameOutside3` at sb/bb/mb) and `KeptBut`
hold unconditionally; `hregion` is NEVER NEEDED; the task stays
UNRESTRICTED. The register-accumulation formulation (the brief's words) is
the same program up to the fact that nothing between round 0 and the loop's
exit reads or writes the head — disclosed at the def rather than silently
substituted.

Knock-on simplifications, all disclosed at their defs: `UnivPins`'s address
clause collapses to `x.c < lim.space`; `UnivInvAll` drops BOTH all-cells
clauses (nothing left for them to justify); `univRowPass_runs'` and
`row_disjoint` deleted; `univRound_runs` and `univRound_runs'` merge into
one; `univLevel_runs` rewritten (327 -> 216 lines, no row tracking);
`univRowB` is the constant 7 where the row pass cost `13n + 16`;
`univRoundB n = callerTt n + 18`. `hregion` removed from the signatures of
`univLevel_runs`, `wireUnivTarget_of` and `prologue_runs`.

RESTORED BRICKS (2 of 4, the two that survive the write-shape change):
`mpRounds_le_word`, `UnivInvAll_zero_self`. `pow_signedLevels_le` survives
under its landed name `pow_pred_signed_levels_le` (+
`two_mul_lt_pow_signed_levels`), already consumed by `wireUnivTarget_of`.
`univProloguePins_eq_argsOf` NOT restored — it needs the callSite's nine
field projections in slot order and nothing in the landed chain consumes it
(the correspondence rides the named `hvals` premise).

STILL OPEN — the filing chain, in order. (1) The ENTRY ASSEMBLY: compose
`WireUnivTarget` (proved by `wireUnivTarget_of`) with `PrologueTarget`
(proved by `prologue_runs`) into `CallerTarget` at `callerProgramUniv`; both
halves are green, only the composition lemma between them is missing.
(2) The `Solves mpTask` bundle: hslot, hret, hflag, hok, hrows (FILL 1),
hidentU, hkeptU. (3) `twinUniv_of`: CallerTarget + hn + hdom ->
`Twin.race_bound` 2994999/1000000, lifting `CallerPost.twin_of_CallerTarget`
to the universal body. Then `Solves mpTask -> isHost_ap -> Solves apTask ->
realized_apsp -> SolvedInTime`.
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

## Entry-assembly convention, confirmed by reading (2026-11-10)

Recorded so the next session need not re-derive it.

The stage frame is Candidates=0, Len=1, Height=2, Active=3, Rows=4,
Scores=5, Remaining=6, Base=7, Free=8, Chosen=9, Unused=10
(`DenseCanonicalSelectionRound`), with the universal body's own scratch map
Out=11, Nreg=12, U2=13, Lvl=14, Rt=15, IdxR=16, DstR=17, J=18, Tmp=10.

`univPrologue` consumes the mpTask frame in registers 0..5 (`[n, U, a, b, c,
fr]`) and PRODUCES exactly that stage frame — which is why the two
conventions do not clash, and why `UnivPins` with `vals = argsOf callSite ++
[fr]` is satisfiable: `Out := v 4` yields `x.c`, `Nreg := v 0` yields `n`,
`U2 := k 2 *' v 1` yields `2U`. ORDER MATTERS and is already correct in the
def: `Height := v 1` is read BEFORE `Len := v 0` overwrites register 1.

Consequences for the run lemma's conclusions:
- `UnivInvAll`'s all-cells clause holds because the prologue writes ONLY at
  Active (`ab = fr`) and Remaining (`mb`); both lie at or above `ab`, and
  `hbelow : x.c + n*n <= ab`, so the product region is untouched — exactly
  the `KeptBut` argument, with `frC <= ab`.
- `StageReads` at `ell = 0` is satisfiable with the ROWS taken from the
  initial memory (`rows p i := mu0 (rb + p*I + i)`): the prologue never
  writes the rows region, the active bits are all 1 from the first pass, and
  the remaining flags are all 1 from the second. This is the same "the array
  keeps the instance's own values" device the all-cells clause uses.

## The prologue's contract now has a name (2026-11-10)

`PrologueTarget` in `CallerUniversalBody.lean` states the entry assembly:
`univPrologue` from the mpTask frame ends in `UnivInvAll ... 0` within
`univProB x.n`. It is STATED (lane pattern, no sorry), and it is the sole
missing premise of `wireUnivTarget_of`.

The frame correspondence is DERIVED, not assumed, and recorded at the def:
`vals` must be `[n, n, U, fr, fr+n, fr+n+n², fr+2n+n², fr+n+n², fr]` in the
instance's `candidates, length, height, activeBase, rowsBase, scoresBase,
remainingBase, baseBase, fr` slots — each one traced to the prologue `.set`
that produces it. Consequences: the writes land only at `ab` and `mb` (both
`>= x.c + n*n`), which is why the product region survives and `KeptBut`
holds; `Height := v 1` must read register 1 before `Len := v 0` overwrites
it; and the rows region is never written, so level-0 stage reads use
`rows p i := mu0 (rb + p*I + i)`.

Budget verified: 13 sets (40 steps) + two passes (13n+6 each) = 26n+52 <=
27n+64 = `univProB n`.

**LANDED (2026-11-10): `prologue_runs` proves `PrologueTarget`**
(standard-3 axioms, no sorryAx). The proof is the fifteen-step `Ends`
chain the def's text dictates: eleven frame `.set`s (36 steps), the two
`Ends.pass` applications at `fun _ => 1` (`13n + 6` each), the two counter
sets (4) — `26n + 52 <= 27n + 64 = univProB n`. Register bookkeeping runs
through the library's frame idiom (`Ends.setToThen` / `Ends.setTo`, the
locals as a list); the memory argument is the two `wrote` regions: the
writes land only at `ab` and `mb`, each at or above `x.c + n*n`, so the
product rows are untouched (the all-cells clause, from `hbelow`), the
product cell keeps `mu0 x.c`, and `KeptBut` holds below `frC <= ab`. The
level-0 stage reads are the "the array keeps the instance's own values"
device (`hactive`, `hrows`), with the rows sampled from `mu0` at `rb`.

Two corrections, both disclosed at the def:
1. the correspondence prose was one buffer early on `baseBase` /
   `remainingBase`. The def writes the buffers in the order active, rows,
   scores, base, remaining, so `baseBase = fr+2n+n^2` and
   `remainingBase = fr+3n+n^2` (the stage's free pointer is `fr+4n+n^2`).
   The def was always right; only the prose was wrong. `univProloguePins`
   now holds the nine values the proof pins.
2. `PrologueTarget` first took ONE `vals` as both the entry frame and the
   pin list — impossible, since the entry is the six-register mpTask frame
   and the pins are the nine-value stage frame the prologue PRODUCES. The
   def now takes the entry frame separately (`frameVals`).

The instance premises the lemma consumes: `hbelow` (`x.c + n*n <= ab`),
the buffer stack's fit `fr + 4n + n^2 <= lim.space` (whence every op
value's word bound, with `space <= word`), `|2U| <= word`, `1 <= word`,
`mpRounds W <= n`, and the two read devices above.

**THE ASSEMBLY SEAM (the next opener — a finding, not bookkeeping).** The
`Light.Solves` bundle now has one premise that does NOT follow from
`mpTask.Pre` plus a polynomial `Need.Ok`: `hregion : mpRounds W <= x.n`.
It is load-bearing: the row pass writes round `t`'s row at
`x.c + t*n`, so when `mpRounds U > n` those stores land above `x.c + n^2`
— inside the buffers the stage reads — and both the certified stage post
and the final `KeptBut` fail. No `Need` can supply it (a `Need` bounds
`word`, `cells`, `depth`; `Pre` bounds `U` only from below, via `AbsLe`).
Counterexample shape: `n = 1`, `U = 100` gives
`mpRounds 100 = 2*(log2 200 + 1) = 16 > 1 = n`.
Honest reading: the universal body solves the (min,+) task on instances
whose value bound fits the row budget (`mpRounds U <= n`) — the
`U <= 2^(n/2)` regime, which is the regime the filing's `timeUpTo`
supremum ranges over (`U <= n^k` per fixed k), but `Light.mpTask` itself
does not carry the constraint. Two cures, named and neither faked:
(a) restrict the task (`mpTaskRounds` with `Pre' := Pre /\ mpRounds U <= n`)
and re-wire the twin to that task; (b) make the body's row use
independent of the round count (accumulate the bracket value in
registers, no per-round row write).
