# PRODUCT_BODY — the product-round body's data-flow design (L7, D7(b) FILL 3)

Status: design pinned 2026-11-09 (the data-flow session). The defs are
`CallerRun.mpBodyWithWrites` / `CallerWire`'s wire machinery (landed); the
assembly, the step count and the domination land in `CallerSummitBody.lean`
(this session). The oracle premise and the (min,+) product are NAMED
PREMISES throughout — D7's boundary stands; nothing here claims a product.

## 1. The loop structure over mpRounds

The product core is `mpRounds W = 2·((2W).log2 + 1)` rounds (`mpRounds_eq`,
the upstream `scheduledCalls (signedLevels W)` — both adaptive tests at
every signed level). One round, at the pinned layout, is:

    roundSlice 6 Out x t  :=  .call 6 callArgs Tmp ;; mpBodyWritesRow Out Tmp x t

— one certified stage call (procedure 6 of the round program at the bare
level; `stageProcIn = 1 + cacheProg.length + restoreProg.length + 6`
inside the caller program), then the row-t write pass: `x.n` stores, entry
`u` writing cell `x.c + t·x.n + u` (`bracketCell x t u`) from register
`v (Tmp + u)`. The whole body is the fold of the rounds
(`mpBodyWithWrites`); the schedule drives the signed levels to the
`scaleBound`-tight bracket (`bounded_signed_eq_minPlus` closes the value
identity at the top).

## 2. The three data sources and their meeting points

Per round t, three certified sources meet at the product region:

1. **The cached rows** (the rows buffer `rb`, written by the cache fill,
   FILL 1). Meeting point: the stage's READ evidence — `StageReads`' rows
   clause (`μ (rb + p·I + i) = rows p i`). The cached rows are what the
   score table counts; they are also what the bracket tests' threshold
   encodings range over. The reads persist round-to-round (`reads_carry`:
   the rows/active regions lie below the scores region — the layout).
2. **The oracle answers** (read off the scores buffer `sb`). Meeting
   point: the certified score cells — `cert_scores`: `μ₁ (sb + p) =
   scores active rows I p` — read through `oracleAnswerOf` (the nonzero
   test) into the round's answers (`reading_at_one_round` /
   `readingAllRounds_of_socket`, given the encoding-identity socket
   `henc`). The answers are the round's two adaptive tests
   (`tests t = (lower t, upper t)`); `refineStep`/`refineWrite` assemble
   the level-(t+1) bracket from the level-t bracket and the tests.
3. **The cs₁-selected row** (the chosen candidate's row, copied to the
   base buffer `bb`; its flag cleared at `mb`). Meeting point: the
   SCHEDULE's evolution — `cert_mask`: the round's flag state becomes
   `maskCleared cs₁.toFinset remaining`, which is exactly the next
   round's read mask (`chain_from`'s induction step). The selected row is
   the greedy state; its clearing is what makes the mpRounds schedule
   well-defined (the flag budget `hflag` gates every round's slot).

The fourth source is the bracket state itself: the product region's
cells, seeded by the construction's initialization, refined in place —
the per-round invariant below.

## 3. The invariant carried between rounds

After round t, at the run's state σ_t:

- **Pins** (`WirePins`): the Out register holds `x.c`; register 0 holds
  zero; every write address `Out + (t'·x.n + j)` is in-range and hits the
  product region; the frame registers 0–8 still carry the stage's argument
  list (the call updates only `Tmp`). Survives every round
  (`WirePins_update`).
- **Reads** (`StageReads` at the evolved mask): the cached rows and active
  bits unchanged (below the scores region), the flags at
  `maskCleared cs₁.toFinset …` — carried by `reads_carry` from the
  round's certified post.
- **The fold**: cell `(0,0)` holds
  `bracketAccumulate (seed) tests (t+1)` — the wire (`wire_from_slots`):
  round 0 writes the delivered fold into `(0,0)`, every later round keeps
  it (`roundZero_writes` / `roundKeeps`).

After ALL rounds: the fold identity at every cell (the construction's own
conversion — `MinPlusIdentity`, the named premise) turns the bracket
state into the `minPlusEntry` values, and `seg_of_entries` bridges the
row-major layout to `minPlusList`'s `q ↦ (q/n, q%n)` order. The frame
half (`KeptBut`) rides the KeptBut premise (below).

## 4. The premise inventory (Tier-A / Tier-B)

**Tier-A — consumed directly by the assembly (`CallerSummitBody.lean`):**
- `hbus₀` — the wire-run's fold delivery, ∀ start state (bare level,
  `CallerRun`'s `BracketFinal` shape). LANDED as a theorem modulo Tier-B:
  `CallerWire.wire_from_slots` at the task frame; the ∀-lift rides the
  pinning/reads premises' ∀-shape.
- `hident₀` — `CallerRun.MinPlusIdentity` (the construction's own
  conversion; D7 boundary: a premise, never claimed). Its producer is the
  parameter concretization + upstream's `bounded_signed_eq_minPlus`
  chain.
- `hkept` — the KeptBut half at the caller program, ∀ start state. Named;
  discharge path (next session's opener): the `aux_wire_from_slots`
  pattern carrying `SameOutside3` + `keptBut_of_chain`, under `hregion`
  (the write-region containment below).

**Tier-B — the sub-bundle from which the landed machinery derives
Tier-A's `hbus₀` (each named, producer documented):**
- `hslots` — the certified slot family at the TIGHT clock `callerTt
  n = 25·(n² + 7n)` (the selection round's cost comparison,
  `time ≤ 25·(P·I + 6·P + I)` at `P = I = n`). Producer: the L5/L6(c)
  wrapper re-clocked to the tight comparison (the stage's own `solvedIn`).
- `hret` — the oracle return premise: the stage call's return register at
  round t carries `bracketAccumulate (μ (x.c + t·x.n)) tests N`. THE
  oracle chain's content (D7 boundary).
- `hflag` / `hok` — the restart pinning's flag budget and the Ok fit.
- `hpins₀` / `hreads₀` / `hidx` / `hTtmp` — the caller-frame pinning at
  the task's start state (the PROLOGUE's deliverable: the register
  convention bridge from `mpTask`'s `[n, U, a, b, c, fr]` frame to the
  stage's nine-value frame and the pre-loaded index registers; the index
  registers miss `Tmp`).
- `hregion` — the write-region containment: `mpRounds W ≤ x.n` — every
  write address lands inside the product region `[x.c, x.c + n²)`. With
  it, `hprodaway` (the product cells away from the reads regions) is
  derivable from `x.Pre` + the layout, and the KeptBut induction closes.

## 5. THE UNIVERSAL-BODY SEAM (this session's design finding)

`Light.Solves` quantifies ONE fixed program over ALL instances, but the
landed write shapes bake the instance into the register indices
(`v (t·x.n + u)` — a different register per `x.n`). The per-round write
pass is therefore an INSTANCE FAMILY, and the run-derivation this session
lands (`summitEnds_of_premises`) is the PER-INSTANCE Ends at the caller
program with the instance's body.

The universal term that discharges `CallerTarget` (and hence, through
`CallerPost.summit_of_CallerTarget`, `SummitSlot`) computes the indices
instead of baking them. LANDED STATE (2026-11-09, the universal-body
session, `CallerUniversalBody.lean`, stages A–D): the program term is
GREEN — fixed register map (Out/Nreg/U2/Lvl/Rt/IdxR/DstR/J, all missing
the stage frame 0–8 and Tmp), `univRowPass` = `set IdxR (t·n) ;; set DstR
(x.c + t·n) ;; pass J (v Nreg) (v DstR) (v Tmp)` (the per-entry addressing
through the upstream canonical `pass` combinator — the design sketch's
per-entry `set IdxR (t·n+j)` advance is subsumed by `Ends.pass`'s
`dst + c` rule, and the stored value is the call's single delivery
register `Tmp`: `v (Tmp + j)` is not expressible with a computed index,
and no landed conclusion consumes the other entries' values);
`univWhile` = the level-doubling loop (test `v Lvl ≤' v U2`, two
certified rounds per level) — exactly `mpRounds W` rounds in one term;
the caller program composed by NESTED `Program.behind` (the flat `++` of
the per-instance skeleton is not renumbering-consistent for
cache/restore layers of length > 0); the run-derivation GREEN through the
row pass (`univRowPass_runs`, the inner while owned by `Ends.pass`) and
the round slice (`univRound_runs`, `Ends.callLast` at the caller program
+ `reads_carry` + the row pass). The clock: `univTn n U = mpRounds U ·
univUnitB n + univProB n`, quadratic, `univTn_le`.

THE NAMED REMAINDER (the lane's open seam, narrowed by this session): the
wire induction is now DISCHARGED — `wireUnivTarget_of` proves
`WireUnivTarget` by `Ends.while` at `signedLevels W` iterations
(standard-3 axioms, no sorryAx). The invariant is `UnivInvAll` (the
all-cells tracking), the body is `univLevelBody` (two certified rounds at
levels 2ℓ and 2ℓ+1 — the second at the first's evolved mask — plus the
three pin-preserving counter sets, brick `univLevel_runs`), the exit is
`2^signedLevels W > 2·U` via `pow_pred_signed_levels_le` /
`two_mul_lt_pow_signed_levels`, and the budget closes on
`univWhile_cost` (the test costs 5 = `univTestB - 1`, so the while total
`SL·(6 + univLevelB) + 6` is that lemma's left side exactly).

TWO DISCLOSED AMENDMENTS, neither silent:
1. `WireUnivTarget`'s hypothesis is now `UnivInvAll … frC 0`, not
   `UnivInv … 0`. The stronger form is REQUIRED: the loop's all-cells
   tracking is load-bearing for every later round's row pass and for the
   cell-(0,0) fold's survival, and it is not derivable from `UnivInv` —
   only the prologue establishes it. Supplying it is the entry assembly's
   obligation, which is exactly the next seam.
2. The discharge also needs `x.U = W` (EQUALITY, not `≤`: both sides of
   the loop test move with the bound, so `≤` breaks the exit and `≥`
   breaks the entry), `0 < W`, and the two word-fit premises
   (`|2·U+1| ≤ word`, `1 ≤ word`).

LANDED (2026-11-10): the entry assembly. `prologue_runs` proves
`PrologueTarget` — thirteen register sets (40 steps) + two `Ends.pass`
applications at `fun _ => 1` (`13n + 6` each) = `26n + 52 <= univProB n`,
ending in `UnivInvAll … 0` (standard-3 axioms, no sorryAx). The frame
correspondence is now the lemma's hypothesis list (`univProloguePins`,
`univPrologueMid`, `univPrologueLocals`), with the two prose corrections
disclosed at the def (the buffer order is active, rows, scores, base,
remaining — so `baseBase = fr+2n+n²`, `remainingBase = fr+3n+n²` — and
the entry frame is `frameVals`, separate from the pins).

STILL OPEN (and this is now a DESIGN finding): the `Light.Solves`
packaging's `hregion : mpRounds W <= n` does NOT follow from
`mpTask.Pre` + a polynomial `Need.Ok`. The row pass writes round `t`'s
row at `x.c + t‧n`, so `mpRounds U > n` puts those stores above
`x.c + n²`, inside the buffers the stage reads — the certified stage post
and the final `KeptBut` both fail (`n = 1, U = 100` gives
`mpRounds 100 = 16 > 1`). Two cures, named, neither faked: (a) restrict
the task (`mpTaskRounds`) and re-wire the twin; (b) drop the per-round
row write (accumulate the bracket value in registers). Until one lands,
`summitSlotUniv_of` / `twinUniv_of` cannot fire `Race.bound`
2994999/1000000 for `mpTask` as stated.

## 6. The step count (landed this session)

Per-round budget `callerB n = 9 + 2 + callerTt n + 5·n + 1`:
the call's argument cost 9 (`callArgs_cost`) + the call overhead 2 + the
tight stage clock + the row pass (`x.n` stores at `Bw = 5`: two `var`s,
an `op`, a `var`, the store). The total clock:

    callerTn n U := mpRounds U * callerB n
                  = 2·((2U).log2 + 1) · (25·(n² + 7n) + 5n + 12)

— logarithmic in U (the schedule), quadratic in n (the stage scan + the
row pass). The domination (`CallerHdom callerTn`, proved): the host's
lifted clock `apTime Tn = Nat.clog 2 n · (Tn n (3nU) + 23n² + 29) + …`
is `O(n² · log² n)` per fixed κ, and `completeCost k n` carries
`log^{k+R+10} n · n²` with `R = 10⁹` — k := 0 dominates eventually with
C := 4.

## 7. What fires when the universal body lands

`SummitSlot` := ∃ P p Tn need, Solves ∧ PolyNeed ∧ completeCost-dom
(`CallerSummit.lean`). The witness is CONSTRUCTED here modulo the one
seam: `P := callerProgram mpBodyUniv cacheProg restoreProg cs`, `p :=
mpProc = 0`, `Tn := callerTn`, `need := callerNeed` (PolyNeed proved this
session); `Solves` = `CallerTarget` = the universal body's run-derivation
(§5); the domination = `callerHdom` (proved, §6). Then
`CallerPost.twin_of_CallerTarget` fires `Race.bound 2.994999` — the
filing package (Bound 2994999/1000000, SHA-at-firing-commit, credit
paragraph) assembles at THAT commit, per the lane convention.

Credits (constructions first, filer last): shresh (shreshth-s) — the
composite-incidence construction and the oracle functional chain
(thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc); Josh
Alman and Virginia Vassilevska Williams — arXiv:2610.06783; Li Xuanji —
the verified ten-term construction and word-RAM compiler; Joshua Wharton
(QFEX) — the canonical adapter arrangement, the checked selection round /
restart-loop driver, and the machine-obligations record; Hrishik Sai
Bojnal — the verified frontier being refined and the refined numerical
certificate this body targets.
