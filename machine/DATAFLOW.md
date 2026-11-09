# DATAFLOW — the caller's per-round cell semantics (L7 design, D7(b) FILL 3)

Status: design pinned at the score-table level; the parameter
concretization (the mod-p / band-batch encoding) is the named remaining
sub-design. Sources mirrored: upstream `MinPlusReduction.lean` (the
functional chain: `refine`/`bitScale`/`signedBitScale`/
`bounded_signed_eq_minPlus`), `StoredMinPlusAPSP.lean` (the dense-oracle
conversion), and the landed L6(a) `cert_*` contracts
(`DenseCompositeCaller.lean`). The machine realization decision is
STMTS.md's INSIDE shape (`CallerBody.lean`/`CallerBodyStmt.lean`).

## The construction's per-round recurrence (upstream's own data-flow)

`bitScale O 0 A B = 0`; `bitScale O (n+1) A B = refine O A B (bitScale O n
(half A) (half B))` — per level t:

1. the level-t inputs are the HALVED-encodings (`half`, entry-wise with
   the remainder bookkeeping) of the level-(t-1) inputs;
2. the level-(t-1) product `C = bitScale O t (half A) (half B)` is the
   COARSE estimate: `coarse_bracket` gives, per entry (i, j),
   `2·C[i,j] ≤ A[i,k]+B[k,j] ≤ 2·C[i,j]+2` for the bracket;
3. TWO adaptive tests per level (the lower test has priority):
   - lower: `O A B (fun i j => -(2·C[i,j]))` — "the min is exactly
     2·C[i,j]";
   - upper: `O A B (fun i j => -(2·C[i,j]+1))` — "the min is exactly
     2·C[i,j]+1";
   - neither: the min is ≥ 2·C[i,j]+2;
4. `refine` assembles the level-(t+1) entry from the tests.

The oracle's triangle form: `O A B T i j = true ↔ ∃ k, A[i,k]+B[k,j]+
T[i,j] = 0` — the test matrix T encodes the bracket threshold
negatively. The signed levels add the sign bracketing
(`signedLevels W = (2W).log2 + 1`, two adaptive tests per level —
`mpRounds W = 2·((2W).log2 + 1)` = `CallerRounds.mpRounds_even`'s
two-call blocks).

## The machine reading: the stage call as the oracle's evidence

At the caller's pinning, ONE stage call (procedure `stageProcLayered`,
the certified stage at the L5/L6 pinning) produces, per its certified
post (L6(a) `cert_*`):

- `cert_scores`: `μ₁ (sb + p) = DenseScoreTablePass.scores active rows I
  p` for `p < P` — the stage's score table: the per-candidate
  active-incidence counts, materialized at the scores buffer `sb`
  (slice 1's `callerSb fr P I`);
- `cert_chosen`/`cert_argmin`: the chosen candidate — the argmin over the
  remaining flags of the score table;
- `cert_row`/`cert_mask`: the selected row copied to the base buffer and
  the chosen flag cleared (`maskCleared cs₁.toFinset remaining`);
- `cert_frame`: the three written regions preserved (`SameOutside3` —
  `chain_runs`/`chain_keptBut`).

THE ORACLE-ANSWER READING (the bridge's pinned shape): the oracle's
triangle test at a scheduled round reads the stage's score table — the
nonzero-score candidates are the triangle witnesses the test asserts.
The reading's def (`CallerDataflow.oracleAnswerOf`): the answer at
candidate p is the nonzero test on the certified score cell `μ₁ (sb +
p)`. This is byte-shaped to `cert_scores` (consumed, not re-proved).

## The named remaining sub-design: the parameter concretization

The identity between "the nonzero incidence count at candidate p" and
"the triangle test at the bracket threshold" runs through the
construction's ENCODING: the mod-p tables, the band batching, and the
bracket-threshold encodings (`-(2C)` / `-(2C+1)` as the dense-oracle's
third-table entries). Upstream pins these in the Batch chapter
(`OParams`/`OQuery`/`OProg` — the procedures 74–84: residTab, smallTab,
rowTab, divTab, zTab, writeSrc, queries, oracle). Mirroring that
encoding at the caller's concrete pinning is the remaining sub-design —
its home is the upstream Batch chapter, consumed as the premise shape
(D7's boundary: the encoding's correctness is upstream's
`DenseOracleCorrect`-conditioned chain, never claimed here).

## The product-entry accumulation

The bracket refinement's machine state: the per-(i, j) bracket lives in
the caller's memory as the level-t product estimate at the product
region `c` (the layout: the matrices at `x.a`/`x.b`, the product at
`x.c`, the stage scratch above — slice 1's layout at the caller's free
pointer). The level-(t+1) entry = `refineStep` of the level-t entry and
the two stage answers (`CallerDataflow.refineStep` — upstream `refine`'s
recurrence at the pinning). The schedule's `mpRounds W = 2·(log₂ 2W+1)`
calls drive the signed levels to the `scaleBound`-tight bracket
(`bounded_signed_eq_minPlus` closes the value identity at the top).

## What the proofs consume (the defs, `CallerDataflow.lean`)

- `oracleAnswerOf` — the stage-score → oracle-answer reading (byte-shaped
  to `cert_scores`).
- `refineStep` — the bracket-doubling recurrence (byte-shaped to
  upstream `refine`'s if-then-else).
- the premises they ride: the landed chain (`chain_runs`/`chain_keptBut`)
  and the oracle premise (`OracleCorrect` — upstream's own shape).

## The remaining sessions

1. the parameter concretization (the mod-p/band encoding at the pinning —
   the upstream Batch chapter mirrored);
2. the machine-stage→oracle-answer LEMMA (the reading def's correctness
   against the certified scores, at one round, then all rounds);
3. the Seg-half assembly (the bracket accumulation into
   `minPlusList x.n x.A x.B` at `x.c` — discharging `SegTarget`, then
   `CallerTarget` via the (b) packaging);
4. the step count for `CallerHdom` (the budget structure B/Tt/9+2 over
   mpRounds; `costBoundOfEventualDomination`).

Credits (constructions first, filer last): shresh (shreshth-s) — the
composite-incidence construction and the oracle functional chain; Josh
Alman and Virginia Vassilevska Williams — arXiv:2610.06783; Li Xuanji —
the verified ten-term construction and word-RAM compiler; Joshua Wharton
(QFEX) — the canonical adapter arrangement, the refinement parameters,
and the machine-obligations record; Hrishik Sai Bojnal — the verified
frontier being refined and the refined numerical certificate this body
targets.
