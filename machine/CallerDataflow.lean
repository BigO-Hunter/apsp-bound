import MinPlusCaller
import CallerSegments

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the design session's defs (the per-round cell semantics).

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the refinement
  parameters, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The design session's defs: the per-round cell semantics

The design is `DATAFLOW.md` (the narrative); this module pins its two
defs, byte-shaped to the landed contracts:

- `oracleAnswerOf` — the stage-score → oracle-answer reading: the answer
  at candidate `p` is the nonzero test on the certified score cell
  `μ₁ (sb + p)` — byte-shaped to L6(a) `cert_scores` (consumed, not
  re-proved).
- `refineStep` — the bracket-doubling recurrence: the level-(t+1)
  product entry from the level-t entry and the two adaptive tests —
  byte-shaped to upstream `MinPlusReduction.refine`'s if-then-else (the
  lower test has priority; neither test means the min is at least
  `2·C + 2`).

D7's boundary stands: the oracle premise (`OracleCorrect`) is upstream's
own shape, never claimed as proved; no (min,+) product is claimed in
this module.
-/

namespace ThinMatrix.CallerDataflow

open ThreeSumApsp

/-- The stage-score → oracle-answer reading: the oracle's answer at
candidate `p` is the nonzero test on the certified score cell
`μ₁ (sb + p)` — the score table L6(a) `cert_scores` materializes. -/
def oracleAnswerOf (sb P : ℕ) (μ₁ : ℕ → ℤ) (p : ℕ) : Bool :=
  decide (p < P ∧ μ₁ (sb + p) ≠ 0)

/-- The bracket-doubling recurrence: the level-(t+1) product entry from
the level-t coarse entry `C` and the two adaptive tests — upstream
`MinPlusReduction.refine`'s if-then-else at the caller's pinning (the
lower test has priority; neither test means the min is at least
`2·C + 2`). -/
def refineStep (C : ℤ) (lower upper : Bool) : ℤ :=
  if lower then 2 * C else if upper then 2 * C + 1 else 2 * C + 2

#print axioms oracleAnswerOf
#print axioms refineStep

end ThinMatrix.CallerDataflow
