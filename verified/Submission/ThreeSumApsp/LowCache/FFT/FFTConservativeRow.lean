/-
Copyright (c) 2026. APSP port campaign: L3(e) the conservative row.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the construction and the affine 47-check battery
  (`AlignedCertificate.lean`, ported byte-identically) whose conservative
  instantiation this row lands.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  frontier row this notch beats.
- Joshua Wharton (QFEX) — the rational retune procedure whose final squeeze
  this row deliberately avoids (APSHP_DELTA sequence step 1).
- Hrishik Sai Bojnal — the verified frontier being refined.

# L3(e): the conservative row takes the notch

The campaign contract's conservative row (APSHP_DELTA recommended sequence,
step 1): run the ledger at slack parameters — delta = 1/200 with the full
1/1000000 margin (0.005001 total, inside the demanded 0.005-0.006 band) — so
that any verified row below the ten-term frontier de-risks the tight final
certificate.

M3d kernel-checked the conservative battery (`conservativeMargins`); the two
binding promotions (cache-encoding and residual-query savings) are
enclosure-conditional theorems over the pinned T/G/q1 boxes. This file adds
the row itself: the exponent identity (3 - 0.005001 = 2.994999), the strict
frontier comparison, the notch size, and the target-shape of the battery
(25 delta cells at the floor, 22 geometry cells at 0/1). No board-model
text is touched; the D7 boundary stands.
-/
import Submission.ThreeSumApsp.LowCache.FFT.FFTConservativeInstance

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ThinMatrix.LowFFTCost

open ThinMatrix.AlignedCertificate

/-- The verified ten-term frontier row: 2.9955607647814 (Li Xuanji's
construction; Bojnal's verified frontier). -/
def verifiedFrontier : ℚ := 29955607647814 / 10000000000000

/-- The conservative row's exponent: `3 - (1/200 + 1/1000000) = 2.994999`. -/
theorem conservative_exponent_eq :
    (3 : ℚ) - (conservativeDelta + conservativeMargin) = 2994999 / 1000000 := by
  norm_num [conservativeDelta, conservativeMargin]

/-- The conservative row takes the notch: its exponent sits strictly below
the verified ten-term frontier. -/
theorem conservative_row_below_frontier :
    (3 : ℚ) - (conservativeDelta + conservativeMargin) < verifiedFrontier := by
  norm_num [verifiedFrontier, conservativeDelta, conservativeMargin]

/-- The notch size: the frontier exceeds the conservative row's exponent by
`5617647814 / 10^13` (≈ 5.62 × 10⁻⁴). -/
theorem conservative_row_gap :
    verifiedFrontier - ((3 : ℚ) - (conservativeDelta + conservativeMargin))
      = 5617647814 / 10000000000000 := by
  norm_num [verifiedFrontier, conservativeDelta, conservativeMargin]

/-- The row's ledger shape: every battery cell guards `0`, `1`, or the
conservative floor — the 25 delta-targeted cells at
`conservativeDelta + conservativeMargin`, the 22 geometry cells unchanged. -/
theorem conservative_row_ledger :
    conservativeChecks.all
      (fun check => check.target = 0 ∨ check.target = 1 ∨
        conservativeDelta + conservativeMargin ≤ check.target) = true := by
  decide +kernel

/-- The conservative row, packaged: the kernel-checked battery guards its
targets, and the row's exponent is strictly below the verified frontier with
the notch of `conservative_row_gap`. -/
theorem conservative_row :
    (∀ check ∈ conservativeChecks,
        check.target = 0 ∨ check.target = 1 ∨
          conservativeDelta + conservativeMargin ≤ check.target) ∧
    (3 : ℚ) - (conservativeDelta + conservativeMargin) < verifiedFrontier := by
  refine ⟨fun check hmem => ?_, conservative_row_below_frontier⟩
  have hall := List.all_eq_true.mp conservative_row_ledger
  exact of_decide_eq_true (hall check hmem)

#print axioms verifiedFrontier
#print axioms conservative_exponent_eq
#print axioms conservative_row_below_frontier
#print axioms conservative_row_gap
#print axioms conservative_row_ledger
#print axioms conservative_row

end ThinMatrix.LowFFTCost
