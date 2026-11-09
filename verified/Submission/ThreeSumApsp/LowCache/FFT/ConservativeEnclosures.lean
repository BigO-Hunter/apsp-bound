/-
Copyright (c) 2026. APSP port campaign: L3(f) the real-log interpretation.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the construction and the pinned witness constants and
  compact boxes (`AlignedCertificate.lean`, ported byte-identically); the
  range-reduction identity and proof arrangement of the log bounds follow the
  open upstream ThinMatrix.RealCertificate module.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler.
- Joshua Wharton (QFEX) — the 40-term positive atanh-series enclosure
  arrangement (`ApspBound.LogBounds`) this module mirrors at the pinned
  constants; the retune procedure whose squeeze the conservative row avoids.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L3(f): the pinned boxes enclose the real quantities

`AlignedCertificate.lean` carries the pinned T/G/q1 boxes with the note "the
real-log/entropy interpretation of these compact boxes is NOT proved here".
This module proves it: binary entropy and the tile geometry T, G, q1 — real
quantities built from Mathlib's actual `Real.log` at the pinned witness
constants — lie inside `tLo/tHi`, `gLo/gHi`, `qLo/qHi`.

Machinery (mirrors `ApspBound.LogBounds`/`Certificate.lean`): the generic
positive atanh-series enclosure (`atanhLogBounds`, proved in
Mathlib.Analysis.SpecialFunctions.Log.Deriv), seven concrete 40-term log
bounds at the pinned arguments, the entropy range-reduction identity, and the
division-monotonicity assembly into T, G, q1. The Python side only selected
rational endpoints and is not in the proof's trust base.

This promotes M3d's two enclosure-conditional theorems
(`conservative_cache_saving_theorem`, `conservative_residual_query_theorem`)
to unconditional: the ledger inequalities hold at the pinned boxes, and the
pinned boxes now provably enclose the real quantities. D7 boundary stands
(no bit-cost → Light-step translation is claimed here).
-/
import Submission.ThreeSumApsp.LowCache.FFT.AlignedCertificate
import Submission.ThreeSumApsp.LowCache.FFT.FFTConservativeInstance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace ThinMatrix.LowFFTCost

open scoped BigOperators
open ThinMatrix.AlignedCertificate

noncomputable section

/-! ## The real quantities at the pinned constants -/

/-- The pinned candidate-count constant, as a real. -/
noncomputable def cR : ℝ := 1066550171 / 100000000

/-- The pinned theta constant, as a real. -/
noncomputable def thetaR : ℝ := 652978214 / 10000000000

/-- Binary entropy at the real parameters. -/
noncomputable def entropyR (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

/-- The real tile geometry: `T = c - 1 + C_K` with `C_K = c·H(1/c)/log 4`. -/
noncomputable def realT : ℝ := cR - 1 + cR * entropyR (1 / cR) / (2 * Real.log 2)

/-- The real tile geometry: the shared-band gain. -/
noncomputable def realG : ℝ :=
  (cR * entropyR (1 / cR) - cR * entropyR ((1 - thetaR) / cR)
    - thetaR * (2 * Real.log 2)) / Real.log 2

/-- The real tile geometry: the phase-I entropy cost. -/
noncomputable def realq1 : ℝ := entropyR thetaR / Real.log 2

/-! ## The generic atanh-series enclosure (40 terms) -/

/-- The applications below use 40 terms of this proved positive atanh-series
enclosure. The omitted nonnegative tail is bounded by a rational geometric
majorant. -/
theorem atanhLogBounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
        ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor <;> linarith

theorem logTwoPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-! ## The seven concrete log bounds at the pinned arguments -/

theorem logTwoFine :
    (693147180559945309417232121458 / 10^30 : ℝ) < Real.log (2 : ℝ) ∧
    Real.log (2 : ℝ) < (693147180559945309417232121459 / 10^30 : ℝ) := by
  have h := atanhLogBounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logC16 :
    (405574328760022632473546439295 / 10^30 : ℝ) < Real.log (1600000000 / 1066550171 : ℝ) ∧
    Real.log (1600000000 / 1066550171 : ℝ) < (405574328760022632473546439296 / 10^30 : ℝ) := by
  have h := atanhLogBounds (533449829 / 2666550171 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logCComp2 :
    (594695808377684387113928766934 / 10^30 : ℝ) < Real.log (1933100342 / 1066550171 : ℝ) ∧
    Real.log (1933100342 / 1066550171 : ℝ) < (594695808377684387113928766935 / 10^30 : ℝ) := by
  have h := atanhLogBounds (866550171 / 2999650513 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logD16 :
    (338047002765033636655113223481 / 10^30 : ℝ) < Real.log (37388087144 / 26663754275 : ℝ) ∧
    Real.log (37388087144 / 26663754275 : ℝ) < (338047002765033636655113223482 / 10^30 : ℝ) := by
  have h := atanhLogBounds (10724332869 / 64051841419 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logDComp2 :
    (601428851680190950020686794905 / 10^30 : ℝ) < Real.log (48653997657 / 26663754275 : ℝ) ∧
    Real.log (48653997657 / 26663754275 : ℝ) < (601428851680190950020686794906 / 10^30 : ℝ) := by
  have h := atanhLogBounds (10995121691 / 37658875966 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logT16 :
    (43792116043198641334733862493 / 10^30 : ℝ) < Real.log (652978214 / 625000000 : ℝ) ∧
    Real.log (652978214 / 625000000 : ℝ) < (43792116043198641334733862494 / 10^30 : ℝ) := by
  have h := atanhLogBounds (13989107 / 638989107 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logTComp2 :
    (625619854564956313598798905643 / 10^30 : ℝ) < Real.log (4673510893 / 2500000000 : ℝ) ∧
    Real.log (4673510893 / 2500000000 : ℝ) < (625619854564956313598798905644 / 10^30 : ℝ) := by
  have h := atanhLogBounds (2173510893 / 7173510893 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-! ## The entropy range reduction and the three entropy enclosures -/

/-- Range-reduction identity used to place both entropy logarithms in [1,2]
for the pinned parameters. -/
theorem entropyScaledR (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    entropyR p = (1 + 3 * p) * Real.log 2 - p * Real.log (16 * p)
      - (1 - p) * Real.log (2 * (1 - p)) := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  have hmul := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hp)
  have hcomp := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt (sub_pos.mpr hp1))
  have ha : Real.log p = Real.log (16 * p) - 4 * Real.log 2 := by
    rw [h16] at hmul
    linarith
  have hb : Real.log (1 - p) = Real.log (2 * (1 - p)) - Real.log 2 := by
    linarith
  rw [entropyR, ha, hb]
  ring

theorem entropyC :
    (311152385503602153694102 / 10^24 : ℝ) < entropyR (1 / cR) ∧
    entropyR (1 / cR) < (311152385503602153694103 / 10^24 : ℝ) := by
  have hs := entropyScaledR (1 / cR) (by norm_num [cR]) (by norm_num [cR])
  have h0 := logTwoFine
  have h1 := logC16
  have h2 := logCComp2
  norm_num [cR] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyD :
    (297038452283886178076075 / 10^24 : ℝ) < entropyR ((1 - thetaR) / cR) ∧
    entropyR ((1 - thetaR) / cR) < (297038452283886178076076 / 10^24 : ℝ) := by
  have hs := entropyScaledR ((1 - thetaR) / cR) (by norm_num [cR, thetaR])
    (by norm_num [cR, thetaR])
  have h0 := logTwoFine
  have h1 := logD16
  have h2 := logDComp2
  norm_num [cR, thetaR] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyT :
    (241302412150899210740294 / 10^24 : ℝ) < entropyR thetaR ∧
    entropyR thetaR < (241302412150899210740295 / 10^24 : ℝ) := by
  have hs := entropyScaledR thetaR (by norm_num [thetaR]) (by norm_num [thetaR])
  have h0 := logTwoFine
  have h1 := logT16
  have h2 := logTComp2
  norm_num [thetaR] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-! ## The tile-geometry enclosures -/

theorem realT_enclosed :
    (12059362922115430713535 / 10^21 : ℝ) < realT ∧
    realT < (12059362922115430713536 / 10^21 : ℝ) := by
  have h0 := logTwoFine
  have hc := entropyC
  have hp : 0 < 2 * Real.log 2 := mul_pos (by norm_num) logTwoPositive
  have hlo : ((12059362922115430713535 / 10^21 : ℝ) - cR + 1) * (2 * Real.log 2)
      < cR * entropyR (1 / cR) := by
    norm_num [cR] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hhi : cR * entropyR (1 / cR)
      < ((12059362922115430713536 / 10^21 : ℝ) - cR + 1) * (2 * Real.log 2) := by
    norm_num [cR] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hl := (lt_div_iff₀ hp).2 hlo
  have hh := (div_lt_iff₀ hp).2 hhi
  dsimp [realT]
  constructor <;> linarith

theorem realG_enclosed :
    (86576385178389936269 / 10^21 : ℝ) < realG ∧
    realG < (86576385178389936270 / 10^21 : ℝ) := by
  have h0 := logTwoFine
  have hc := entropyC
  have hd := entropyD
  dsimp [realG]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    norm_num [cR, thetaR] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    norm_num [cR, thetaR] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]

theorem realq1_enclosed :
    (348125793364647037384 / 10^21 : ℝ) < realq1 ∧
    realq1 < (348125793364647037385 / 10^21 : ℝ) := by
  have h0 := logTwoFine
  have ht := entropyT
  dsimp [realq1]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    linarith [h0.1, h0.2, ht.1, ht.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    linarith [h0.1, h0.2, ht.1, ht.2]

/-! ## The bridge to the pinned boxes and the unconditional promotions -/

/-- THE REAL-LOG INTERPRETATION: the pinned boxes enclose the real
quantities. This discharges the enclosure hypotheses of M3d's two promoted
theorems. -/
theorem conservative_enclosures :
    (tLo : ℝ) ≤ realT ∧ realT ≤ (tHi : ℝ) ∧
    (gLo : ℝ) ≤ realG ∧ realG ≤ (gHi : ℝ) ∧
    (qLo : ℝ) ≤ realq1 ∧ realq1 ≤ (qHi : ℝ) := by
  have ht := realT_enclosed
  have hg := realG_enclosed
  have hq := realq1_enclosed
  norm_num [tLo, tHi, gLo, gHi, qLo, qHi] at ht hg hq ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- UNCONDITIONAL: the final-point cache-encoding saving at the conservative
delta + margin — the real quantities lie in the pinned boxes
(`conservative_enclosures`), and M3d's battery clears the floor there. -/
theorem conservative_cache_saving_final :
    conservativeDelta + conservativeMargin <
      eval ⟨1 + b - u / 2 - v - eta, -e, 0, -e⟩ tLo gHi qHi := by
  obtain ⟨h1, h2, h3⟩ := boxesOrdered
  exact conservative_cache_saving_theorem tLo gHi qHi ⟨le_refl _, h1⟩ ⟨h2, le_refl _⟩
    ⟨h3, le_refl _⟩

/-- UNCONDITIONAL: the binding residual-query saving at the conservative
delta + margin. -/
theorem conservative_residual_query_final :
    conservativeDelta + conservativeMargin < eval ⟨b - v - eta, 0, 0, -e⟩ tLo gHi qHi := by
  obtain ⟨h1, h2, h3⟩ := boxesOrdered
  exact conservative_residual_query_theorem tLo gHi qHi ⟨le_refl _, h1⟩ ⟨h2, le_refl _⟩
    ⟨h3, le_refl _⟩

#print axioms atanhLogBounds
#print axioms entropyC
#print axioms entropyD
#print axioms entropyT
#print axioms realT_enclosed
#print axioms realG_enclosed
#print axioms realq1_enclosed
#print axioms conservative_enclosures
#print axioms conservative_cache_saving_final
#print axioms conservative_residual_query_final

end
end ThinMatrix.LowFFTCost
