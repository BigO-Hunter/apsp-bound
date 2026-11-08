/-
Copyright (c) 2026. APSP port campaign: L3(d) conservative instantiation.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the construction and the affine certificate
  (`AlignedCertificate.lean`, ported byte-identically) whose checks this
  module re-runs at the conservative delta.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler.
- Joshua Wharton (QFEX) — the rational retune procedure this module mirrors
  at the conservative point instead of the final squeeze.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L3(d): the conservative instantiation of the ledger

The construction's own witness constants are kept; the delta target is
lowered from 705208/10^8 to 1/200 with the full 1/1000000 margin demanded
(0.005001 total). The 25 delta-targeted checks are RETARGETED to
`conservativeDelta + conservativeMargin` (the conservative floor rides on the
cell targets, mirroring the pin's `delta`-as-target); the 22 geometry checks
(targets 0/1) are unchanged, as in the pin. Every ledger cell clears the
conservative floor because its pinned lower bound exceeds 705208/10^8 >
0.005001 — kernel-verified here at the same witness constants.

WHY NOT A CONSTANT FLOOR ON ALL 47 CELLS: that claim is FALSE — the
geometry cells guard `0 < x` at x = eta = b/R ≈ 4.6e-17 (candidate
exponent) and friends, far below 0.005001. The floor applies to the
delta-targeted cells only; the theorem predicates are the pin's
(`check.target < lower ...`), byte-identical in shape. (A `decide +kernel`
over a battery containing a false cell reports a bogus "reduction got stuck":
the kernel rejects the aux lemma and the diagnose-path whnf cannot re-derive
`isFalse` at default transparency.)

The battery is a FLAT 47-entry literal: no map, no ite, no instance —
cell extraction at indices 41 (residual queries) and 43 (cache encodings) is
definitional (`rfl`), membership via `List.getElem_mem`.

This PROMOTES the ledger: the cache-encoding and residual-query savings of
the final witness point are theorems (enclosure-conditional) at the
conservative delta + margin. No interval constants (T/G/q1) are recomputed.
-/
import Submission.ThreeSumApsp.LowCache.FFT.AlignedCertificate
import Submission.ThreeSumApsp.LowCache.FFT.FFTConservative

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ThinMatrix.LowFFTCost

open ThinMatrix.AlignedCertificate

/-- The certificate's checks with every delta target replaced by the
conservative floor (`conservativeDelta + conservativeMargin`); zero- and
one-target geometry checks unchanged.
Flat literal: 19 regimes + 4 phases of 7. -/
def conservativeChecks : List Check :=
  [⟨"ordinary tail regime", 0, ⟨c-5, 0, 0, 0⟩⟩,
   ⟨"positive switching threshold", 0, ⟨theta, 0, 0, 0⟩⟩,
   ⟨"unweighted cache cutoff increasing", 0, ⟨1/2-theta, 0, 0, 0⟩⟩,
   ⟨"stored cutoff increasing", 0, ⟨4/5-theta, 0, 0, 0⟩⟩,
   ⟨"ordinary private-cap tail geometric", 0, ⟨1-4/(c-1), 0, 0, 0⟩⟩,
   ⟨"box private-cap tail geometric", 0, ⟨1-4*(1-theta)/(c-1+theta), 0, 0, 0⟩⟩,
   ⟨"positive box gain", 0, ⟨0, 0, 1, 0⟩⟩,
   ⟨"box gain below one", 0, ⟨1, 0, -1, 0⟩⟩,
   ⟨"positive residual query exponent", 0, ⟨0, 0, 0, 1⟩⟩,
   ⟨"positive stored query exponent", 0, ⟨2*theta, 0, 0, 1⟩⟩,
   ⟨"positive source encoder slope", 0, ⟨1/2, 1, 0, 1⟩⟩,
   ⟨"positive box encoder slope", 0, ⟨1/2, 1, -1, 0⟩⟩,
   ⟨"positive original geometry slope", 0, ⟨-1/2, 1, 0, 0⟩⟩,
   ⟨"positive frozen-factor count", 0, ⟨(S : Rat), 0, 0, 0⟩⟩,
   ⟨"at least two cyclic factors", 1, ⟨((R-S : Nat) : Rat), 0, 0, 0⟩⟩,
   ⟨"positive final ring exponent", 0, ⟨v, 0, 0, 0⟩⟩,
   ⟨"positive candidate exponent", 0, ⟨eta, 0, 0, 0⟩⟩,
   ⟨"middle blocks fit", 0, ⟨1-b, 0, 0, 0⟩⟩,
   ⟨"incidence bookkeeping after enumeration", conservativeDelta + conservativeMargin, ⟨b-eta, 0, 0, 0⟩⟩,
   ⟨"phase I initial: boxes", conservativeDelta + conservativeMargin, ⟨b-0-eta, 0, b+0, 0⟩⟩,
   ⟨"phase I initial: residual queries", conservativeDelta + conservativeMargin, ⟨b-eta, 0, 0, -(b+0)⟩⟩,
   ⟨"phase I initial: stored queries", conservativeDelta + conservativeMargin,
     ⟨b-eta-(b+0)*(2*theta), 0, 0, -(b+0)⟩⟩,
   ⟨"phase I initial: cache encodings", conservativeDelta + conservativeMargin,
     ⟨1+b-0/2-eta, -(b+0), 0, -(b+0)⟩⟩,
   ⟨"phase I initial: ordinary box encodings", conservativeDelta + conservativeMargin,
     ⟨1+b-0/2-eta, -(b+0), (b+0), 0⟩⟩,
   ⟨"phase I initial: matrix formation", conservativeDelta + conservativeMargin, ⟨1-3*0/2-eta, 0, 0, 0⟩⟩,
   ⟨"phase I initial: original tile geometry", 0, ⟨1+0/2, -(b+0), 0, 0⟩⟩,
   ⟨"phase I freeze: boxes", conservativeDelta + conservativeMargin, ⟨b-u-eta, 0, b+u, 0⟩⟩,
   ⟨"phase I freeze: residual queries", conservativeDelta + conservativeMargin, ⟨b-eta, 0, 0, -(b+u)⟩⟩,
   ⟨"phase I freeze: stored queries", conservativeDelta + conservativeMargin,
     ⟨b-eta-(b+u)*(2*theta), 0, 0, -(b+u)⟩⟩,
   ⟨"phase I freeze: cache encodings", conservativeDelta + conservativeMargin,
     ⟨1+b-u/2-eta, -(b+u), 0, -(b+u)⟩⟩,
   ⟨"phase I freeze: ordinary box encodings", conservativeDelta + conservativeMargin,
     ⟨1+b-u/2-eta, -(b+u), (b+u), 0⟩⟩,
   ⟨"phase I freeze: matrix formation", conservativeDelta + conservativeMargin, ⟨1-3*u/2-eta, 0, 0, 0⟩⟩,
   ⟨"phase I freeze: original tile geometry", 0, ⟨1+u/2, -(b+u), 0, 0⟩⟩,
   ⟨"phase II start: boxes", conservativeDelta + conservativeMargin, ⟨b - u - eta, 0, e, 0⟩⟩,
   ⟨"phase II start: residual queries", conservativeDelta + conservativeMargin, ⟨b - eta, 0, 0, -e⟩⟩,
   ⟨"phase II start: stored queries", conservativeDelta + conservativeMargin,
     ⟨b - eta - e * (2 * theta), 0, 0, -e⟩⟩,
   ⟨"phase II start: cache encodings", conservativeDelta + conservativeMargin,
     ⟨1 + b - u / 2 - eta, -e, 0, -e⟩⟩,
   ⟨"phase II start: ordinary box encodings", conservativeDelta + conservativeMargin,
     ⟨1 + b - u / 2 - eta, -e, e, 0⟩⟩,
   ⟨"phase II start: matrix formation", conservativeDelta + conservativeMargin,
     ⟨1 - 3 * u / 2 - eta, 0, 0, 0⟩⟩,
   ⟨"phase II start: original tile geometry", 0, ⟨1 + u / 2, -e, 0, 0⟩⟩]
  ++ [⟨"phase II final: boxes", conservativeDelta + conservativeMargin, ⟨b - u - v - eta, 0, e, 0⟩⟩,
     ⟨"phase II final: residual queries", conservativeDelta + conservativeMargin, ⟨b - v - eta, 0, 0, -e⟩⟩,
     ⟨"phase II final: stored queries", conservativeDelta + conservativeMargin,
       ⟨b - eta - e * (2 * theta), 0, 0, -e⟩⟩,
     ⟨"phase II final: cache encodings", conservativeDelta + conservativeMargin,
       ⟨1 + b - u / 2 - v - eta, -e, 0, -e⟩⟩,
     ⟨"phase II final: ordinary box encodings", conservativeDelta + conservativeMargin,
       ⟨1 + b - u / 2 - v - eta, -e, e, 0⟩⟩,
     ⟨"phase II final: matrix formation", conservativeDelta + conservativeMargin,
       ⟨1 - 3 * u / 2 - v - eta, 0, 0, 0⟩⟩,
     ⟨"phase II final: original tile geometry", 0, ⟨1 + u / 2, -e, 0, 0⟩⟩]

/-- The battery count matches the certificate's 47 checks (flat literal:
definitional). -/
theorem conservativeCheckCount : conservativeChecks.length = 47 := rfl

/-- The residual-query cell, by definitional extraction. -/
theorem conservativeChecks_res_val : conservativeChecks[41] =
    ⟨"phase II final: residual queries", conservativeDelta + conservativeMargin,
      ⟨b - v - eta, 0, 0, -e⟩⟩ :=
  rfl

/-- The cache-encoding cell, by definitional extraction. -/
theorem conservativeChecks_cache_val : conservativeChecks[43] =
    ⟨"phase II final: cache encodings", conservativeDelta + conservativeMargin,
      ⟨1 + b - u / 2 - v - eta, -e, 0, -e⟩⟩ :=
  rfl

/-- Kernel-transferred conservative battery: the cell targets carry the
conservative floor (ledger cells at `conservativeDelta + conservativeMargin`,
geometry cells at 0/1), and every cell's pinned lower bound exceeds its
target — same predicate shape as the pin's `numericalMargins`. -/
theorem conservativeMargins :
    conservativeChecks.all (fun check =>
      decide (check.target < lower check.expression)) = true := by
  decide +kernel

/-- Enclosure-conditional conservative battery (pin's statement shape). -/
theorem allCostsOfEnclosures_conservative (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi)
    (hq : qLo ≤ q1 ∧ q1 ≤ qHi) :
    ∀ check ∈ conservativeChecks,
      check.target < eval check.expression T G q1 := by
  intro check hmember
  have hb : decide (check.target < lower check.expression) = true :=
    (List.all_eq_true.mp conservativeMargins) check hmember
  have hm : check.target < lower check.expression :=
    of_decide_eq_true hb
  have hl := lower_le_eval check.expression T G q1 hT hG hq
  grind

/-- PROMOTED: the final-point cache-encoding saving at delta = 1/200 plus
the 1e-6 margin — enclosure-conditional theorem over the pinned constants
(promotes `ConservativeLedger.cacheSaving`). -/
theorem conservative_cache_saving_theorem (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi) (hq : qLo ≤ q1 ∧ q1 ≤ qHi) :
    conservativeDelta + conservativeMargin <
      eval ⟨1 + b - u / 2 - v - eta, -e, 0, -e⟩ T G q1 := by
  have hmem : conservativeChecks[43] ∈ conservativeChecks :=
    List.getElem_mem (by rw [conservativeCheckCount]; omega)
  have hp := (List.all_eq_true.mp conservativeMargins) _ hmem
  rw [conservativeChecks_cache_val] at hp
  have hm : conservativeDelta + conservativeMargin <
      lower ⟨1 + b - u / 2 - v - eta, -e, 0, -e⟩ := of_decide_eq_true hp
  have hl := lower_le_eval ⟨1 + b - u / 2 - v - eta, -e, 0, -e⟩ T G q1 hT hG hq
  exact lt_of_lt_of_le hm hl

/-- PROMOTED: the final-point residual-query saving (the certificate's
BINDING inequality) at delta = 1/200 plus the 1e-6 margin
(promotes `ConservativeLedger.residualQuery`). -/
theorem conservative_residual_query_theorem (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi) (hq : qLo ≤ q1 ∧ q1 ≤ qHi) :
    conservativeDelta + conservativeMargin <
      eval ⟨b - v - eta, 0, 0, -e⟩ T G q1 := by
  have hmem : conservativeChecks[41] ∈ conservativeChecks :=
    List.getElem_mem (by rw [conservativeCheckCount]; omega)
  have hp := (List.all_eq_true.mp conservativeMargins) _ hmem
  rw [conservativeChecks_res_val] at hp
  have hm : conservativeDelta + conservativeMargin <
      lower ⟨b - v - eta, 0, 0, -e⟩ := of_decide_eq_true hp
  have hl := lower_le_eval ⟨b - v - eta, 0, 0, -e⟩ T G q1 hT hG hq
  exact lt_of_lt_of_le hm hl

#print axioms conservativeCheckCount
#print axioms conservativeMargins
#print axioms allCostsOfEnclosures_conservative
#print axioms conservative_cache_saving_theorem
#print axioms conservative_residual_query_theorem

end ThinMatrix.LowFFTCost
