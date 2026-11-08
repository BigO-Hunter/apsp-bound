/-
Copyright (c) 2026. APSP port campaign: L3(b) conservative-parameter contract.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the construction and the BinaryArrayFFT path whose
  multiplication theorem this file wraps (thin-matrix-results at the pin).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler.
- Joshua Wharton (QFEX) — the compatibility shim and adapted CyclicRing; the
  rational retune whose final-exponent squeeze this file deliberately avoids.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L3(b): the FFT multiplication contract at conservative parameters

The cone's top theorem `BinaryArrayFFT.multiplication_correct_and_cost`
states, for modulus length `q` and coefficient bound `A`:

  correctness: the product's viewed coefficients equal the exact cyclic
  convolution of the viewed inputs; and
  cost: `bitSteps + arrayActions ≤ 147573952589676412928 * (q.log2+3) * q *
        (q.log2 + A.log2 + 102)^10`,

counted over the cone's OWN counters (`bitSteps + arrayActions`).

BOUNDARY (campaign decision, recorded): those counters are bit-cost units —
charged-work style. The translation "bit-cost counter → Light step budget"
is delta D7, assigned to L5. This file does NOT invent that translation: the
wrapper states the resource contract over the cone's own counters, and the
`Solves`/`SolvedIn` Light-step forms are deferred with it.

The conservative-margin arithmetic: the final certificate's slack is
2.24e-14; the conservative parameters (delta ≈ 0.005..0.006) carry a margin
of 1e-6. This file proves the domination `2.24e-14 < 1e-6` and fixes the
conservative constants, so L3's proofs land before that squeeze.
-/
import Submission.ThreeSumApsp.LowCache.FFT.BinaryArrayFFT

namespace ThinMatrix.LowFFTCost

open ThinMatrix.BinaryArrayFFT

/-- The L3 resource contract for one bounded-word cyclic multiplication:
exact convolution correctness plus the cone's own counter bound. The
bit-cost → Light-step translation is delta D7 (L5) and is deliberately
absent here. -/
structure FftMultContract (q A : ℕ) [NeZero q] : Prop where
  correct : ∀ (a b : Array Integer),
    (∀ i : Fin q, (Integer.view (Array.getD a i.val zeroInteger)).natAbs ≤ A) →
    (∀ i : Fin q, (Integer.view (Array.getD b i.val zeroInteger)).natAbs ≤ A) →
    ∀ j : Fin q, Integer.view (Array.getD (multiplication q A a b).value j.val zeroInteger) =
      CyclicRing.convolution (ArrayFFT.asCyclic q (viewIntegers a))
        (ArrayFFT.asCyclic q (viewIntegers b)) j
  counterBound : ∀ (a b : Array Integer),
    (∀ i : Fin q, (Integer.view (Array.getD a i.val zeroInteger)).natAbs ≤ A) →
    (∀ i : Fin q, (Integer.view (Array.getD b i.val zeroInteger)).natAbs ≤ A) →
    (multiplication q A a b).bitSteps + (multiplication q A a b).arrayActions ≤
      147573952589676412928 * (q.log2 + 3) * q * (q.log2 + A.log2 + 102) ^ 10

/-- The cone's top theorem instantiates the contract. -/
theorem fft_mult_contract (q A : ℕ) [NeZero q] (hA : 1 ≤ A) : FftMultContract q A := by
  refine ⟨?_, ?_⟩
  · intro a b ha hb j
    exact (multiplication_correct_and_cost q A hA a b ha hb).1 j
  · intro a b ha hb
    exact (multiplication_correct_and_cost q A hA a b ha hb).2

/-- The conservative parameter point: delta = 1/200 (0.005), within the
campaign's conservative band 0.005..0.006. -/
def conservativeDelta : ℚ := 1 / 200

/-- The conservative arithmetic margin: one part in a million. -/
def conservativeMargin : ℚ := 1 / 1000000

/-- The final-exponent squeeze this layer deliberately avoids: the binding
inequality's slack at 2.9929479187094. -/
def finalSqueeze : ℚ := 224 / 100000000000000

/-- The conservative margin dominates the final squeeze by six orders of
magnitude — this is why L3 lands as a proof before the retune. -/
theorem conservative_margin_dominates : finalSqueeze < conservativeMargin := by
  norm_num [finalSqueeze, conservativeMargin]

/-- The conservative delta plus its margin stays inside the campaign's
conservative band (delta + margin ≤ 0.006). -/
theorem conservative_band : conservativeDelta + conservativeMargin ≤ 3 / 500 := by
  norm_num [conservativeDelta, conservativeMargin]

#print axioms fft_mult_contract
#print axioms conservative_margin_dominates
#print axioms conservative_band

end ThinMatrix.LowFFTCost
