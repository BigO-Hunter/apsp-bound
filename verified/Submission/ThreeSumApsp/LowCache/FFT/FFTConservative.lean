/-
Copyright (c) 2026. APSP port campaign: L3(c) conservative-parameter instantiation.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the construction; the ledger quantities (u, e, eta,
  C_K, T) and the binding condition "phase II final: residual queries" come
  from the numerical certificate of the pinned construction
  (certificate.json / parameters.json, source_commit 8a21eaae...).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler.
- Joshua Wharton (QFEX) — the rational retune (47-inequality certificate at
  2.9929479187094, gap 2.24e-14) whose squeeze this file avoids by
  instantiating at the CONSERVATIVE delta instead.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L3(c): the conservative instantiation

Two pieces, per the campaign design:

1. A NON-VACUOUS concrete instantiation of the FFT multiplication contract:
   `fft_mult_contract_concrete : FftMultContract 2 1` quantifies over actual
   arrays fed to the actual cone program `multiplication 2 1` (q = 2: the
   smallest nontrivial cyclic length; A = 1: the smallest nontrivial
   coefficient bound). The production (q, A) pair is a retune output and is
   NOT fixed here.

2. The cache-saving ledger inequality at the conservative delta, as a NAMED
   HYPOTHESIS (conditional-by-construction): `ConservativeLedger` carries the
   ledger quantities u, e, E, eta with the two binding inequalities at
   delta = 1/200 plus the 1e-6 margin. This matches the campaign's
   conditional pattern (the final certificate itself is conditional on the
   cited written algorithmic proof). STATUS: named-hypothesis, NOT ported —
   the ledger inequality is numeric-computation evidence in the certificate
   chain (certificate.json: smallest_runtime_gap 2.24e-14, binding_condition
   "phase II final: residual queries"), not a lemma-shaped statement in the
   FFT cone. Porting it is the named obstruction for M3c's successor.

BOUNDARY (unchanged): bit-cost -> Light-step translation is D7 (L5).
-/
import Submission.ThreeSumApsp.LowCache.FFT.FFTCostContract

namespace ThinMatrix.LowFFTCost

open ThinMatrix.BinaryArrayFFT

/-- NON-VACUOUS concrete instantiation: q = 2, A = 1 are concrete numerals,
so `multiplication 2 1` below is the actual cone program, not a schema
variable. -/
theorem fft_mult_contract_concrete : FftMultContract 2 1 :=
  fft_mult_contract 2 1 (by norm_num)

/-- The conservative ledger quantities and the two binding inequalities at
delta = 1/200 with the 1e-6 margin. NAMED HYPOTHESIS (conditional-by-
construction): satisfiability evidence is the numeric certificate of the
pinned construction (certificate.json: gap 2.24e-14 at delta = 0.007052...,
binding condition "phase II final: residual queries"); the conservative
instance is the retune target, not a derived instance. -/
structure ConservativeLedger where
  u : ℚ
  e : ℚ
  bigE : ℚ
  eta : ℚ
  /-- Cache saving: `1 + u/2 - e*E >= delta + margin` at the conservative
  delta = 1/200 and margin = 1/1000000. -/
  cacheSaving : 1 + u / 2 - e * bigE ≥ conservativeDelta + conservativeMargin
  /-- Residual-query saving (the binding inequality of the final
  certificate): `u - e*E - eta >= delta + margin`. -/
  residualQuery : u - e * bigE - eta ≥ conservativeDelta + conservativeMargin

/-- The conservative ledger delivers the cache saving with the full margin. -/
theorem conservative_cache_saving (L : ConservativeLedger) :
    1 + L.u / 2 - L.e * L.bigE ≥ 1 / 200 + 1 / 1000000 :=
  L.cacheSaving

/-- The conservative ledger delivers the binding residual-query saving with
the full margin. -/
theorem conservative_residual_query (L : ConservativeLedger) :
    L.u - L.e * L.bigE - L.eta ≥ 1 / 200 + 1 / 1000000 :=
  L.residualQuery

/-- The final certificate's squeeze is bounded away from the conservative
margin (restated here so this module carries its own receipt). -/
theorem squeeze_below_margin : finalSqueeze < conservativeMargin :=
  conservative_margin_dominates

#print axioms fft_mult_contract_concrete
#print axioms conservative_cache_saving
#print axioms conservative_residual_query
#print axioms squeeze_below_margin

end ThinMatrix.LowFFTCost
