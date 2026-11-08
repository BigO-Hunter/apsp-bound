# STMTS.md — L3(c) conservative-parameter instantiation: statement inventory

Status per statement (ported Lean content vs named hypothesis), with provenance.
Campaign branch: apsp-l1 @ darkhipo/apsp-bound. Lean 4.33.1, Mathlib 0df444a3.

## Ported (kernel-checked Lean content)

| Statement | File | Provenance |
|---|---|---|
| `FftMultContract q A` (correctness + `bitSteps+arrayActions <= 147573952589676412928*(q.log2+3)*q*(q.log2+A.log2+102)^10`) | FFTCostContract.lean | wraps `BinaryArrayFFT.multiplication_correct_and_cost` (shresh pin 225c37476e) |
| `fft_mult_contract` | FFTCostContract.lean | instantiation of the cone's top theorem |
| `fft_mult_contract_concrete : FftMultContract 2 1` | FFTConservative.lean | NON-VACUOUS concrete instantiation (q=2, A=1 concrete numerals; real cone program). Production (q,A) is a retune output, deliberately not fixed. |
| `conservative_margin_dominates` (2.24e-14 < 1e-6), `conservative_band` (delta+margin <= 0.006) | FFTCostContract.lean | arithmetic |

## Named hypothesis (conditional-by-construction, NOT ported)

| Statement | File | Status + provenance |
|---|---|---|
| `ConservativeLedger` — u, e, E, eta with `1 + u/2 - e*E >= delta + margin` (cache saving) and `u - e*E - eta >= delta + margin` (residual queries, the BINDING inequality) | FFTConservative.lean | **Named hypothesis.** The ledger inequality is numeric-computation evidence in the certificate chain (apsp-claimed/certificate.json: smallest_runtime_gap = 2.24e-14 at delta = 0.0070520812906, binding_condition = "phase II final: residual queries"; derived quantities u = 0.035408..., e = 0.081455..., eta interval ~4.6e-17), not a lemma-shaped statement in the FFT cone. Porting it (from shresh's analysis modules / certificate chain) is the named obstruction for the next milestone. The conservative instance (delta = 1/200 + margin 1e-6) is the retune target; it is not derived from the final certificate. |
| Corollaries `conservative_cache_saving`, `conservative_residual_query`, `squeeze_below_margin` | FFTConservative.lean | restatements of the hypothesis + prior arithmetic |

## Boundary (standing)

Bit-cost -> Light-step translation is D7, assigned to L5. The FFT contract is
stated over the cone's own counters (`bitSteps + arrayActions`).
