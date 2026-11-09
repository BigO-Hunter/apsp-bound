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

## Ported (M3c follow-up): the ledger machinery itself

| Statement | File | Provenance |
|---|---|---|
| The affine ledger: `Check`, `eval`, `scalarPhase`/`scalarCosts`, `cyclicPhase`/`cyclicCosts` — including the cache-encoding form `1+b-u/2-z-e*E-eta` and the residual-query form `b-z-e*q1-eta` — with `scalarPhaseEval`, `cyclicPhaseEval`, `witnessIdentities` and the constant definitions (c, theta, b, delta=705208/10^8, R, S, eta=b/R, u=S*eta, e=b+u, T/G/q1 interval bounds) | AlignedCertificate.lean | PORTED from the pin (byte-identical, zero drift; imports only Std + Init.Grind.Ordered.Rat — no 129-module chain, no real-log enclosures). Axioms: [propext, Classical.choice, Quot.sound]. The CONSERVATIVE instantiation of these checks (delta = 1/200 + 1e-6 margin) remains the retune-scope item — the ported constants are the FINAL point. |

## Ported (M3d): the conservative instantiation kernel-checked

| Statement | File | Provenance |
|---|---|---|
| `conservativeChecks` — the pinned 47-check battery with the 25 delta-targeted cells retargeted to `conservativeDelta + conservativeMargin` (= 1/200 + 1/1000000, 0.005001 total); the 22 geometry cells unchanged (targets 0/1) | FFTConservativeInstance.lean | retargeting of the pinned `checks` (AlignedCertificate); expressions byte-identical to the pin. Battery count `conservativeCheckCount` = 47 (rfl). |
| `conservativeMargins : conservativeChecks.all (fun check => decide (check.target < lower check.expression)) = true` | FFTConservativeInstance.lean | `decide +kernel` at the pin's exact predicate shape. Ledger cells clear the conservative floor because their pinned lower bounds exceed 705208/10^8 > 0.005001 at the SAME witness constants. Axioms: [propext, Classical.choice, Quot.sound]. |
| `allCostsOfEnclosures_conservative` (pin's statement shape, enclosure-conditional) | FFTConservativeInstance.lean | from `conservativeMargins` + `lower_le_eval` |
| `conservative_cache_saving_theorem`, `conservative_residual_query_theorem` — the two LEDGER inequalities at delta = 1/200 + 1e-6, enclosure-conditional over the pinned T/G/q1 boxes (promote `ConservativeLedger.cacheSaving` / `.residualQuery`) | FFTConservativeInstance.lean | the binding inequality ("phase II final: residual queries") is now a THEOREM at the conservative point. Non-vacuity verified: corrected cells 33/40 (boxes, gCoeff = e) and 41/43 evaluate true via `decide +kernel` on the projected battery. |

FORENSICS RECORD (the elaboration-environment discrepancy, resolved): the
prior session's "maximum recursion depth" + "Unknown identifier kernel" was
NOT an import-scope/option problem. Three independent defects: (1)
`decide +kernel` is TACTIC syntax — in term position `+kernel` parses as
`+ kernel` (identifier error); (2) the pin's `maxRecDepth 100000` /
`maxHeartbeats 8000000` are file-scoped and do not transfer through imports
(the WIP had 8000 / default); (3) TWO battery transcription drifts (phase II
boxes cells lost their `e` gCoeff; the residual-query extraction conflated
the unexpanded and affine forms) — and, decisively, the original statement
applied the 0.005001 floor to ALL 47 cells, which is FALSE at the
candidate-exponent cell (0 < eta with eta = b/R ≈ 4.6e-17). `decide +kernel`
over a false cell reports a bogus "reduction got stuck" (kernel rejects the
aux lemma; the diagnose-path whnf cannot re-derive `isFalse` at default
transparency). Fix: floor rides on the CELL TARGETS (pin shape), predicates
byte-identical to the pin's.

## Named hypothesis (conditional-by-construction, NOT ported)

| Statement | File | Status + provenance |
|---|---|---|
| `ConservativeLedger` — u, e, E, eta with `1 + u/2 - e*E >= delta + margin` (cache saving) and `u - e*E - eta >= delta + margin` (residual queries, the BINDING inequality) | FFTConservative.lean | **PROMOTED AT THE CONSERVATIVE POINT (M3d)**: satisfiability of the ledger at delta = 1/200 + 1e-6 is now kernel-checked via `conservativeMargins` + the two promotion theorems in FFTConservativeInstance.lean. What remains named-hypothesis is the FINAL-point squeeze (gap 2.24e-14 at delta = 0.0070520812906, binding condition "phase II final: residual queries") — the conservative instance is deliberately NOT the final squeeze. |
| Corollaries `conservative_cache_saving`, `conservative_residual_query`, `squeeze_below_margin` | FFTConservative.lean | restatements of the hypothesis + prior arithmetic |

## Boundary (standing)

Bit-cost -> Light-step translation is D7, assigned to L5. The FFT contract is
stated over the cone's own counters (`bitSteps + arrayActions`).

## Ported (M3e): the conservative row takes the notch

| Statement | File | Provenance |
|---|---|---|
| `verifiedFrontier` = 29955607647814/10^13 (2.9955607647814) | FFTConservativeRow.lean | the LV frontier row (Li Xuanji construction; Bojnal's verified frontier), stated as the comparison constant |
| `conservative_exponent_eq` : 3 − (1/200 + 1/1000000) = 2994999/10^6 | FFTConservativeRow.lean | norm_num; the row's exponent identity |
| `conservative_row_below_frontier` : 3 − (δ_c + margin) < verifiedFrontier | FFTConservativeRow.lean | norm_num — THE NOTCH: 2.994999 < 2.9955607647814 |
| `conservative_row_gap` : frontier − row exponent = 5617647814/10^13 | FFTConservativeRow.lean | norm_num; notch size ≈ 5.62×10⁻⁴ |
| `conservative_row_ledger` : all 47 battery cells guard 0, 1, or the conservative floor | FFTConservativeRow.lean | decide +kernel on the flat literal |
| `conservative_row` (packaged: battery target-shape ∧ below-frontier) | FFTConservativeRow.lean | from conservative_row_ledger + conservative_row_below_frontier |

Receipts (exit-code in the same chain as each build): M3e build
`lake build Submission.ThreeSumApsp.LowCache.FFT.FFTConservativeRow` —
exit 0 (`/private/tmp/apsp_m3e_m2.exit`; first attempt failed on
`List.all_eq_true` decide-coercion, fixed with `of_decide_eq_true`).
Axioms: all six declarations `[propext, Classical.choice, Quot.sound]` —
standard-3; no sorry, no native_decide. The two binding promotions remain
enclosure-conditional (M3d) — the unconditional real-log enclosures at the
conservative point are the successor item (LogBounds regeneration), not
needed for the row's notch claim.

## Ported (M3f): the real-log interpretation of the pinned boxes

| Statement | File | Provenance |
|---|---|---|
| `cR`/`thetaR` (the pinned constants as reals), `entropyR`, `realT`/`realG`/`realq1` (binary entropy and the tile geometry via Mathlib's actual `Real.log`) | ConservativeEnclosures.lean | definitions at the pinned witness constants; discharges the AlignedCertificate note "the real-log/entropy interpretation of these compact boxes is NOT proved here" |
| `atanhLogBounds` (generic 40-term positive atanh-series enclosure, from `Real.sum_range_le_log_div` / `Real.log_div_le_sum_range_add`) + seven concrete log bounds at the pinned arguments (log2, log(16p), log(2(1-p)) for p = 1/c, (1-theta)/c, theta) | ConservativeEnclosures.lean | Wharton's `ApspBound.LogBounds` arrangement mirrored at the pinned constants; range-reduction identity from the upstream ThinMatrix.RealCertificate module; Python endpoints NOT in the trust base |
| `entropyScaledR` + `entropyC`/`entropyD`/`entropyT` (10^-24-scaled entropy enclosures) | ConservativeEnclosures.lean | entropy range reduction + linarith over the log bounds |
| `realT_enclosed`/`realG_enclosed`/`realq1_enclosed` (10^-21-scaled), `conservative_enclosures` : the pinned boxes `tLo/tHi`, `gLo/gHi`, `qLo/qHi` enclose `realT`, `realG`, `realq1` | ConservativeEnclosures.lean | division monotonicity (`lt_div_iff₀`/`div_lt_iff₀`) assembly, upstream `Certificate.lean` pattern |
| `conservative_cache_saving_final`, `conservative_residual_query_final` — the two binding ledger inequalities at delta = 1/200 + 1/1000000, UNCONDITIONAL (no hypotheses) | ConservativeEnclosures.lean | M3d's promoted theorems at the box point `(tLo, gHi, qHi)`; the boxes' honesty is now `conservative_enclosures` |

Receipts (exit-code in the same chain as the build): M3f final build
`lake build Submission.ThreeSumApsp.LowCache.FFT.ConservativeEnclosures` —
exit 0 (`/private/tmp/apsp_m3f_m7.exit`; earlier detached attempts of the
corrected file were SIGTERM'd twice — exit 143 at ~20:41 and ~21:09 —
timestamps recorded for the kill-ledger gap; the successful foreground run
took ~2 min). Axioms: all ten declarations
`[propext, Classical.choice, Quot.sound]` — standard-3; no sorry, no
native_decide. Box honesty verified independently at 70-digit Decimal
precision before the Lean literals were generated (T, G, q1 all inside the
pinned boxes; float64 had misjudged G at the 15th digit).
