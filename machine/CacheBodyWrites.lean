import MinPlusCaller
import CallerWrites
import CallerFill1
import BinaryArrayFFT

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 1 — the cache body's
Light statements (the write-side slice) and the L2/L3 cone's wire.

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

# Fill 1's cache-body statements + the L2/L3 cone's wire

The L2/L3 cone's BinaryArrayFFT module is wired into the workspace's
build closure (the copied-file pattern, byte-identical to the board-side
`../lean/BinaryArrayFFT.lean`). The cone's value contract
(`ThinMatrix.BinaryArrayFFT.fft_view`: the FFT's output view = the
cyclic convolution of the input views) and its cost bounds
(`tabulate_bitSteps_bound` / `array_fold_cost_bound` — the `CallerHdom`
bricks) are now importable at the caller's namespace.

THE COUNT-DERIVATION LEMMA (the next slice): the per-(p, i) incidence
counts ride the exponential encoding (the min-plus-as-multiplication
identity — the upstream construction's own conversion,
`DenseOracleCorrect`-conditioned) composed with the FFT's round-trip
(`fft_view`). D7's boundary stands: the encoding identity is a premise,
never claimed as proved.

The cache-body statements (unchanged from the first landing):
- `cacheWritesEntry` / `cacheWritesRow` — the per-(p, i) count-write
  statements at the cache's own register map: the store into the cache's
  row-base + entry-offset (the `mpBodyWritesEntry`/`mpBodyWritesRow`
  store-pattern from `CallerWrites`), the row-loop unrolled.
- `cacheBodyWrites` — the cache-body write skeleton: the count-writes
  for all P candidate rows, sequenced. SHAPE ONLY: the count cells'
  COMPUTATION (the L2/L3 cone) rides the wire above.
- `CellContentTarget` — the named delivery target: the cache body's run
  delivers `CellContent` — the per-cell contract the EncodingIdentity
  derivation consumes. The cone-port's execution proof discharges this
  target.

THE REMAINING SLICES: the count-derivation lemma (the exponential
encoding composed with `fft_view`); the writes' execution derivation
(the Seg half of mpBody's run); the step count for `CallerHdom`. Until
they land, `CallerTarget(Layered)` and the twin stay conditional —
honestly: no solver is postulated, no (min,+) product is claimed. D7's
boundary stands.
-/

namespace ThinMatrix.CacheBodyWrites

open ThreeSumApsp Light
  ThinMatrix.CallerWrites ThinMatrix.CallerFill1
  ThinMatrix.BinaryArrayFFT

/-- The cone's value contract, re-exported at the caller's namespace:
the FFT's output view is the cyclic convolution of the input views
(`ThinMatrix.BinaryArrayFFT.fft_view`, consumed not re-proved). -/
theorem fft_view_caller {B k : ℕ} {s : Register ((2 ^ B : ℕ) : ℤ)}
    {inverse : Bool} {a : Array Cell} :
    viewCells (fft B s inverse k a).value =
      (ArrayFFT.fft B inverse k (viewCells a)).value :=
  fft_view B k s inverse a

/-- The cone's cost brick, re-exported: the tabulate bound
(`ThinMatrix.BinaryArrayFFT.tabulate_bitSteps_bound`) — the `CallerHdom`
step count's FFT-side component. -/
theorem tabulate_bound_caller {α : Type} {N : ℕ}
    (f : Fin N → BinaryResult α) (C : ℕ) (hC : ∀ i, (f i).bitSteps ≤ C) :
    (tabulate N f).bitSteps ≤ N * C :=
  tabulate_bitSteps_bound f C hC

#print axioms fft_view_caller
#print axioms tabulate_bound_caller

end ThinMatrix.CacheBodyWrites
