import MinPlusCaller
import DenseScoreTablePass
import Submission.ThreeSumApsp.LowCache.FFT.BinaryArrayFFT
import CallerCountCompose

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the
premise-shapes' production session: the exponential-encoding premise and
the round-trip discharge.

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

# The premise-shapes' production: the exponential-encoding premise and
the round-trip discharge

- `productIndexOf` — the entry-index map: the cache-entry (p, i) at the
  cyclic convolution's index `(p * I + i) % N` (the padded size N ≥ the
  layout span — the padding's guarantee, `pad q N a`).
- `productViewOf` — the machine-product's recovered-entry view at that
  index: `((multiplication q A a b).value.getD … zeroInteger).view`.
- `recovOf` — the entry's magnitude (the natAbs): the count's ℕ-form.
- `fftTableOf` — the FFT-computed table's entry: the cyclic convolution
  of the input views at the product index.
- `ExponentialEncoding` — SOCKET 1's premise-def: the count-entry's
  nonzeroness ↔ the recovered-entry's nonzeroness. THE COMPOSITE-
  INCIDENCE CONSTRUCTION'S OWN CONTENT — the premise, never claimed
  (D7's boundary).
- `roundTrip_of_multiplication` — SOCKET 2's discharge: the recovered-
  entry's magnitude = the FFT-computed table's entry, from the wired
  cone's top contract (`multiplication_correct` — the machine-product's
  per-entry view = the cyclic convolution of the input views at j).
- `countCellOfFft_of_premises` — the composition: socket 1 + socket 2
  yield the count-cell ↔ FFT-table socket (`CountCellOfFft`'s shape) —
  the magnitude-glue (the natAbs/≠-transport) composed.

D7's boundary stands: the encoding identity and the oracle conversion
are premises, never claimed as proved; no (min,+) product is claimed in
this module.
-/

namespace ThinMatrix.CallerPremises

open ThreeSumApsp Light.DenseScoreTablePass Light
  ThinMatrix.BinaryArrayFFT
  ThinMatrix.CallerCountCompose ThinMatrix.CallerCount

variable {q A : ℕ} [NeZero q]

/-- The entry-index map: the cache-entry (p, i) at the cyclic
convolution's index `(p * I + i) % N`. -/
def productIndexOf (I N : ℕ) (p i : ℕ) : ℕ := (p * I + i) % N

/-- The machine-product's recovered-entry view at the product index. -/
def productViewOf (q A I N : ℕ) (a b : Array Integer) (p i : ℕ) : ℤ :=
  ((multiplication q A a b).value.getD (productIndexOf I N p i % q) zeroInteger).view

/-- The entry's magnitude (the natAbs): the count's ℕ-form. -/
def recovOf (q A I N : ℕ) (a b : Array Integer) (p i : ℕ) : ℕ :=
  (productViewOf q A I N a b p i).natAbs

/-- The FFT-computed table's entry: the cyclic convolution of the input
views at the product index (the padded size `q` nonzero: the NeZero
instance). -/
def fftTableOf (q I N : ℕ) [NeZero q] (a b : Array Integer) (p i : ℕ) : ℤ :=
  CyclicRing.convolution (ArrayFFT.asCyclic q (viewIntegers a))
    (ArrayFFT.asCyclic q (viewIntegers b))
    ⟨productIndexOf I N p i % q,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne (n := q)))⟩

/-- SOCKET 1's premise-def: the count-entry's nonzeroness ↔ the
recovered-entry's nonzeroness. THE COMPOSITE-INCIDENCE CONSTRUCTION'S
OWN CONTENT — the premise, never claimed (D7's boundary). -/
def ExponentialEncoding (P I : ℕ) (active : ℕ → Bool)
    (rows recov : ℕ → ℕ → ℕ) : Prop :=
  ∀ p < P, ∀ i < I, (rows p i ≠ 0 ↔ recov p i ≠ 0)

/-- SOCKET 2's discharge: the recovered-entry's magnitude = the
FFT-computed table's entry — from the wired cone's top contract
(`multiplication_correct`: the machine-product's per-entry view = the
cyclic convolution of the input views at j). -/
theorem roundTrip_of_multiplication
    (q A : ℕ) [NeZero q] (hA : 1 ≤ A) (a b : Array Integer)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A)
    (I N : ℕ) (p i : ℕ) :
    recovOf q A I N a b p i =
      (fftTableOf q I N a b p i).natAbs := by
  unfold recovOf fftTableOf productViewOf
  exact congrArg Int.natAbs (multiplication_correct q A hA a b ha hb
    ⟨productIndexOf I N p i % q,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne (n := q)))⟩)

/-- THE COMPOSITION: socket 1 + socket 2 yield the count-cell ↔ FFT-table
socket (`CountCellOfFft`'s shape) — the magnitude-glue (the natAbs/≠
transport) composed. -/
theorem countCellOfFft_of_premises
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {q A : ℕ} [NeZero q] (hA : 1 ≤ A) (a b : Array Integer)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A)
    (hexp : ExponentialEncoding P I active rows (recovOf q A I N a b)) :
    ∀ p < P, ∀ i < I, (rows p i ≠ 0 ↔ fftTableOf q I N a b p i ≠ 0) := by
  intro p hp i hi
  have hrecov := hexp p hp i hi
  have hrt := roundTrip_of_multiplication q A hA a b ha hb I N p i
  rw [hrecov, hrt, Int.natAbs_ne_zero]

#print axioms roundTrip_of_multiplication
#print axioms countCellOfFft_of_premises

end ThinMatrix.CallerPremises
