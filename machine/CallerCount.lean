import MinPlusCaller
import DenseScoreTablePass
import CallerEncoding
import CacheBodyWrites
import CallerReading

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the count-
derivation session: the composition's sockets and the transport lemma.

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

# The count-derivation: the composition's sockets and the transport

The Seg half's count cells ride the exponential encoding (the
min-plus-as-multiplication identity — upstream's own conversion,
`DenseOracleCorrect`-conditioned) composed with the FFT's round-trip
(`fft_view_caller`). This module pins the composition's sockets:

- `CountCellOfFft` — the count-cell ↔ FFT-cell socket: the incidence
  count's nonzeroness ↔ the FFT-computed table's cell's nonzeroness.
  THE COMPOSITION LEMMA (the exponential-encoding identity composed
  with `fft_view_caller` at one cell) discharges this socket — its
  premise shapes are DATAFLOW.md's named sub-design; D7's boundary
  stands (the encoding identity is a premise, never claimed).
- `encodingIdentity_transport` — the transport: the EncodingIdentity is
  invariant under the rows-table's pointwise equality — the
  substitution the Seg half's table-identification uses.
- `ReadingAllRounds_transport` — the same transport for the all-rounds
  reading: the answers are invariant under the rows-table's equality.

THE REMAINING SESSIONS: the composition lemma (the exponential encoding
composed with `fft_view_caller` at one cell — discharging
`CountCellOfFft`); the Seg-half assembly (the bracket accumulation via
`refineStep` — the writes' shapes landed); the step count for
`CallerHdom`. Until they land, `CallerTarget(Layered)` and the twin
stay conditional — honestly: no solver is postulated, no (min,+) product
is claimed. D7's boundary stands.
-/

namespace ThinMatrix.CallerCount

open ThreeSumApsp Light.DenseScoreTablePass Light
  ThinMatrix.MinPlusCaller ThinMatrix.CallerEncoding ThinMatrix.CallerReading
  ThinMatrix.CallerDataflow

/-- The count-cell ↔ FFT-cell socket: the incidence count's nonzeroness ↔
the FFT-computed table's cell's nonzeroness, per (p, i). THE COMPOSITION
LEMMA discharges this socket — the exponential-encoding identity
composed with `fft_view_caller` at one cell (the premise shapes are
DATAFLOW.md's named sub-design; the encoding identity is a premise,
never claimed as proved — D7's boundary). -/
def CountCellOfFft (P I : ℕ) (active : ℕ → Bool)
    (rows fftTable : ℕ → ℕ → ℕ) : Prop :=
  ∀ p < P, ∀ i < I, (rows p i ≠ 0 ↔ fftTable p i ≠ 0)

/-- The transport: the EncodingIdentity is invariant under the
rows-table's pointwise equality — the substitution the Seg half's
table-identification uses. -/
theorem encodingIdentity_transport
    {P I : ℕ} {active : ℕ → Bool} {answer : ℕ → Bool}
    {rows rows' : ℕ → ℕ → ℕ} (heq : rows = rows')
    (hid : EncodingIdentity P I active rows answer) :
    EncodingIdentity P I active rows' answer := by
  subst heq
  exact hid

/-- The transport for the all-rounds reading: the answers are invariant
under the rows-table's pointwise equality. (The conclusion in the
unfolded ∀-form — the def-application's implicit-synthesis is the
elaboration trap.) -/
theorem ReadingAllRounds_transport
    {P I : ℕ} {active : ℕ → Bool} {sb : ℕ} {W : ℕ}
    {Op : ℕ → ℕ → Bool} {rows rows' : ℕ → ℕ → ℕ} (heq : rows = rows')
    (hall : ∀ (t : ℕ), t < mpRounds W → ∀ (μ₁ : ℕ → ℤ),
      (∀ p < P, μ₁ (sb + p) = DenseScoreTablePass.scores active rows I p) →
      ∀ p < P, oracleAnswerOf sb P μ₁ p = Op t p) :
    ∀ (t : ℕ), t < mpRounds W → ∀ (μ₁ : ℕ → ℤ),
      (∀ p < P, μ₁ (sb + p) = DenseScoreTablePass.scores active rows I p) →
      ∀ p < P, oracleAnswerOf sb P μ₁ p = Op t p := by
  subst heq
  exact hall

#print axioms encodingIdentity_transport
#print axioms ReadingAllRounds_transport

end ThinMatrix.CallerCount
