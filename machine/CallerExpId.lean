import MinPlusCaller
import DenseScoreTablePass
import CallerPremises
import CallerFill1

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the
exponential-encoding identity's composition session.

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

# The exponential-encoding identity: composed from the sockets

`ExponentialEncoding` (the count-entry's nonzeroness ↔ the recovered-
entry's nonzeroness) composed from three sockets:

- `CellContent` — the per-cell contract (the active-gated oracle
  positivity). THE DELIVERY is the composite-incidence construction's
  own content — consumed as the premise, never claimed.
- `MultiplicationNonzero` — THE EXPONENTIAL-ENCODING PREMISE (the
  DATAFLOW.md named sub-design): the active-gated oracle positivity ↔
  the machine-product's entry's nonzeroness. THE PREMISE, never claimed
  (the encoding's correctness is upstream's `DenseOracleCorrect`-
  conditioned chain; D7's boundary).
- the round-trip (`recovOf` = the entry's magnitude — the landed
  `roundTrip_of_multiplication` chain, consumed).

THE REMAINING SESSIONS: the `MultiplicationNonzero` premise's own
delivery (the exponential-encoding's parameter concretization's proof —
DATAFLOW.md's named sub-design); the Seg-half assembly (the bracket
accumulation via `refineStep` — the writes' shapes landed); the step
count for `CallerHdom`. Until they land, `CallerTarget(Layered)` and
the twin stay conditional — honestly: no solver is postulated, no
(min,+) product is claimed. D7's boundary stands: the encoding identity
and the oracle premise are premises, never claimed as proved.
-/

namespace ThinMatrix.CallerExpId

open ThreeSumApsp Light.DenseScoreTablePass Light
  ThinMatrix.CallerPremises ThinMatrix.CallerFill1

/-- THE EXPONENTIAL-ENCODING PREMISE (the DATAFLOW.md named
sub-design): the active-gated oracle positivity ↔ the machine-product's
entry's nonzeroness, per (p, i). THE PREMISE, never claimed — the
encoding's correctness is upstream's `DenseOracleCorrect`-conditioned
chain (D7's boundary). -/
def MultiplicationNonzero (P I : ℕ) (active : ℕ → Bool)
    (Opos : ℕ → ℕ → Prop) (view : ℕ → ℕ → ℤ) : Prop :=
  ∀ p < P, ∀ i < I, ((active i ∧ Opos p i) ↔ view p i ≠ 0)

/-- THE EXPONENTIAL-ENCODING IDENTITY, composed from the sockets:
`CellContent` (the per-cell contract) + `MultiplicationNonzero` (the
exponential-encoding premise) + the round-trip (`recovOf` = the entry's
magnitude) yield `ExponentialEncoding` — the count-entry's nonzeroness ↔
the recovered-entry's nonzeroness. -/
theorem exponentialEncoding_of_sockets
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {Opos : ℕ → ℕ → Prop}
    {q A : ℕ} [NeZero q] (hA : 1 ≤ A) (a b : Array ThinMatrix.BinaryArrayFFT.Integer)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A)
    {N : ℕ}
    (hcell : CellContent P I active rows Opos)
    (hmult : ∀ p < P, ∀ i < I, ((active i ∧ Opos p i) ↔
      productViewOf q A I N a b p i ≠ 0))
    (hrt : ∀ p : ℕ, ∀ i : ℕ, recovOf q A I N a b p i =
      (productViewOf q A I N a b p i).natAbs) :
    ExponentialEncoding P I active rows (recovOf q A I N a b) := by
  intro p hp i hi
  have hcell := hcell p hp i hi
  have hrt := hrt p i
  constructor
  · intro hne
    have hpair := hcell.1 hne
    have hviewne := (hmult p hp i hi).1 hpair
    rw [hrt]
    exact Int.natAbs_ne_zero.mpr hviewne
  · intro hne
    have hviewne : productViewOf q A I N a b p i ≠ 0 :=
      Int.natAbs_ne_zero.mp (by rw [← hrt]; exact hne)
    exact hcell.2 ((hmult p hp i hi).2 hviewne)

#print axioms exponentialEncoding_of_sockets

end ThinMatrix.CallerExpId
