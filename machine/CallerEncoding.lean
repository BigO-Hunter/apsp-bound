import MinPlusCaller
import DenseScoreTablePass
import CallerDataflow

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the
parameter-concretization session: the encoding shapes and the
encoding-identity premise.

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

# The parameter concretization: the encoding shapes and the identity premise

The design's named remaining sub-design (DATAFLOW.md), pinned at the
caller's pinning:

- `lowerTestEntry` / `upperTestEntry` — the two adaptive tests' threshold
  encodings: the third-table entries `-(2·C)` and `-(2·C + 1)` —
  byte-shaped to upstream `MinPlusReduction.refine`'s test matrices
  (`fun i j => -(2 * C i j))` / `(fun i j => -(2 * C i j + 1))`).
- `residTabShape` / `smallTabShape` — the mod-p table shapes (upstream
  Batch procedures 77/78): `dst[q] := sgn·src[q] mod p` and
  `dst[h] := (h·mul + add) mod p` — the encoding arithmetic's shapes,
  byte-formed to `OProg.lean`'s procedure map.
- `EncodingIdentity` — THE ENCODING-IDENTITY PREMISE: the score's
  nonzeroness ↔ the round's answer, per candidate. This is the premise
  the reading lemma consumes per round; its DELIVERY (the proof) is the
  composite-incidence construction's own content, conditioned on
  `DenseOracleCorrect` — consumed as a premise, never claimed as proved
  (D7's boundary).
- `henc_of_identity` — the derivation: the identity premise (at the ℕ
  score level) yields the reading lemma's ℤ-cast socket
  (`Nat.cast_ne_zero`/omega — the cast is the only glue).

D7's boundary stands: the encoding's correctness is upstream's
`DenseOracleCorrect`-conditioned chain; no (min,+) product is claimed in
this module.
-/

namespace ThinMatrix.CallerEncoding

open ThreeSumApsp Light.DenseScoreTablePass

/-! ## The bracket-threshold encodings -/

/-- The lower test's threshold encoding: the third-table entry
`-(2·C[i,j])` — the oracle's zero-sum test at the bracket's floor.
Byte-shaped to upstream `MinPlusReduction.refine`'s lower test matrix. -/
def lowerTestEntry (C : ℤ) : ℤ := -(2 * C)

/-- The upper test's threshold encoding: `-(2·C + 1)` — at the bracket's
step. Byte-shaped to upstream `refine`'s upper test matrix. -/
def upperTestEntry (C : ℤ) : ℤ := -(2 * C + 1)

/-! ## The mod-p table shapes (the upstream Batch procedures 77/78) -/

/-- The residTab shape (upstream Batch procedure 77): `dst[q] :=
sgn·src[q] mod p` — the signed residue table. -/
def residTabShape (sgn p : ℤ) (src : ℕ → ℤ) (q : ℕ) : ℤ := (sgn * src q) % p

/-- The smallTab shape (upstream Batch procedure 78): `dst[h] :=
(h·mul + add) mod p` — the affine residue table. -/
def smallTabShape (mul add p : ℤ) (h : ℕ) : ℤ := ((h : ℤ) * mul + add) % p

/-! ## The encoding-identity premise and the reading socket -/

/-- THE ENCODING-IDENTITY PREMISE: the score's nonzeroness ↔ the round's
answer, per candidate — the parameter concretization's deliverable. The
DELIVERY (the proof) is the composite-incidence construction's own
content, conditioned on `DenseOracleCorrect` — consumed as a premise,
never claimed as proved (D7's boundary). -/
def EncodingIdentity (P I : ℕ) (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (answer : ℕ → Bool) : Prop :=
  ∀ p < P, (scores active rows I p ≠ 0) ↔ answer p = true

/-- The reading lemma's ℤ-cast socket, derived from the identity
premise: the cast is the only glue (`Nat.cast_ne_zero`, via omega over
the ℕ/ℤ atoms). -/
theorem henc_of_identity
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ} {answer : ℕ → Bool}
    (hid : EncodingIdentity P I active rows answer)
    (p : ℕ) (hp : p < P) :
    ((scores active rows I p : ℤ) ≠ 0) ↔ answer p = true := by
  rw [Nat.cast_ne_zero]
  exact hid p hp

#print axioms henc_of_identity

end ThinMatrix.CallerEncoding
