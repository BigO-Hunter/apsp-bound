import MinPlusCaller
import CallerEncoding

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the oracle
test-form's instantiation session.

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

# The oracle test-form's instantiation: the bracket tests

The design's test-form defs at the caller's pinning (the ℕ-indexed
shapes, upstream `MinPlusReduction.refine`'s test matrices byte-formed):

- `CallerOracle` — the caller's abstract oracle: the triangle test at
  the caller's ℕ-indexed table shapes (the upstream `TriangleOracle`'s
  ℕ-indexed form).
- `CallerOracleCorrect` — the oracle's correctness: the triangle test's
  answer ↔ the zero-sum existence — upstream `OracleCorrect`'s
  ℕ-indexed form. THE PREMISE (D7's boundary: the oracle's correctness
  is the premise, never claimed).
- `lowerTestTable` / `upperTestTable` — the threshold-table defs
  (byte-shaped to upstream `refine`'s test matrices, via the landed
  `lowerTestEntry`/`upperTestEntry`).
- `bracketTestLower` / `bracketTestUpper` — the oracle's invocations at
  the threshold tables.
- `bracketTestLower_correct` / `bracketTestUpper_correct` — the
  `OracleCorrect`-conditioned answers: the bracket tests' trueness ↔
  the zero-sum existence at the thresholds — upstream
  `OracleCorrect`'s triangle-form consumed at the encoded tables.

D7's boundary stands: the oracle's correctness and the encoding
identity are premises, never claimed as proved; no (min,+) product is
claimed in this module.
-/

namespace ThinMatrix.CallerTestForm

open ThreeSumApsp ThinMatrix.CallerEncoding

/-- The caller's abstract oracle: the triangle test at the caller's
ℕ-indexed table shapes (the upstream `TriangleOracle`'s ℕ-indexed
form). -/
def CallerOracle := (ℕ → ℕ → ℤ) → (ℕ → ℕ → ℤ) → (ℕ → ℕ → ℤ) → ℕ → ℕ → Bool

/-- The caller's oracle correctness: the triangle test's answer ↔ the
zero-sum existence — upstream `OracleCorrect`'s ℕ-indexed form. THE
PREMISE (D7's boundary: the oracle's correctness is the premise, never
claimed). -/
def CallerOracleCorrect (O : CallerOracle) : Prop :=
  ∀ A B T i j, O A B T i j = true ↔ ∃ k, A i k + B k j + T i j = 0

/-- The lower test's third-table: the threshold-encodings per entry —
byte-shaped to upstream `MinPlusReduction.refine`'s lower test matrix. -/
def lowerTestTable (C : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ :=
  fun i j => lowerTestEntry (C i j)

/-- The upper test's third-table: the threshold-encodings per entry —
byte-shaped to upstream `refine`'s upper test matrix. -/
def upperTestTable (C : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ :=
  fun i j => upperTestEntry (C i j)

/-- THE BRACKET TEST (the lower — the priority): the oracle's
triangle-form at the lower-threshold tables. -/
def bracketTestLower (O : CallerOracle) (A_t B_t T_t : ℕ → ℕ → ℤ)
    (i j : ℕ) : Bool :=
  O A_t B_t (lowerTestTable T_t) i j

/-- THE BRACKET TEST (the upper): the oracle's triangle-form at the
upper-threshold tables. -/
def bracketTestUpper (O : CallerOracle) (A_t B_t T_t : ℕ → ℕ → ℤ)
    (i j : ℕ) : Bool :=
  O A_t B_t (upperTestTable T_t) i j

/-- THE LOWER TEST'S ANSWER: under the oracle's correctness, the lower
test's trueness ↔ the zero-sum existence at the lower threshold —
upstream `OracleCorrect`'s triangle-form consumed at the encoded
tables. -/
theorem bracketTestLower_correct (O : CallerOracle)
    {A_t B_t T_t : ℕ → ℕ → ℤ} {i j : ℕ} (hO : CallerOracleCorrect O) :
    bracketTestLower O A_t B_t T_t i j = true ↔
      ∃ k, A_t i k + B_t k j + lowerTestTable T_t i j = 0 := by
  exact hO A_t B_t (lowerTestTable T_t) i j

/-- THE UPPER TEST'S ANSWER: under the oracle's correctness, the upper
test's trueness ↔ the zero-sum existence at the upper threshold. -/
theorem bracketTestUpper_correct (O : CallerOracle)
    {A_t B_t T_t : ℕ → ℕ → ℤ} {i j : ℕ} (hO : CallerOracleCorrect O) :
    bracketTestUpper O A_t B_t T_t i j = true ↔
      ∃ k, A_t i k + B_t k j + upperTestTable T_t i j = 0 := by
  exact hO A_t B_t (upperTestTable T_t) i j

#print axioms bracketTestLower_correct
#print axioms bracketTestUpper_correct

end ThinMatrix.CallerTestForm
