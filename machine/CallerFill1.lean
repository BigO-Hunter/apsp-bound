import MinPlusCaller
import DenseScoreTablePass
import CallerEncoding
import CallerDataflow

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 1 — the cache content
contract's consumption: the EncodingIdentity derivation.

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

# Fill 1's content consumption: the EncodingIdentity derivation

The cache-slot's content contract (upstream's own, byte-identical:
`cacheContent O A = Oracle.Correct O A`) — at the caller's pinning, in
the two socket shapes the derivation consumes:

- `CellContent` — the per-cell contract: the cached row-entry's
  nonzeroness is the active-gated oracle positivity at (p, i). THE
  DELIVERY is the composite-incidence construction's own content
  (the `DenseOracleCorrect`-conditioned chain — consumed as the
  premise, never claimed; the L2/L3 cone's cache-body port rides
  board-side per CacheFill's recorded deferral).
- `AnswerOr` — the per-candidate answer contract: the answer's trueness
  is the active OR of the oracle positivities.

- `encodingIdentity_of_content` — THE DERIVATION: `CellContent +
  AnswerOr` yield `EncodingIdentity` (the reading lemma's socket) — the
  count-vs-existence bridge at the ℕ-sum level: the score's nonzeroness
  ↔ some active entry nonzero (the ℕ-sum's nonnegativity — the entries
  are counts, nonnegative by type) ↔ the active OR of the
  positivities ↔ the answer.

THE CACHE BODY'S LIGHT STATEMENT: the per-(p, i) count-writes ride the
landed `CallerWrites.mpBodyWritesRow` store-pattern at the cache's own
register map; the L2/L3 cone (the score-table pass + the BinaryArrayFFT
cyclic path) is the board-side port's content — CacheFill's recorded
deferral, unchanged. D7's boundary stands: the oracle premise and the
content contracts are premises, never claimed as proved; no (min,+)
product is claimed in this module.
-/

namespace ThinMatrix.CallerFill1

open ThreeSumApsp Light.DenseScoreTablePass
  ThinMatrix.CallerEncoding

/-- The per-cell content contract: the cached row-entry's nonzeroness is
the active-gated oracle positivity at (p, i). The DELIVERY is the
composite-incidence construction's own content (the
`DenseOracleCorrect`-conditioned chain — consumed as the premise, never
claimed; the L2/L3 cone's cache-body port rides board-side per
CacheFill's recorded deferral). -/
def CellContent (P I : ℕ) (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (Opos : ℕ → ℕ → Prop) : Prop :=
  ∀ p < P, ∀ i < I, (rows p i ≠ 0 ↔ active i ∧ Opos p i)

/-- The per-candidate answer contract: the answer's trueness is the
active OR of the oracle positivities. -/
def AnswerOr (P I : ℕ) (active : ℕ → Bool) (answer : ℕ → Bool)
    (Opos : ℕ → ℕ → Prop) : Prop :=
  ∀ p < P, (answer p = true ↔ ∃ i < I, active i ∧ Opos p i)

/-- THE DERIVATION: `CellContent + AnswerOr` yield `EncodingIdentity`
(the reading lemma's socket) — the count-vs-existence bridge at the ℕ
level: the score's nonzeroness ↔ some active entry nonzero (the entries
are counts, nonnegative by type) ↔ the active OR of the positivities ↔
the answer. -/
theorem encodingIdentity_of_content
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ} {answer : ℕ → Bool}
    {Opos : ℕ → ℕ → Prop}
    (hcell : CellContent P I active rows Opos)
    (hans : AnswerOr P I active answer Opos) :
    EncodingIdentity P I active rows answer := by
  intro p hp
  have hcell := hcell p hp
  have hans := hans p hp
  constructor
  · intro hne
    rw [scores_eq_sum] at hne
    obtain ⟨i, hi, hne'i⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hai : active i = true := by
      by_cases h : active i = true
      · exact h
      · rw [if_neg h] at hne'i
        exact absurd hne'i (by simp)
    have hrne : rows p i ≠ 0 := by
      rw [if_pos hai] at hne'i
      exact hne'i
    have hpair : active i = true ∧ Opos p i :=
      (hcell i (Finset.mem_range.mp hi)).1 hrne
    exact hans.2 ⟨i, Finset.mem_range.mp hi, hpair.1, hpair.2⟩
  · intro htrue hzero
    obtain ⟨i, hi, hai, hpos⟩ := hans.1 htrue
    have hrne : rows p i ≠ 0 := (hcell i hi).2 ⟨hai, hpos⟩
    rw [scores_eq_sum] at hzero
    have hge : (if active i then rows p i else 0) ≤
        ∑ j ∈ Finset.range I, (if active j then rows p j else 0) :=
      Finset.single_le_sum (f := fun j => (if active j then rows p j else 0))
        (fun j _ => Nat.zero_le _) (Finset.mem_range.2 hi)
    rw [if_pos hai, hzero] at hge
    omega

#print axioms encodingIdentity_of_content

end ThinMatrix.CallerFill1
