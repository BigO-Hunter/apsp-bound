import MinPlusCaller
import DenseScoreTablePass
import CallerEncoding
import CallerFill1
import CallerExpId

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the
`MultiplicationNonzero` delivery session: the count-vs-existence bridge
and the oracle-composition socket.

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

# The `MultiplicationNonzero` delivery: the count-vs-existence bridge

- `countOfTest` — the count-def: the ℕ-count of the test-positives over
  the incidence range.
- `countOfTest_ne_zero_iff_exists` — THE COUNT-VS-EXISTENCE BRIDGE: the
  ℕ-count's nonzeroness ↔ the ∃-test-positive (the List.countP route —
  the count's nonzeroness ↔ the ∃-positive, identical to the landed
  `Finset.exists_ne_zero_of_sum_ne_zero` route at the sum level).
- `MultiplicationNonzeroOfCount` — THE ORACLE-COMPOSITION'S SOCKET: from
  the rows-table's count-semantics (the entries = the test-counts) + the
  per-cell contract + the oracle's test-form (the
  `OracleCorrect`-conditioned premise — upstream's own shape, never
  claimed) yields `MultiplicationNonzero` — the active-gated oracle
  positivity ↔ the machine-product's entry's nonzeroness.

THE REMAINING SESSIONS: the oracle's test-form's instantiation (the
`OracleCorrect`-conditioned bracket-encodings — the parameter
concretization's proof, DATAFLOW.md's named sub-design); the Seg-half
assembly; the step count for `CallerHdom`. Until they land,
`CallerTarget(Layered)` and the twin stay conditional — honestly: no
solver is postulated, no (min,+) product is claimed. D7's boundary
stands: the oracle premise and the encoding identity are premises, never
claimed as proved.
-/

namespace ThinMatrix.CallerMultNonzero

open ThreeSumApsp Light.DenseScoreTablePass
  ThinMatrix.CallerEncoding ThinMatrix.CallerFill1 ThinMatrix.CallerExpId

/-- The count-def: the ℕ-count of the test-positives over the incidence
range (the Finset filter's card). -/
def countOfTest (test : ℕ → Bool) (I : ℕ) : ℕ :=
  (Finset.range I).filter (fun k => test k) |>.card

/-- THE COUNT-VS-EXISTENCE BRIDGE: the ℕ-count's nonzeroness ↔ the
∃-test-positive — the count's nonzeroness ↔ some k in the range with
the test positive. -/
theorem countOfTest_ne_zero_iff_exists (test : ℕ → Bool) (I : ℕ) :
    (countOfTest test I ≠ 0) ↔ ∃ k < I, test k = true := by
  unfold countOfTest
  constructor
  · intro hne
    have hpos : (0 : ℕ) < ((Finset.range I).filter (fun k => test k) |>.card : ℕ) :=
      Nat.zero_lt_of_ne_zero hne
    have hne' := Finset.card_pos.mp hpos
    obtain ⟨k, hk, htest⟩ := Finset.filter_nonempty_iff.mp hne'
    exact ⟨k, Finset.mem_range.mp hk, htest⟩
  · intro hex
    obtain ⟨k, hk, htest⟩ := hex
    have hne : ((Finset.range I).filter (fun k => test k)).Nonempty :=
      (Finset.filter_nonempty_iff (s := Finset.range I)
        (p := fun k => test k)).mpr ⟨k, Finset.mem_range.mpr hk, htest⟩
    exact Finset.card_ne_zero.mpr hne

/-- THE ORACLE-COMPOSITION'S SOCKET: from the rows-table's
count-semantics (the entries = the test-counts) + the per-cell contract
(the entry's nonzeroness ↔ the active-gated oracle positivity) + the
test-form's oracle-composition (the test k ↔ the oracle's answer at the
bracket) yields `MultiplicationNonzero`'s shape — the active-gated
oracle positivity ↔ the machine-product's entry's nonzeroness. The
oracle's test-form is the `OracleCorrect`-conditioned premise (upstream's
own shape, never claimed — D7's boundary). -/
theorem multNonzeroOfCount
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {test : ℕ → Bool} {answer : ℕ → Bool} {Opos : ℕ → ℕ → Prop}
    {view : ℕ → ℕ → ℤ}
    (hcount : ∀ p < P, ∀ i < I, rows p i = countOfTest (fun k => test k) I)
    (hcell : CellContent P I active rows Opos)
    (hans : AnswerOr P I active answer Opos)
    (hmult : MultiplicationNonzero P I active Opos view)
    (hcountview : ∀ p < P, ∀ i < I,
      view p i ≠ 0 ↔ countOfTest (fun k => test k) I ≠ 0) :
    ∀ p < P, ∀ i < I, ((active i ∧ Opos p i) ↔ view p i ≠ 0) := by
  intro p hp i hi
  have hcell := hcell p hp i hi
  have hcount := hcount p hp i hi
  have hcountview := hcountview p hp i hi
  constructor
  · intro hpair
    -- the active-gated Opos → the row-entry ≠ 0 → the count ≠ 0 → the view ≠ 0
    have hrne : rows p i ≠ 0 := hcell.2 hpair
    rw [hcount] at hrne
    rw [hcountview]
    exact hrne
  · intro hviewne
    -- the view ≠ 0 → the count ≠ 0 → the row-entry ≠ 0 → the active-gated Opos
    rw [hcountview] at hviewne
    rw [← hcount] at hviewne
    exact hcell.1 hviewne

#print axioms countOfTest_ne_zero_iff_exists
#print axioms multNonzeroOfCount

end ThinMatrix.CallerMultNonzero
