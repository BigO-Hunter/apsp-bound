import MinPlusCaller
import DenseScoreTablePass
import DenseArgminPass
import CallerDataflow
import CallerSegments

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the reading-lemma session (the design's first consumed proof).

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

# The reading lemma: the certified cells read as the round's answers

`reading_at_one_round` — THE DESIGN'S FIRST CONSUMED PROOF: at one
scheduled round, the certified score cells (`cert_scores`' clause —
consumed, not re-proved) read, through the design's `oracleAnswerOf`, as
the round's answers — GIVEN the encoding-identity socket (`henc`: the
score's nonzeroness ↔ the round's answer). The socket is the parameter
concretization's deliverable (DATAFLOW.md's named remaining sub-design —
the mod-p/band encoding at the pinning, upstream's own shape: the
`OracleCorrect`-conditioned construction lemmas consume the same
identity). D7's boundary stands: the oracle premise and the encoding
identity are premises, never claimed as proved.

`ReadingAllRounds` — the all-rounds target, stated as the named next
slice: the same reading at every round boundary of the chain's run (the
per-round certified posts feed the one-round lemma through the
`chain_from` induction's structure).
-/

namespace ThinMatrix.CallerReading

open ThreeSumApsp Light
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  ThinMatrix.CallerDataflow

/-- THE DESIGN'S FIRST CONSUMED PROOF: at one scheduled round, the
certified score cells read as the round's answers through
`oracleAnswerOf` — given the encoding-identity socket (`henc`: the
score's nonzeroness ↔ the answer). The certified-score premise is
L6(a)/`chain_runs`' `cert_scores` clause, consumed not re-proved; the
socket is DATAFLOW.md's named parameter-concretization deliverable. -/
theorem reading_at_one_round
    {P I : ℕ} {μ₁ : ℕ → ℤ} {active mask : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {sb : ℕ} (Op : ℕ → Bool)
    (henc : ∀ p < P,
      ((DenseScoreTablePass.scores active rows I p : ℤ) ≠ 0) ↔ Op p = true)
    (hcert : ∀ p < P, μ₁ (sb + p) = DenseScoreTablePass.scores active rows I p)
    (p : ℕ) (hp : p < P) :
    oracleAnswerOf sb P μ₁ p = Op p := by
  unfold oracleAnswerOf
  rw [hcert p hp]
  by_cases hpos : (DenseScoreTablePass.scores active rows I p : ℤ) ≠ 0
  · have hops : Op p = true := (henc p hp).1 hpos
    have hdec : (decide (p < P ∧ ((DenseScoreTablePass.scores active rows I p : ℤ) ≠ 0)) : Bool) = true :=
      decide_eq_true ⟨hp, hpos⟩
    rw [hdec]
    exact hops.symm
  · push_neg at hpos
    have hops : ¬(Op p = true) := fun h => (henc p hp).2 h hpos
    have hdec : (decide (p < P ∧ ((DenseScoreTablePass.scores active rows I p : ℤ) ≠ 0)) : Bool) = false :=
      decide_eq_false (fun hc => hc.2 hpos)
    rw [hdec]
    simp [hops]

/-- The all-rounds target: the same reading at every round boundary of
the chain's run — the per-round certified posts feed the one-round lemma
through the `chain_from` induction's structure. Stated as the named next
slice; not yet proved. -/
def ReadingAllRounds
    {P I : ℕ} {μ₀ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {sb mb : ℕ} (Op : ℕ → ℕ → Bool) (W : ℕ) (R : Light.Program) : Prop :=
  ∀ t : ℕ, t < mpRounds W → ∀ (μ₁ : ℕ → ℤ) (mask : ℕ → Bool),
    (∀ p < P, μ₁ (mb + p) = DenseArgminPass.bit (mask p)) →
    (∀ p < P, oracleAnswerOf sb P μ₁ p = Op t p)

#print axioms reading_at_one_round

end ThinMatrix.CallerReading
