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
    {P I : ℕ} {μ₁ : ℕ → ℤ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
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

/-- The all-rounds target: the same reading at every round boundary —
given the encoding-identity socket per round and the certified score
cells at the queried state. The reading is flag-independent: the score
table is the evidence, the flags gate the argmin. The ONE-ROUND lemma
discharges it per candidate per round — the socket-theorem proving it
from the per-round encoding-identity family is the next session's
opener (its conclusion should be stated in the unfolded ∀-form — the
`ReadingAllRounds Op W` def-application's implicit-synthesis is the
elaboration trap this round hit). -/
def ReadingAllRounds
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ} {sb : ℕ}
    (Op : ℕ → ℕ → Bool) (W : ℕ) : Prop :=
  ∀ t : ℕ, t < mpRounds W → ∀ (μ₁ : ℕ → ℤ),
    (∀ p < P, μ₁ (sb + p) = DenseScoreTablePass.scores active rows I p) →
    ∀ p < P, oracleAnswerOf sb P μ₁ p = Op t p

/-! ## The all-rounds socket-theorem -/

/-- THE ALL-ROUNDS READING: at every scheduled round, the certified score
cells read as the round's answers through `oracleAnswerOf` — given the
encoding-identity socket per round (`henc`, the parameter
concretization's per-round deliverable) and the certified score cells at
the queried state (the reading is flag-independent: the score table is
the evidence, the flags gate the argmin). The conclusion is stated in
the UNFOLDED ∀-form — the def-application's implicit-synthesis is the
elaboration trap this round hit. -/
theorem readingAllRounds_of_socket
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ} {sb : ℕ} (W : ℕ)
    (Op : ℕ → ℕ → Bool)
    (henc : ∀ t < mpRounds W, ∀ p < P,
      ((DenseScoreTablePass.scores active rows I p : ℤ) ≠ 0) ↔ Op t p = true) :
    ∀ (t : ℕ), t < mpRounds W → ∀ (μ₁ : ℕ → ℤ),
      (∀ p < P, μ₁ (sb + p) = DenseScoreTablePass.scores active rows I p) →
      ∀ p < P, oracleAnswerOf sb P μ₁ p = Op t p := by
  intro t ht μ₁ hcells p hp
  exact reading_at_one_round (Op t) (fun q hq => henc t ht q hq)
    (fun q hq => hcells q hq) p hp

#print axioms reading_at_one_round
#print axioms readingAllRounds_of_socket

end ThinMatrix.CallerReading
