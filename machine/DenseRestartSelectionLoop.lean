import DenseCanonicalSelectionRound

/-!
Copyright (c) 2026. APSP port campaign: L4 restart-loop driver.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the canonical greedy selection round this loop restarts
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler
  (`Submission/`) whose Light language these procedures execute in.
- Joshua Wharton (QFEX) — the checked `DenseCanonicalSelectionRound` six-procedure
  round and its closed `Solves` contract, on which this driver is built.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L4: the restart loop over the canonical selection round

`DenseCanonicalSelectionRound.program` is procedure `5`-callable: one greedy
round that scores the active incidences, selects a remaining minimum-score
candidate, copies the selected row into the base buffer, and clears exactly
that candidate's remaining flag. The canonical greedy restarts this round
while the remaining mask is nonempty.

Because a Light program is finite, the restart loop is an unrolling over a
fixed round count `R` (`loopBody x.rounds`, procedure `6` of `program x`).
Each round is one `.call 5` into the appended round program, driven only by
the round's proved contract (`DenseCanonicalSelectionRound.task_solved` via
`Solves.meets`), so the driver does not depend on the round's body. The loop
is sound for exactly `R` rounds because every round requires a flagged
candidate and clears one more: `R` rounds consume `R` of the flagged
candidates, so `Pre` carries `enoughFlags` — at least `R` flagged candidates.

The written-set invariant is a list induction over the round indices: the
cleared set `S₀` grows by exactly the chosen candidate of each round, and the
memory flags read `maskCleared S₀` (original flags, cleared candidates false)
throughout. Everything outside the scores, base and remaining regions is
preserved (`SameOutside3` composed along the rounds), so the active and rows
read premises persist from round to round unchanged.
-/

namespace Light.DenseRestartSelectionLoop

open Light

abbrev Candidates : ℕ := 0
abbrev Len : ℕ := 1
abbrev Height : ℕ := 2
abbrev Active : ℕ := 3
abbrev Rows : ℕ := 4
abbrev Scores : ℕ := 5
abbrev Remaining : ℕ := 6
abbrev Base : ℕ := 7
abbrev Free : ℕ := 8
abbrev Tmp : ℕ := 10

/-- The remaining mask with every candidate of `S` forced off: the flag state
after the rounds whose chosen candidates were exactly `S`. -/
def maskCleared (S : Finset ℕ) (remaining : ℕ → Bool) (p : ℕ) : Bool :=
  remaining p && !(decide (p ∈ S))

/-- The flagged candidates below `P`. -/
def flagged (P : ℕ) (remaining : ℕ → Bool) : Finset ℕ :=
  (Finset.range P).filter fun p => remaining p

/-- Clearing a chosen candidate turns exactly its own flag off. -/
theorem maskCleared_insert (S : Finset ℕ) (remaining : ℕ → Bool) (c p : ℕ) :
    (if p = c then false else maskCleared S remaining p)
      = maskCleared (insert c S) remaining p := by
  by_cases h : p = c
  · subst h
    simp [maskCleared]
  · have hmem : decide (p ∈ insert c S) = decide (p ∈ S) := by
      simp [Finset.mem_insert, h]
    simp [h, maskCleared, hmem]

/-- One round is at least `R` flagged candidates: a fresh flagged candidate
outside the cleared set exists whenever fewer than `R` rounds are done. -/
theorem exists_fresh_flagged {P : ℕ} {remaining : ℕ → Bool} {S : Finset ℕ} {k : ℕ}
    (hsub : S ⊆ flagged P remaining) (hcard : S.card = k)
    (henough : k < (flagged P remaining).card) :
    ∃ p, p < P ∧ remaining p = true ∧ p ∉ S := by
  by_contra h
  have hF : flagged P remaining ⊆ S := by
    intro a ha
    by_contra hain
    simp only [flagged, Finset.mem_filter, Finset.mem_range] at ha
    exact h ⟨a, ha.1, ha.2, hain⟩
  have h2 := Finset.card_le_card hF
  omega

/-- One restart-loop instance: the round's parameters plus the restart count. -/
structure Inst where
  rounds : ℕ
  candidates : ℕ
  length : ℕ
  height : ℕ
  activeBase : ℕ
  rowsBase : ℕ
  scoresBase : ℕ
  remainingBase : ℕ
  baseBase : ℕ
  active : ℕ → Bool
  rows : ℕ → ℕ → ℕ
  remaining : ℕ → Bool

def instanceSize (x : Inst) : ℕ :=
  x.candidates * x.length + 2 * x.candidates + 2 * x.length

/-- There are at least `x.rounds` flagged candidates, so `x.rounds` restarts
can each find a fresh flagged candidate. -/
def enoughFlags (x : Inst) : Prop :=
  x.rounds ≤ (flagged x.candidates x.remaining).card

/-- The driver's precondition: the round's physical layout and reads, with the
flag memory holding the original mask, and enough flagged candidates. -/
structure Pre (x : Inst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  active_read : ∀ i < x.length, μ (x.activeBase + i) = DenseScorePass.bit (x.active i)
  rows_read : ∀ p < x.candidates, ∀ i < x.length,
    μ (x.rowsBase + p * x.length + i) = x.rows p i
  rows_bound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height
  flags : ∀ p < x.candidates, μ (x.remainingBase + p) = DenseArgminPass.bit (x.remaining p)
  enough : enoughFlags x
  layout : InOrder fr [(x.activeBase, x.length), (x.rowsBase, x.candidates * x.length),
    (x.scoresBase, x.candidates), (x.baseBase, x.length), (x.remainingBase, x.candidates)]

/-- The round's task instance for the current cleared set. -/
def roundInst (x : Inst) (S : Finset ℕ) : DenseCanonicalSelectionRound.Instance where
  candidates := x.candidates
  length := x.length
  height := x.height
  activeBase := x.activeBase
  rowsBase := x.rowsBase
  scoresBase := x.scoresBase
  remainingBase := x.remainingBase
  baseBase := x.baseBase
  active := x.active
  remaining := maskCleared S x.remaining
  rows := x.rows

/-- The arguments of one round call: the nine round registers, free pointer
last. -/
def callArgs : List Expr :=
  [v Candidates, v Len, v Height, v Active, v Rows, v Scores, v Remaining, v Base, v Free]

/-- The unrolled restart loop: `R` rounds, one call each. -/
def loopBody (R : ℕ) : List (Fin R) → Stmt
  | [] => .skip
  | _ :: rest => .call 5 callArgs Tmp ;; loopBody R rest

/-- The round indices the driver runs: `0, …, R-1`. -/
def rounds (R : ℕ) : List (Fin R) := List.finRange R

/-- The driver program: the round's six procedures, then the loop body. -/
def program (x : Inst) : Program :=
  DenseCanonicalSelectionRound.program ++ [loopBody x.rounds (rounds x.rounds)]

/-- One round at the call site: nine argument steps, two call steps, and the
proved round time. -/
def callTime (P I : ℕ) : ℕ := DenseCanonicalSelectionRound.time P I + 11

/-- The driver's total step allowance. -/
def driverTime (x : Inst) : ℕ := x.rounds * callTime x.candidates x.length

/-- The driver's resource need: the round's need, plus one call level. -/
def need (n U : ℕ) : Need :=
  { word := (n + 1) * (U + 1) + 1, cells := 0, depth := 4 }

/-- The driver's need is polynomial. -/
theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

/-- The round procedure is `5`; the loop body is procedure `6` of the driver
program. -/
theorem program_proc (x : Inst) :
    (program x)[6]? = some (loopBody x.rounds (rounds x.rounds)) := by
  have hlen : DenseCanonicalSelectionRound.program.length = 6 := by
    simp [DenseCanonicalSelectionRound.program]
  have hstep : (DenseCanonicalSelectionRound.program ++ [loopBody x.rounds (rounds x.rounds)])[6]? =
      [loopBody x.rounds (rounds x.rounds)][6 - DenseCanonicalSelectionRound.program.length]? :=
    List.getElem?_append_right (by rw [hlen])
  unfold program
  rw [hstep]
  simp [hlen]

/-- The nine-argument cost of one round call site. -/
theorem callArgs_cost : (callArgs.map Expr.cost).sum = 9 := by
  simp [callArgs, Expr.cost]

/-- The driver time unfolds to the round time plus call overhead, per round. -/
theorem driverTime_eq (x : Inst) :
    driverTime x = x.rounds * (22 * x.candidates * x.length + 62 * x.candidates
      + 16 * x.length + 98) := by
  unfold driverTime callTime
  rw [DenseCanonicalSelectionRound.time_eq]

end Light.DenseRestartSelectionLoop

#print axioms Light.DenseRestartSelectionLoop.need_polynomial
#print axioms Light.DenseRestartSelectionLoop.program_proc
#print axioms Light.DenseRestartSelectionLoop.callArgs_cost
#print axioms Light.DenseRestartSelectionLoop.maskCleared_insert
#print axioms Light.DenseRestartSelectionLoop.exists_fresh_flagged
