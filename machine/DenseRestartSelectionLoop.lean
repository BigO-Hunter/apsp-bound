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
flag memory holding the mask cleared by `S` so far, and enough flagged
candidates. -/
structure Pre (x : Inst) (S : Finset ℕ) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  active_read : ∀ i < x.length, μ (x.activeBase + i) = DenseScorePass.bit (x.active i)
  rows_read : ∀ p < x.candidates, ∀ i < x.length,
    μ (x.rowsBase + p * x.length + i) = x.rows p i
  rows_bound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height
  flags : ∀ p < x.candidates,
    μ (x.remainingBase + p) = DenseArgminPass.bit (maskCleared S x.remaining p)
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

/-! ## The restart loop's execution contract -/

/-- The driver's eight round arguments. -/
def argsOf (x : Inst) : List ℤ :=
  [x.candidates, x.length, x.height, x.activeBase, x.rowsBase, x.scoresBase,
    x.remainingBase, x.baseBase]

/-- A round instance's task arguments are the driver's argument list. -/
theorem roundInst_args (x : Inst) (S : Finset ℕ) :
    DenseCanonicalSelectionRound.task.args (roundInst x S) = argsOf x := rfl

/-- The active-array cells lie strictly below the scores region, hence outside
all three written regions. -/
private theorem outside_trio {ab rb sb mb rem P I i : ℕ}
    (hAR : ab + I ≤ rb) (hRS : rb + P * I ≤ sb) (hSM : sb + P ≤ mb)
    (hMR : mb + I ≤ rem) (hi : i < I) :
    Outside sb P (ab + i) ∧ Outside mb I (ab + i) ∧ Outside rem P (ab + i) := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;> omega

/-- The rows cells lie strictly below the scores region, hence outside all
three written regions. -/
private theorem outside_trio_rows {rb sb mb rem P I i p : ℕ}
    (hRS : rb + P * I ≤ sb) (hSM : sb + P ≤ mb) (hMR : mb + I ≤ rem)
    (hp : p < P) (hi : i < I) :
    Outside sb P (rb + p * I + i) ∧ Outside mb I (rb + p * I + i) ∧
      Outside rem P (rb + p * I + i) := by
  have hbound : p * I + i < P * I := by nlinarith
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;> omega

/-- The body running over any round list writes the chosen list, clears
exactly those flags, writes the scores and the last selected row, preserves
everything outside the three written regions, and certifies each round's
argmin over the mask before that round. -/
theorem loop_ends (x : Inst) (l : List (Fin x.rounds))
    (S₀ : Finset ℕ) (hcard : S₀.card + l.length = x.rounds)
    (hsub : S₀ ⊆ flagged x.candidates x.remaining)
    {fr : ℕ} (arguments : List ℤ)
    (hloc : ∀ k, k < 9 → arguments.getD k 0 = (argsOf x ++ [(fr : ℤ)]).getD k 0)
    (μ : ℕ → ℤ) {lim : Limits} {d : ℕ} {T : ℕ} {Prog : Program}
    (hpre : Pre x S₀ μ fr)
    (hok : (need (instanceSize x) x.height).Ok lim fr d)
    (hT : l.length * callTime x.candidates x.length ≤ T) :
    Ends lim (program x ++ Prog) d (loopBody x.rounds l)
      ⟨frame arguments, μ⟩ T
      fun σ => ∃ cs : List ℕ, cs.length = l.length ∧ cs.Nodup ∧
        (∀ c ∈ cs, c < x.candidates ∧ x.remaining c = true ∧ c ∉ S₀) ∧
        (∀ p < x.candidates,
          σ.mem (x.remainingBase + p) =
            DenseArgminPass.bit (maskCleared (S₀ ∪ cs.toFinset) x.remaining p)) ∧
        SameOutside3 μ σ.mem x.scoresBase x.candidates x.baseBase x.length
          x.remainingBase x.candidates ∧
        (l.length = 0 → σ.mem = μ) ∧
        (0 < l.length → ∃ c, cs.getLast? = some c ∧
          (∀ i < x.length, σ.mem (x.baseBase + i) = x.rows c i) ∧
          (∀ p < x.candidates,
            σ.mem (x.scoresBase + p) =
              (DenseScoreTablePass.scores x.active x.rows x.length p : ℤ)) ∧
          (∀ k, k < cs.length →
            DenseArgminPass.IsArgmin
              (maskCleared (S₀ ∪ (cs.take k).toFinset) x.remaining)
              (DenseScoreTablePass.scores x.active x.rows x.length) x.candidates
              (cs.getD k 0))) := by
  induction l generalizing S₀ μ T arguments with
  | nil =>
    refine Ends.skip ⟨[], rfl, List.nodup_nil, (fun c hc => nomatch hc), ?_, SameOn.refl,
      fun _ => rfl, fun h0 => absurd h0 (by simp)⟩
    · intro p hp
      show μ (x.remainingBase + p) = _
      rw [hpre.flags p hp]
      congr 1
      simp [maskCleared]
  | cons j rest ih =>
    obtain ⟨hAR, hRS, hSM, hMR, hend⟩ := hpre.layout
    obtain ⟨hqn, harrays, hbound, hfl, henough, hlay⟩ := hpre
    -- resource facts shared with the round's own contract
    have hn : x.length ≤ instanceSize x := by unfold instanceSize; omega
    have hheight : x.height ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by nlinarith
    have hsum : x.length * x.height + 1 ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by
      nlinarith
    have hone : 1 ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by omega
    have hw' : (((instanceSize x + 1) * (x.height + 1) + 1 : ℕ) : ℤ) ≤ lim.word := hok.word
    have h1 : 1 ≤ lim.word :=
      (by exact_mod_cast hone : (1 : ℤ) ≤ _).trans hw'
    have hh : (x.height : ℤ) ≤ lim.word :=
      (by exact_mod_cast hheight : (x.height : ℤ) ≤ _).trans hw'
    have hsent : ((x.length * x.height + 1 : ℕ) : ℤ) ≤ lim.word :=
      (by exact_mod_cast hsum : ((x.length * x.height + 1 : ℕ) : ℤ) ≤ _).trans hw'
    have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
    have hd4 : d + 4 ≤ lim.depth := by
      have := hok.depth
      simpa only [need] using this
    -- a fresh flagged candidate exists for this round
    have h1c : S₀.card + (rest.length + 1) = x.rounds := by
      simpa [List.length_cons] using hcard
    have hcardle : S₀.card = x.rounds - (rest.length + 1) := by omega
    have hposF : x.rounds - (rest.length + 1) < (flagged x.candidates x.remaining).card := by
      have h2 := henough
      simp only [enoughFlags] at h2
      omega
    obtain ⟨chosen, hchP, hchrem, hchS₀⟩ :=
      exists_fresh_flagged hsub hcardle hposF
    have hmaskchosen : maskCleared S₀ x.remaining chosen = true := by
      simp [maskCleared, hchrem, hchS₀]
    -- the round's tight-time contract, in the appended program
    have hmeets : Meets lim
        (DenseCanonicalSelectionRound.program ++
          ([loopBody x.rounds (rounds x.rounds)] ++ Prog)) 5 (d + 1)
        (argsOf x ++ [(fr : ℤ)]) μ
        (DenseCanonicalSelectionRound.time x.candidates x.length)
        (DenseCanonicalSelectionRound.task.Post (roundInst x S₀) μ fr) :=
      Meets.of_body
        (getElem?_append_of_eq_some
          (show DenseCanonicalSelectionRound.program[5]? =
            some (DenseCanonicalSelectionRound.body 3 4) from rfl) _)
        (DenseCanonicalSelectionRound.ends
          (getElem?_append_of_eq_some
            (show DenseCanonicalSelectionRound.program[3]? =
              some (DenseScoreTablePass.Selection.body 1 2) from rfl) _)
          (getElem?_append_of_eq_some
            (show DenseCanonicalSelectionRound.program[1]? =
              some (DenseScoreTablePass.body 0) from rfl) _)
          (getElem?_append_of_eq_some
            (show DenseCanonicalSelectionRound.program[0]? =
              some DenseScorePass.body from rfl) _)
          (getElem?_append_of_eq_some
            (show DenseCanonicalSelectionRound.program[2]? =
              some DenseArgminPass.body from rfl) _)
          (getElem?_append_of_eq_some
            (show DenseCanonicalSelectionRound.program[4]? =
              some copyBody from rfl) _)
          hqn harrays hbound hfl ⟨chosen, hchP, hmaskchosen⟩
          hok.space h1 hh hsent ⟨hAR, hRS, hSM, hMR, hend.trans hfr⟩ hfr
          (by omega))
    -- time accounting
    have hct : callTime x.candidates x.length =
        DenseCanonicalSelectionRound.time x.candidates x.length + 11 := rfl
    have hTexp : rest.length * callTime x.candidates x.length +
        callTime x.candidates x.length ≤ T := by
      have h := hT
      rw [List.length_cons, Nat.succ_mul] at h
      exact h
    have hsplit : rest.length * callTime x.candidates x.length +
        (callArgs.map Expr.cost).sum + 2 +
        DenseCanonicalSelectionRound.time x.candidates x.length ≤ T := by
      rw [callArgs_cost]
      omega
    have hTrest : rest.length * callTime x.candidates x.length ≤
        T - ((callArgs.map Expr.cost).sum + 2 +
          DenseCanonicalSelectionRound.time x.candidates x.length) := by
      omega
    -- the nine argument expressions evaluate to the round's frame
    have e0 : frame arguments Candidates = (x.candidates : ℤ) := by
      show arguments.getD 0 0 = _
      simpa [argsOf] using hloc 0 (by omega)
    have e1 : frame arguments Len = (x.length : ℤ) := by
      show arguments.getD 1 0 = _
      simpa [argsOf] using hloc 1 (by omega)
    have e2 : frame arguments Height = (x.height : ℤ) := by
      show arguments.getD 2 0 = _
      simpa [argsOf] using hloc 2 (by omega)
    have e3 : frame arguments Active = (x.activeBase : ℤ) := by
      show arguments.getD 3 0 = _
      simpa [argsOf] using hloc 3 (by omega)
    have e4 : frame arguments Rows = (x.rowsBase : ℤ) := by
      show arguments.getD 4 0 = _
      simpa [argsOf] using hloc 4 (by omega)
    have e5 : frame arguments Scores = (x.scoresBase : ℤ) := by
      show arguments.getD 5 0 = _
      simpa [argsOf] using hloc 5 (by omega)
    have e6 : frame arguments Remaining = (x.remainingBase : ℤ) := by
      show arguments.getD 6 0 = _
      simpa [argsOf] using hloc 6 (by omega)
    have e7 : frame arguments Base = (x.baseBase : ℤ) := by
      show arguments.getD 7 0 = _
      simpa [argsOf] using hloc 7 (by omega)
    have e8 : frame arguments Free = (fr : ℤ) := by
      show arguments.getD 8 0 = _
      simpa [argsOf] using hloc 8 (by omega)
    unfold program
    rw [List.append_assoc]
    simp only [loopBody]
    refine Ends.callToThen hmeets (fun r μ₁ hpost => ?_)
      (ha := by
        refine ⟨fun e he => ?_, ?_⟩
        · simp only [callArgs, List.mem_cons] at he
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact absurd h (by simp)
        · have hvals : argsOf x ++ [(fr : ℤ)] =
              [(x.candidates : ℤ), (x.length : ℤ), (x.height : ℤ), (x.activeBase : ℤ),
                (x.rowsBase : ℤ), (x.scoresBase : ℤ), (x.remainingBase : ℤ),
                (x.baseBase : ℤ), (fr : ℤ)] := rfl
          rw [hvals]
          simp only [callArgs, List.map_cons, List.map_nil, Expr.val]
          rw [e0, e1, e2, e3, e4, e5, e6, e7, e8])
      (hd := by omega) (hT := by omega)
    obtain ⟨hsame₁, hscores₁, chosen', hrch, harg, hcopy, hflags₁⟩ := hpost
    have hargP : chosen' < x.candidates := harg.1
    have hargsplit : x.remaining chosen' = true ∧ chosen' ∉ S₀ := by
      have h : maskCleared S₀ x.remaining chosen' = true := harg.2.1
      simp only [maskCleared, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, by simpa using h.2⟩
    have hargx : DenseArgminPass.IsArgmin (maskCleared S₀ x.remaining)
        (DenseScoreTablePass.scores x.active x.rows x.length) x.candidates chosen' := harg
    -- the round's flag write clears exactly the chosen candidate
    have hflags₁' : ∀ p < x.candidates,
        μ₁ (x.remainingBase + p) =
          DenseArgminPass.bit (maskCleared (insert chosen' S₀) x.remaining p) := by
      intro p hp
      rw [show μ₁ (x.remainingBase + p) =
        μ₁ ((roundInst x S₀).remainingBase + p) from rfl, hflags₁ p hp]
      simp only [roundInst]
      by_cases hp' : p = chosen'
      · subst hp'
        simp [maskCleared]
      · have hmem : decide (p ∈ insert chosen' S₀) = decide (p ∈ S₀) := by
          simp only [Finset.mem_insert, hp', false_or]
        rw [if_neg hp']
        simp only [maskCleared, hmem]
    -- the round preserves the reads
    have hpre₁ : Pre x (insert chosen' S₀) μ₁ fr := by
      refine ⟨?_, ?_, hbound, hflags₁', henough, ⟨hAR, hRS, hSM, hMR, hend⟩⟩
      · intro i hi
        exact (hsame₁ _ (outside_trio hAR hRS hSM hMR hi)).trans (hqn i hi)
      · intro p hp i hi
        exact (hsame₁ _ (outside_trio_rows hRS hSM hMR hp hi)).trans (harrays p hp i hi)
    -- induction hypotheses
    have hcard₁ : (insert chosen' S₀).card + rest.length = x.rounds := by
      have h1i : (insert chosen' S₀).card = S₀.card + 1 :=
        Finset.card_insert_of_notMem hargsplit.2
      omega
    have hsub₁ : insert chosen' S₀ ⊆ flagged x.candidates x.remaining := by
      intro c hc
      simp only [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · simp [flagged, Finset.mem_filter, Finset.mem_range, hargP, hargsplit.1]
      · exact hsub hc
    have hloc₁ : ∀ k, k < 9 →
        (setLocal arguments Tmp r).getD k 0 = (argsOf x ++ [(fr : ℤ)]).getD k 0 := by
      intro k hk
      rw [show (setLocal arguments Tmp r).getD k 0 =
        frame (setLocal arguments Tmp r) k from rfl, frame_setLocal]
      have hne : k ≠ Tmp := by simp only [Tmp]; omega
      simp only [hne, if_false]
      exact hloc k hk
    have hends := ih (insert chosen' S₀) hcard₁ hsub₁ (setLocal arguments Tmp r) hloc₁
      μ₁ hpre₁ hTrest
    refine hends.mono (by omega) ?_
    intro σ hσ
    obtain ⟨cs, hcslen, hcsnodup, hcselem, hflags₂, hsame₂, hskip, hguard⟩ := hσ
    have hchcs : chosen' ∉ cs := fun hmem =>
      (hcselem chosen' hmem).2.2 (Finset.mem_insert_self chosen' S₀)
    refine ⟨chosen' :: cs, ?_, List.nodup_cons.mpr ⟨hchcs, hcsnodup⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, hcslen]
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨hargP, hargsplit.1, hargsplit.2⟩
      · exact ⟨(hcselem c hc).1, (hcselem c hc).2.1,
          fun hmem => (hcselem c hc).2.2 (Finset.mem_insert_of_mem hmem)⟩
    · intro p hp
      rw [hflags₂ p hp]
      congr 1
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    · exact hsame₁.trans hsame₂
    · intro h0
      omega
    · intro hpos
      by_cases hrest : rest = []
      · subst hrest
        have hcsempty : cs = [] := by
          have hz : cs.length = 0 := by rw [hcslen]; rfl
          cases cs
          · rfl
          · exact absurd hz (by simp)
        subst hcsempty
        have hσμ : σ.mem = μ₁ := hskip rfl
        refine ⟨chosen', ?_, ?_, ?_, ?_⟩
        · simp
        · intro i hi
          rw [hσμ]
          exact hcopy i hi
        · intro p hp
          rw [hσμ]
          exact hscores₁ p hp
        · intro k hk
          have hk1 : k < 1 := by simpa using hk
          have hk0 : k = 0 := by omega
          subst hk0
          simpa [List.take_zero, Finset.union_empty] using hargx
      · by_cases hcsempty : cs = []
        · have hz : (0 : ℕ) = cs.length := by rw [hcsempty]; rfl
          have h0 : rest.length = 0 := by omega
          exact absurd (List.length_eq_zero_iff.mp h0) hrest
        · obtain ⟨c, hcget, hbase, hscoresf, hchain⟩ :=
            hguard (List.length_pos_of_ne_nil hrest)
          refine ⟨c, ?_, hbase, hscoresf, ?_⟩
          · simp [List.getLast?_cons, hcget]
          · intro k hk
            rcases Nat.eq_zero_or_pos k with rfl | hk0
            · simpa [List.take_zero, Finset.union_empty] using hargx
            · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0)
              have hm : m < cs.length := by simp only [List.length_cons] at hk; omega
              have hseteq : (S₀ ∪ ((chosen' :: cs).take (m + 1)).toFinset)
                  = (insert chosen' S₀ ∪ (cs.take m).toFinset) := by
                simp [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
              have hchainm := hchain m hm
              rw [hseteq]
              simpa [List.getD_cons_succ] using hchainm

/-- The loop's total step allowance against a polynomial clock: each round
is at most `time P I + 11`, at most `P <= instanceSize` rounds fit, and
`time P I <= 100 * instanceSize + 87`.  This is the piece the L5 caller
instantiates once its call site pins the instance sizes. -/
theorem driverTime_le (x : Inst) (hrounds : x.rounds <= x.candidates) :
    driverTime x <= x.rounds * (100 * instanceSize x + 98) := by
  have hP : x.candidates <= instanceSize x := by unfold instanceSize; omega
  have hI : x.length <= instanceSize x := by unfold instanceSize; omega
  have hPI : x.candidates * x.length <= instanceSize x := by unfold instanceSize; omega
  have htime : DenseCanonicalSelectionRound.time x.candidates x.length
      <= 100 * instanceSize x + 87 := by
    rw [DenseCanonicalSelectionRound.time_eq]
    nlinarith [hP, hI, hPI]
  have hdriv := driverTime_eq x
  nlinarith [htime, hP, hI, hPI, hdriv]

/-! ## L5: the pinned call site and its statements

A `Solves` contract carries ONE fixed program, but the restart unrolling is
instance-sized (`loopBody x.rounds` over the finRange round list).  The
min-plus caller (`mpTask`-matching) therefore pins the instance sizes
`(P, R)` at its call site: upstream this is `stage`'s
`greedy O active primes k 1 remaining blockSizes []` — `R := k` restarts
over the `P`-sized candidate pool, with the greedy premise
`k ≤ (pool primes remaining).card` supplying `enoughFlags`.
`pinnedTask` fixes the pinned instance, so `program x` is one fixed
program and the Task/Solves/SolvedIn triple closes at the pinned `(P, R)`.

The deferred `Post`/take-vs-erase refinement: `Post` packages the
`loop_ends` conclusion at `S₀ = ∅` over the full round list, keeping the
**take** form — the mask before round `k` is `maskCleared (cs.take k)
.toFinset`, exactly the shape `loop_ends` exposes.  The erase form
(suffix-erased masks) carries the same information and adds nothing; it is
not used. -/

/-- The flagged-pool cardinality never exceeds the pool size: the greedy
caller's `k ≤ (pool primes remaining).card` premise bounds the restart count
by `P`. -/
theorem flagged_card_le (P : ℕ) (remaining : ℕ → Bool) :
    (flagged P remaining).card ≤ P := by
  have hsub : flagged P remaining ⊆ Finset.range P := by
    intro a ha
    simp only [flagged, Finset.mem_filter, Finset.mem_range] at ha
    exact Finset.mem_range.mpr ha.1
  calc (flagged P remaining).card ≤ (Finset.range P).card := Finset.card_le_card hsub
    _ = P := Finset.card_range P

/-- With nothing cleared yet, `maskCleared` is the plain remaining mask: the
flag memory the caller starts from. -/
theorem maskCleared_empty (remaining : ℕ → Bool) (p : ℕ) :
    maskCleared ∅ remaining p = remaining p := by
  simp [maskCleared]

/-- The restart-loop driver's result at the pinned call site: the chosen list
of all `x.rounds` restarts, packaged from the `loop_ends` conclusion at
`S₀ = ∅` (the take form is kept; see the section note). -/
def Post (x : Inst) (μ : ℕ → ℤ) (μ' : ℕ → ℤ) : Prop :=
  ∃ cs : List ℕ, cs.length = x.rounds ∧ cs.Nodup ∧
    (∀ c ∈ cs, c < x.candidates ∧ x.remaining c = true) ∧
    (∀ p < x.candidates,
      μ' (x.remainingBase + p) =
        DenseArgminPass.bit (maskCleared cs.toFinset x.remaining p)) ∧
    SameOutside3 μ μ' x.scoresBase x.candidates x.baseBase x.length
      x.remainingBase x.candidates ∧
    (x.rounds = 0 → μ' = μ) ∧
    (0 < x.rounds → ∃ c, cs.getLast? = some c ∧
      (∀ i < x.length, μ' (x.baseBase + i) = x.rows c i) ∧
      (∀ p < x.candidates,
        μ' (x.scoresBase + p) =
          (DenseScoreTablePass.scores x.active x.rows x.length p : ℤ)) ∧
      (∀ k, k < cs.length →
        DenseArgminPass.IsArgmin
          (maskCleared (cs.take k).toFinset x.remaining)
          (DenseScoreTablePass.scores x.active x.rows x.length) x.candidates
          (cs.getD k 0)))

/-- The pinned call-site task: the instance is pinned to `x`, so the driver
program `program x` is one fixed program.  `Pre` carries the plain flag
memory (nothing cleared yet), the round's physical layout and reads, and
`enoughFlags` — the greedy premise `k ≤ pool.card`. -/
def pinnedTask (x : Inst) : Task where
  Inst := { y : Inst // y = x }
  size y := instanceSize y.1
  bound y := y.1.height
  args y := argsOf y.1
  Pre y μ fr := Pre y.1 ∅ μ fr
  Post y μ _fr _r μ' := Post y.1 μ μ'

/-- The pinned clock: at the call site the restart count is pinned, and
`driverTime_le` unfolds the allowance into a polynomial of the instance size
— the shape the L5 caller's task-clock carries. -/
def taskTime (n _U : ℕ) : ℕ := 100 * n * n + 98 * n

/-- The pinned call site of the greedy controller: `P` candidates, `R`
restarts, incidence length `I`, row bound `h`, the fixed active mask, the
plain remaining mask, the row table, and the five ordered regions.  Upstream
this is `stage`'s `greedy O active primes k 1 remaining blockSizes []`. -/
def callSite (P R I h : ℕ) (active remaining : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (ab rb sb mb bb : ℕ) : Inst where
  rounds := R
  candidates := P
  length := I
  height := h
  activeBase := ab
  rowsBase := rb
  scoresBase := sb
  remainingBase := mb
  baseBase := bb
  active := active
  rows := rows
  remaining := remaining

/-- The greedy premise pins `enoughFlags` at the call site:
`R ≤ (flagged P remaining).card`. -/
theorem callSite_enough (P R I h : ℕ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (ab rb sb mb bb : ℕ)
    (hR : R ≤ (flagged P remaining).card) :
    enoughFlags (callSite P R I h active remaining rows ab rb sb mb bb) := hR

/-- The caller's physical premises — the plain flag memory included —
assemble into the pinned task premise at the call site. -/
theorem pre_of_reads {x : Inst} {μ : ℕ → ℤ} {fr : ℕ}
    (hAR : ∀ i < x.length, μ (x.activeBase + i) = DenseScorePass.bit (x.active i))
    (hRR : ∀ p < x.candidates, ∀ i < x.length,
      μ (x.rowsBase + p * x.length + i) = x.rows p i)
    (hbound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height)
    (hfl : ∀ p < x.candidates,
      μ (x.remainingBase + p) = DenseArgminPass.bit (x.remaining p))
    (hR : x.rounds ≤ (flagged x.candidates x.remaining).card)
    (hlay : InOrder fr [(x.activeBase, x.length), (x.rowsBase, x.candidates * x.length),
      (x.scoresBase, x.candidates), (x.baseBase, x.length),
      (x.remainingBase, x.candidates)]) :
    Pre x ∅ μ fr := by
  refine ⟨hAR, hRR, hbound, ?_, hR, hlay⟩
  intro p hp
  rw [maskCleared_empty]
  exact hfl p hp

/-- The pinned clock dominates the driver's step allowance at every call
site: `R ≤ P` restarts, each within the round's instance-sized bound. -/
theorem taskTime_ge (x : Inst) (hrounds : x.rounds ≤ x.candidates) :
    driverTime x ≤ taskTime (instanceSize x) x.height := by
  have h1 := driverTime_le x hrounds
  have hP : x.candidates ≤ instanceSize x := by unfold instanceSize; omega
  unfold taskTime
  nlinarith

end Light.DenseRestartSelectionLoop

#print axioms Light.DenseRestartSelectionLoop.need_polynomial
#print axioms Light.DenseRestartSelectionLoop.program_proc
#print axioms Light.DenseRestartSelectionLoop.callArgs_cost
#print axioms Light.DenseRestartSelectionLoop.maskCleared_insert
#print axioms Light.DenseRestartSelectionLoop.exists_fresh_flagged
#print axioms Light.DenseRestartSelectionLoop.loop_ends
#print axioms Light.DenseRestartSelectionLoop.driverTime_le
#print axioms Light.DenseRestartSelectionLoop.flagged_card_le
#print axioms Light.DenseRestartSelectionLoop.maskCleared_empty
#print axioms Light.DenseRestartSelectionLoop.pre_of_reads
#print axioms Light.DenseRestartSelectionLoop.taskTime_ge
#print axioms Light.DenseRestartSelectionLoop.callSite_enough
