/-
Copyright (c) 2026. APSP port campaign: L1 physical cache constructor.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the aligned-cache construction whose physical cache
  this program materializes (thin-matrix-results, pin below).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler
  (`Submission/`) this module's programs execute in.
- Joshua Wharton (QFEX) — the checked `LowRowMachine` twelve-procedure backend
  and its `Solves` contracts, on which this caller is built.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L1(b): the physical low-cache constructor

`LowRowMachine.allProgram` contains the twelve checked finite procedures that
materialize one coefficient row each. This module adds the caller that builds
the whole physical cache: twelve sequential procedure calls, writing
`12 * n` coefficient cells at `base + i * n`, driven only by the procedures'
proved `Solves` contracts (`Solves.meets`), so the caller does not depend on
their bodies. The cache region is exactly the block set consumed by the
`rowBlock`-named payloads of `LowCacheRowBlock`.

The execution contract is a genuine `Light.Solves`: every admissible word,
address, and call-depth limit, all appended programs, exact postcondition.
Each call site is twelve argument steps, two call steps, and the proved
`64 * n + 8` body time, so the accounted total is `12 * (64 * n + 22)`.
-/
import Submission.ThreeSumApsp.LowCache.LowRowBlockAgreement
import Submission.ThreeSumApsp.Lang.Calls

namespace Light.LowCacheConstructor

open Light
open ThinMatrix

abbrev Len : ℕ := 0
abbrev Q : ℕ := 1
abbrev SrcA : ℕ := 2
abbrev SrcB : ℕ := 3
abbrev SrcC : ℕ := 4
abbrev SrcD : ℕ := 5
abbrev Base : ℕ := 6
abbrev Free : ℕ := 7
abbrev Tmp : ℕ := 8

/-- The normal/opposite side of cache block `i` (`i < 6` normal, else opposite). -/
def rowNormal (i : Fin 12) : Bool := decide (i.val < 6)

/-- The row of cache block `i`. -/
def rowIdx (i : Fin 12) : Fin 6 := ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩

/-- One cache-construction instance: four source coefficient arrays of shape
`width × q` and a cache region of `12 * n` cells at `base`. -/
structure Inst where
  n : ℕ
  width : ℕ
  q : ℕ
  bound : ℕ
  shape : n = width * q
  src : Fin 4 → ℕ
  base : ℕ
  data : Fin 4 → List Int

/-- The address of cache block `i`. -/
def blockAddr (x : Inst) (i : Fin 12) : ℕ := x.base + i.val * x.n

/-- The erased `rowBlock` payload that cache block `i` must contain. -/
def blockValue (x : Inst) (i : Fin 12) (degree : Fin x.width) (residue : Fin x.q) : Int :=
  SparseLocalForms.denseRead
    (LowCacheRowBlock.rowBlock (rowNormal i) (rowIdx i)
      (fun col => SparseLocalForms.toDense
        (LowRowRefinement.listGrid x.data x.q x.width col)))
    degree residue

/-- The arguments of the cache call: sizes, the four sources, and the base. -/
def argsList (x : Inst) : List ℤ :=
  [x.n, x.q, x.src 0, x.src 1, x.src 2, x.src 3, x.base]

/-- The validity of a cache instance below the free pointer. -/
def Pre (x : Inst) (μ : ℕ → ℤ) (fr : ℕ) : Prop :=
  x.q ≤ x.n ∧
    (∀ col, ArrayAt μ (x.src col) (x.data col) x.n x.bound fr) ∧
    x.base + 12 * x.n ≤ fr ∧
    (∀ col, ∀ i : Fin 12, Apart (x.src col) x.n (blockAddr x i) x.n)

/-- The cache postcondition: the twelve `rowBlock` payloads, nothing else changed. -/
def Post (x : Inst) (μ : ℕ → ℤ) (_fr : ℕ) (_r : ℤ) (μ' : ℕ → ℤ) : Prop :=
  SameOutside μ μ' x.base (12 * x.n) ∧
    ∀ (i : Fin 12) (degree : Fin x.width) (residue : Fin x.q),
      μ' (blockAddr x i + (degree.val * x.q + residue.val)) = blockValue x i degree residue

/-- The cache task: the four source arrays and the `12 * n` cache region. -/
def task : Task where
  Inst := Inst
  size x := x.n
  bound x := x.bound
  args x := argsList x
  Pre x μ fr := Pre x μ fr
  Post x μ _ r μ' := Post x μ x.base r μ'

/-- The arguments of the call that materializes block `i`: the row procedure's
concrete layout, with `dst = base + i * n`. -/
def callArgs (i : Fin 12) : List Expr :=
  [v Len, v Q, v SrcA, v SrcB, v SrcC, v SrcD, v Base +' (k i.val *' v Len), v Free]

/-- The constructor body over a list of block indices: one call each. -/
def ctorBody : List (Fin 12) → Stmt
  | [] => .skip
  | i :: rest => .call i.val (callArgs i) Tmp ;; ctorBody rest

/-- The constructor's own resource need: the row procedures' word bound,
no scratch cells, and one level of calls. -/
def need (_n U : ℕ) : Need :=
  { word := 8 * U + 2 + 16, cells := 0, depth := 1 }

/-- The constructor's need is polynomial. -/
theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

/-- The total step allowance: each call site is twelve argument steps (seven
variable reads, one three-step address expression, one free-pointer read),
two call steps, and the proved `64 * n + 8` body time. -/
def time (n : ℕ) : ℕ := 12 * (64 * n + 22)

/-- The backend's need has no call depth below it. -/
theorem lowNeed_depth (n U : ℕ) : (LowRowMachine.need n U).depth = 0 := rfl

/-- The constructor's own need uses one level of calls. -/
theorem ownNeed_depth (n U : ℕ) : (need n U).depth = 1 := rfl

/-- The procedure index of block `i` in `LowRowMachine.allProgram`. -/
theorem procedureIndex_val (i : Fin 12) :
    LowRowMachine.procedureIndex (rowNormal i) (rowIdx i) = i.val := by
  rcases i with ⟨v, hv⟩
  interval_cases v <;> norm_num [rowNormal, rowIdx, LowRowMachine.procedureIndex]

/-- A cell of the cache region outside all twelve blocks is outside block `i`. -/
private theorem outside_block_of_outside {base n : ℕ} {i : Fin 12} {a : ℕ}
    (ha : Outside base (12 * n) a) : Outside (base + i.val * n) n a := by
  unfold Outside at *
  have hi : i.val * n + n ≤ 12 * n := by
    calc i.val * n + n = (i.val + 1) * n := by ring
      _ ≤ 12 * n := Nat.mul_le_mul_right n (by omega)
  omega

/-- A cell of another block is outside block `i` (blocks are disjoint). -/
private theorem cell_of_other_block {base n o : ℕ} {i j : Fin 12} (hne : i ≠ j)
    (ho : o < n) :
    Outside (base + i.val * n) n (base + j.val * n + o) := by
  unfold Outside
  have hv : i.val ≠ j.val := fun h' => hne (Fin.ext h')
  rcases lt_or_gt_of_ne hv with hlt | hlt
  · right
    have hmul : i.val * n + n ≤ j.val * n := by
      calc i.val * n + n = (i.val + 1) * n := by ring
        _ ≤ j.val * n := Nat.mul_le_mul_right n (by omega)
    omega
  · left
    have hmul : j.val * n + n ≤ i.val * n := by
      calc j.val * n + n = (j.val + 1) * n := by ring
        _ ≤ i.val * n := Nat.mul_le_mul_right n (by omega)
    omega

/-- The body running over any duplicate-free block list writes those blocks and
preserves every earlier-written block and all memory outside the cache. -/
theorem body_ends (l : List (Fin 12)) (hnodup : l.Nodup)
    (S₀ : Finset (Fin 12)) (hdisj : ∀ i ∈ l, i ∉ S₀)
    (x : Inst) {fr : ℕ} (arguments : List ℤ)
    (hloc : ∀ k, k < 8 → arguments.getD k 0 = (argsList x ++ [(fr : ℤ)]).getD k 0)
    (μ : ℕ → ℤ) {lim : Limits} {d : ℕ} {T : ℕ} {Prog : Program}
    (hpre : Pre x μ fr)
    (hok : (need x.n x.bound).Ok lim fr d)
    (hw : ∀ i ∈ S₀, ∀ (degree : Fin x.width) (residue : Fin x.q),
      μ (blockAddr x i + (degree.val * x.q + residue.val)) = blockValue x i degree residue)
    (hT : l.length * (64 * x.n + 22) ≤ T) :
    Ends lim (LowRowMachine.allProgram ++ Prog) d (ctorBody l) ⟨frame arguments, μ⟩ T
      (fun σ => (∀ i ∈ S₀ ∪ l.toFinset, ∀ (degree : Fin x.width) (residue : Fin x.q),
          σ.mem (blockAddr x i + (degree.val * x.q + residue.val)) = blockValue x i degree residue)
        ∧ SameOutside μ σ.mem x.base (12 * x.n)) := by
  induction l generalizing S₀ μ T arguments with
  | nil =>
    refine Ends.skip ?_
    refine ⟨?_, SameOutside.refl⟩
    intro i hi degree residue
    simp only [List.toFinset_nil, Finset.union_empty] at hi
    exact hw i hi degree residue
  | cons i rest ih =>
    obtain ⟨hdisj_i, hnodup_rest⟩ := List.nodup_cons.mp hnodup
    let xi : LowRowMachine.Instance :=
      { n := x.n, q := x.q, bound := x.bound, src := x.src,
        dst := blockAddr x i, data := x.data }
    have hpre_flat : (LowRowMachine.task (rowNormal i) (rowIdx i)).Pre xi μ fr := by
      obtain ⟨hqn, harrays, hbase, hapart⟩ := hpre
      have hdst : blockAddr x i + x.n ≤ fr := by
        have hsh : blockAddr x i + x.n = x.base + (i.val + 1) * x.n := by
          unfold blockAddr; ring
        rw [hsh]
        have hi1 : i.val + 1 ≤ 12 := by omega
        exact (Nat.add_le_add_left (Nat.mul_le_mul_right x.n hi1) x.base).trans hbase
      exact ⟨hqn, harrays, hdst, fun col => hapart col i⟩
    have hok_i : (LowRowMachine.need x.n x.bound).Ok lim fr (d + 1) := by
      have hw8 : ((LowRowMachine.need x.n x.bound).word : ℤ) ≤ lim.word := by
        have h1 := hok.word
        simp only [need] at h1
        show ((8 * x.bound + 2 : ℕ) : ℤ) ≤ lim.word
        push_cast at h1 ⊢
        omega
      refine ⟨hw8, hok.cells, hok.space, ?_⟩
      have hd1 : d + 1 ≤ lim.depth := by
        have h := hok.depth
        rw [ownNeed_depth] at h
        exact h
      rw [lowNeed_depth]
      simpa using hd1
    have hmeets := (LowCacheRowBlock.rowBlockTask_solves (rowNormal i) (rowIdx i)).meets
      Prog { flat := xi, width := x.width, shape := x.shape } (fr := fr) hpre_flat hok_i
    rw [procedureIndex_val] at hmeets
    have hsum : ((callArgs i).map Expr.cost).sum = 12 := by
      simp [callArgs, Expr.cost]
    have hTsplit : rest.length * (64 * x.n + 22) + (64 * x.n + 22) ≤ T := by
      have h0 := hT
      rw [show (i :: rest).length * (64 * x.n + 22) =
          rest.length * (64 * x.n + 22) + (64 * x.n + 22) by
        simp [List.length_cons, Nat.succ_mul]] at h0
      exact h0
    have hone : 64 * x.n + 22 ≤ T := by omega
    have hstep : ((callArgs i).map Expr.cost).sum + 2 + LowRowMachine.time x.n ≤ T := by
      rw [hsum]
      have ht : LowRowMachine.time x.n = 64 * x.n + 8 := rfl
      rw [ht]
      omega
    have hTrest : rest.length * (64 * x.n + 22) ≤ T - (64 * x.n + 22) :=
      Nat.le_sub_of_add_le hTsplit
    have hspace : x.base + 12 * x.n ≤ lim.space := hpre.2.2.1.trans hok.cells
    have hw_dst : ((x.base + i.val * x.n : ℕ) : ℤ) ≤ lim.word := by
      have h1 : ((x.base + i.val * x.n : ℕ) : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast (Nat.add_le_add_left (Nat.mul_le_mul_right x.n (by omega)) x.base).trans hspace
      exact h1.trans hok.space
    have hw_len : ((i.val * x.n : ℕ) : ℤ) ≤ lim.word := by
      have hle : i.val * x.n ≤ x.base + i.val * x.n := Nat.le_add_left _ _
      exact (by exact_mod_cast hle : ((i.val * x.n : ℕ) : ℤ) ≤ ((x.base + i.val * x.n : ℕ) : ℤ)).trans hw_dst
    have hwi : (↑i.val : ℤ) ≤ lim.word := by
      have hw := hok.word
      simp only [need] at hw
      push_cast at hw
      have hi : (↑i.val : ℤ) ≤ 11 := by
        exact_mod_cast (show i.val ≤ 11 by omega)
      omega
    have e0 : frame arguments Len = (x.n : ℤ) := by
      show arguments.getD 0 0 = (x.n : ℤ)
      simpa [argsList] using hloc 0 (by omega)
    have e1 : frame arguments Q = (x.q : ℤ) := by
      show arguments.getD 1 0 = (x.q : ℤ)
      simpa [argsList] using hloc 1 (by omega)
    have e2 : frame arguments SrcA = (x.src 0 : ℤ) := by
      show arguments.getD 2 0 = (x.src 0 : ℤ)
      simpa [argsList] using hloc 2 (by omega)
    have e3 : frame arguments SrcB = (x.src 1 : ℤ) := by
      show arguments.getD 3 0 = (x.src 1 : ℤ)
      simpa [argsList] using hloc 3 (by omega)
    have e4 : frame arguments SrcC = (x.src 2 : ℤ) := by
      show arguments.getD 4 0 = (x.src 2 : ℤ)
      simpa [argsList] using hloc 4 (by omega)
    have e5 : frame arguments SrcD = (x.src 3 : ℤ) := by
      show arguments.getD 5 0 = (x.src 3 : ℤ)
      simpa [argsList] using hloc 5 (by omega)
    have e6 : frame arguments Base = (x.base : ℤ) := by
      show arguments.getD 6 0 = (x.base : ℤ)
      simpa [argsList] using hloc 6 (by omega)
    have e7 : frame arguments Free = (fr : ℤ) := by
      show arguments.getD 7 0 = (fr : ℤ)
      simpa [argsList] using hloc 7 (by omega)
    have hdstcast : ((x.base : ℤ) + (↑i.val * ↑x.n)) = ((x.base + i.val * x.n : ℕ) : ℤ) := by
      push_cast; ring
    refine Ends.callToThen hmeets (fun r μ₁ hpost => ?_)
      (ha := by
        refine ⟨fun e he => ?_, ?_⟩
        · simp only [callArgs, List.mem_cons] at he
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · exact trivial
          · refine ⟨trivial, ⟨hwi, trivial, ?_⟩, ?_⟩
            · simp only [Expr.val, Op.eval, e0]
              rw [show ((↑i.val : ℤ) * (x.n : ℤ)) = ((i.val * x.n : ℕ) : ℤ) by push_cast; ring]
              rw [abs_of_nonneg (by positivity)]
              exact hw_len
            · simp only [Expr.val, Op.eval, e0, e6]
              rw [hdstcast]
              rw [abs_of_nonneg (by positivity)]
              exact hw_dst
          · exact trivial
          · exact absurd h (by simp)
        · have hargsEq : ((LowCacheRowBlock.rowBlockTask (rowNormal i) (rowIdx i)).args
              { flat := xi, width := x.width, shape := x.shape } ++ [(fr : ℤ)]) =
              [(x.n : ℤ), (x.q : ℤ), (x.src 0 : ℤ), (x.src 1 : ℤ), (x.src 2 : ℤ), (x.src 3 : ℤ),
               ((x.base + i.val * x.n : ℕ) : ℤ), (fr : ℤ)] := rfl
          rw [hargsEq]
          simp only [callArgs, List.map_cons, List.map_nil, Expr.val, Op.eval]
          rw [e0, e1, e2, e3, e4, e5, e6, e7, hdstcast])
      (hd := by
        have h := hok_i.depth
        rw [lowNeed_depth] at h
        omega)
      (hT := hstep)
    obtain ⟨hsame_i, hval_i⟩ := hpost
    have hpre₁ : Pre x μ₁ fr := by
      refine ⟨hpre.1, ?_, hpre.2.2.1, hpre.2.2.2⟩
      intro col
      exact ArrayAt.keep (hpre.2.1 col) (hs := by
        intro b hb
        obtain ⟨hins, -⟩ := hb
        refine hsame_i b ?_
        unfold Inside at hins
        unfold Outside
        rcases hpre.2.2.2 col i with h | h
        · exact Or.inl (lt_of_lt_of_le hins.2 h)
        · exact Or.inr (le_trans h hins.1))
    have hloc' : ∀ k, k < 8 →
        (setLocal arguments Tmp r).getD k 0 = (argsList x ++ [(fr : ℤ)]).getD k 0 := by
      intro k hk
      rw [show (setLocal arguments Tmp r).getD k 0 = frame (setLocal arguments Tmp r) k from rfl,
        frame_setLocal]
      have hne : k ≠ Tmp := by simp only [Tmp]; omega
      simp only [hne, if_false]
      exact hloc k hk
    have hdisj' : ∀ j ∈ rest, j ∉ insert i S₀ := by
      intro j hj hjS
      rcases Finset.mem_insert.mp hjS with h | h
      · exact hdisj_i (h ▸ hj)
      · exact hdisj j (List.mem_cons_of_mem i hj) h
    have hw₁ : ∀ j ∈ insert i S₀, ∀ (degree : Fin x.width) (residue : Fin x.q),
        μ₁ (blockAddr x j + (degree.val * x.q + residue.val)) = blockValue x j degree residue := by
      intro j hj degree residue
      rcases Finset.mem_insert.mp hj with h | h
      · subst h
        exact hval_i degree residue
      · have hne : j ≠ i := by
          intro hji
          exact (hdisj i List.mem_cons_self) (hji ▸ h)
        have ho : degree.val * x.q + residue.val < x.n := by
          rw [x.shape]
          have h1 := residue.isLt
          have h2 := degree.isLt
          nlinarith [Nat.zero_le residue.val]
        have hout : Outside (blockAddr x i) x.n
            (blockAddr x j + (degree.val * x.q + residue.val)) :=
          cell_of_other_block (base := x.base) (n := x.n)
            (o := degree.val * x.q + residue.val) (Ne.symm hne) ho
        exact (hsame_i _ hout).trans (hw j h degree residue)
    have hends := ih hnodup_rest (insert i S₀) hdisj'
      (setLocal arguments Tmp r) hloc' μ₁ hpre₁ hw₁ hTrest
    have hbudget : ((callArgs i).map Expr.cost).sum + 2 +
        LowRowMachine.time
          ((LowCacheRowBlock.rowBlockTask (rowNormal i) (rowIdx i)).size
            { flat := xi, width := x.width, shape := x.shape }) = 64 * x.n + 22 := by
      rw [hsum]
      have hsz : (LowCacheRowBlock.rowBlockTask (rowNormal i) (rowIdx i)).size
          { flat := xi, width := x.width, shape := x.shape } = x.n := rfl
      rw [hsz]
      have ht : LowRowMachine.time x.n = 64 * x.n + 8 := rfl
      rw [ht]
      omega
    refine hends.mono (by omega) ?_
    intro σ hσ
    obtain ⟨hvals, hsame_rest⟩ := hσ
    refine ⟨?_, ?_⟩
    · have hset : S₀ ∪ (i :: rest).toFinset = insert i S₀ ∪ rest.toFinset := by
        rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
      intro j hj degree residue
      rw [hset] at hj
      exact hvals j hj degree residue
    · have hsame_union : SameOutside μ μ₁ x.base (12 * x.n) := by
        intro a ha
        exact hsame_i a (outside_block_of_outside ha)
      exact hsame_union.trans hsame_rest

/-- The cache region is exactly `12 * n` cells. -/
theorem twelve_mul {n : ℕ} : 12 * n = n * 12 := Nat.mul_comm 12 n

/-- **The physical cache constructor solves the cache task**, from the twelve
proved row procedures' contracts alone. -/
theorem solves : Solves task
    (LowRowMachine.allProgram ++ [ctorBody (List.finRange 12)]) 12
    (fun n _ => time n) need := by
  refine ⟨ctorBody (List.finRange 12), ?_, ?_⟩
  · -- procedure 12 of the extended program is the constructor body
    have hlen : LowRowMachine.allProgram.length = 12 := by simp [LowRowMachine.allProgram]
    have hstep : (LowRowMachine.allProgram ++ [ctorBody (List.finRange 12)])[12]? =
        [ctorBody (List.finRange 12)][12 - LowRowMachine.allProgram.length]? :=
      List.getElem?_append_right (by rw [hlen])
    rw [hstep]
    simp [hlen]
  · intro R lim d x μ fr hpre hok
    have hT : (List.finRange 12).length * (64 * x.n + 22) ≤ time x.n := by
      simp [time]
    rw [List.append_assoc]
    have hbody := body_ends (Prog := [ctorBody (List.finRange 12)] ++ R)
      (List.finRange 12) (List.nodup_finRange 12) ∅
      (by intro i _ hi; simp at hi) x (argsList x ++ [(fr : ℤ)]) (by intro k _; rfl) μ
      hpre hok (by intro i hi; simp at hi) hT
    refine hbody.mono le_rfl ?_
    intro σ hσ
    obtain ⟨hvals, hsame⟩ := hσ
    refine ⟨hsame, ?_⟩
    intro i degree residue
    have hi : i ∈ (∅ : Finset (Fin 12)) ∪ (List.finRange 12).toFinset := by
      simp
    exact hvals i hi degree residue

/-- The cache constructor's running time is `12 * (64 * n + 22)`. -/
theorem solvedIn : SolvedIn task (fun n _ => 12 * (64 * (n : ℝ) + 22)) := by
  refine ⟨LowRowMachine.allProgram ++ [ctorBody (List.finRange 12)], 12,
    (fun n _ => time n), need, need_polynomial, solves, ?_⟩
  intro n U u hn hU hu
  simp [time]

#print axioms solves
#print axioms solvedIn
#print axioms need_polynomial

end Light.LowCacheConstructor
