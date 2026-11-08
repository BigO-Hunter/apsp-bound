/-
Copyright (c) 2026. APSP port campaign: L2 physical read/write procedures.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the aligned-cache construction; the polynomial query
  cache (`CacheDenseLowering`, thin-matrix-results at the pin) is the
  functional spec of this layer.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler
  (`Submission/`) these procedures execute in.
- Joshua Wharton (QFEX) — the checked low-row backend and constructor
  contracts; the rational retune.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L2(b): the physical cache read/write procedures

The block start `dst` is an argument, exactly as in `LowRowMachine.task`: the
caller (the constructor's layout, then the later layers) knows the block
address, so the address expression is `dst + (degree * q + residue)` and the
`Expr.Safe` obligations reduce to three bounds derived from
`dst + width * q ≤ fr`:

  degree * q ≤ word,  degree * q + residue ≤ word,  dst + (degree*q+residue) ≤ word.

Reads load one cell into the result slot (local 0); writes store one value
argument at the cell. Both are `Solves` over every appended program and every
admissible word/address/call-depth limit, with a constant `64`-step budget.
-/
import Submission.ThreeSumApsp.LowCache.LowCacheOracle

namespace Light.LowCacheOracle

abbrev Dst : ℕ := 0
abbrev Dg : ℕ := 1
abbrev Rs : ℕ := 2
abbrev Qq : ℕ := 3
abbrev Val : ℕ := 4
abbrev Tmp : ℕ := 5

/-- The cell address `dst + (degree * q + residue)`, as a machine expression. -/
def cellExpr : Expr :=
  v Dst +' ((v Dg *' v Qq) +' v Rs)

/-- Read one cache cell into the result slot. -/
def readBody : Stmt := .set Tmp cellExpr ;; .set 0 (M (v Tmp))

/-- Write one cache cell from the value argument. -/
def writeBody : Stmt := .set Tmp cellExpr ;; .store (v Tmp) (v Val)

/-- One read instance: the block start and the addressed cell. -/
structure RInst where
  dst : ℕ
  width : ℕ
  q : ℕ
  bound : ℕ
  degree : Fin width
  residue : Fin q

/-- The addressed cell. -/
def RInst.cell (x : RInst) : ℕ := x.dst + (x.degree.val * x.q + x.residue.val)

/-- The call arguments of a read: block start, degree, residue, modulus. -/
def rArgs (x : RInst) : List ℤ := [x.dst, x.degree.val, x.residue.val, x.q]

/-- The read's resource need. -/
def rNeed (_n U : ℕ) : Need := { word := 8 * U + 2 + 16, cells := 0, depth := 0 }

/-- The read task. -/
def rTask : Task where
  Inst := RInst
  size x := x.width * x.q
  bound x := x.bound
  args x := rArgs x
  Pre x μ fr := x.dst + x.width * x.q ≤ fr ∧ |μ x.cell| ≤ (x.bound : ℤ)
  Post x μ fr r μ' := Kept μ μ' fr ∧ r = μ x.cell

/-- One write instance. -/
structure WInst where
  dst : ℕ
  width : ℕ
  q : ℕ
  bound : ℕ
  degree : Fin width
  residue : Fin q
  val : ℤ

/-- The addressed cell. -/
def WInst.cell (x : WInst) : ℕ := x.dst + (x.degree.val * x.q + x.residue.val)

/-- The call arguments of a write: block start, degree, residue, modulus, value. -/
def wArgs (x : WInst) : List ℤ :=
  [x.dst, x.degree.val, x.residue.val, x.q, x.val]

/-- The write's resource need. -/
def wNeed (_n U : ℕ) : Need := { word := 8 * U + 2 + 16, cells := 0, depth := 0 }

/-- The write task. -/
def wTask : Task where
  Inst := WInst
  size x := x.width * x.q
  bound x := x.bound
  args x := wArgs x
  Pre x μ fr := x.dst + x.width * x.q ≤ fr ∧ |x.val| ≤ (x.bound : ℤ)
  Post x μ _fr _r μ' := μ' = Function.update μ x.cell x.val

/-- The three word bounds of the cell expression, from the block layout. -/
theorem cell_bounds {dst w q fr d r : ℕ} {lim : Limits}
    (hbase : dst + w * q ≤ fr) (hfr : fr ≤ lim.space)
    (hs : (lim.space : ℤ) ≤ lim.word) (hd : d < w) (hr : r < q) :
    (↑d : ℤ) * ↑q ≤ (lim.word : ℤ) ∧
      (↑d : ℤ) * ↑q + ↑r ≤ (lim.word : ℤ) ∧
      (↑dst : ℤ) + ((↑d : ℤ) * ↑q + ↑r) ≤ (lim.word : ℤ) := by
  have hdq : d * q ≤ w * q := by
    calc d * q ≤ (d + 1) * q := by rw [Nat.succ_mul]; omega
      _ ≤ w * q := Nat.mul_le_mul_right q (by omega)
  have hoff : d * q + r < w * q := by
    calc d * q + r < d * q + q := Nat.add_lt_add_left hr _
      _ = (d + 1) * q := by ring
      _ ≤ w * q := Nat.mul_le_mul_right q (by omega)
  have hw : w * q ≤ dst + w * q := Nat.le_add_left _ _
  have hsp : (dst + w * q : ℕ) ≤ lim.space := le_trans hbase hfr
  refine ⟨?_, ?_, ?_⟩
  · calc (↑d : ℤ) * ↑q = (↑(d * q) : ℤ) := by push_cast; ring
      _ ≤ (lim.space : ℤ) := by exact_mod_cast le_trans hdq (le_trans hw hsp)
      _ ≤ lim.word := hs
  · calc (↑d : ℤ) * ↑q + ↑r = (↑(d * q + r) : ℤ) := by push_cast; ring
      _ ≤ (lim.space : ℤ) := by exact_mod_cast le_trans hoff.le (le_trans hw hsp)
      _ ≤ lim.word := hs
  · calc (↑dst : ℤ) + ((↑d : ℤ) * ↑q + ↑r) = (↑(dst + (d * q + r)) : ℤ) := by push_cast; ring
      _ ≤ (lim.space : ℤ) := by
          have h2 : dst + (d * q + r) < dst + w * q := Nat.add_lt_add_left hoff dst
          exact_mod_cast h2.le.trans hsp
      _ ≤ lim.word := hs

/-- The cell of a read instance lies below the space bound. -/
theorem rcell_lt {x : RInst} {fr : ℕ} {lim : Limits}
    (hbase : x.dst + x.width * x.q ≤ fr) (hfr : fr ≤ lim.space) :
    x.cell < lim.space := by
  have hoff : x.degree.val * x.q + x.residue.val < x.width * x.q :=
    offset_lt_len { base := x.dst, width := x.width, q := x.q } x.degree x.residue
  have h2 : x.dst + (x.degree.val * x.q + x.residue.val) < x.dst + x.width * x.q :=
    Nat.add_lt_add_left hoff x.dst
  show x.dst + (x.degree.val * x.q + x.residue.val) < lim.space
  exact lt_of_lt_of_le h2 (hbase.trans hfr)

/-- The cell of a write instance lies below the space bound. -/
theorem wcell_lt {x : WInst} {fr : ℕ} {lim : Limits}
    (hbase : x.dst + x.width * x.q ≤ fr) (hfr : fr ≤ lim.space) :
    x.cell < lim.space := by
  have hoff : x.degree.val * x.q + x.residue.val < x.width * x.q :=
    offset_lt_len { base := x.dst, width := x.width, q := x.q } x.degree x.residue
  have h2 : x.dst + (x.degree.val * x.q + x.residue.val) < x.dst + x.width * x.q :=
    Nat.add_lt_add_left hoff x.dst
  show x.dst + (x.degree.val * x.q + x.residue.val) < lim.space
  exact lt_of_lt_of_le h2 (hbase.trans hfr)

/-- The read procedure's body ends with the cell value in local 0. -/
theorem read_ends (x : RInst) {μ : ℕ → ℤ} {fr : ℕ} {lim : Limits} {d : ℕ} {P : Program}
    (hpre : rTask.Pre x μ fr) (hok : (rNeed (x.width * x.q) x.bound).Ok lim fr d) :
    Ends lim P d readBody ⟨frame (rArgs x ++ [(fr : ℤ)]), μ⟩ 64
      (fun σ' => rTask.Post x μ fr (σ'.loc 0) σ'.mem) := by
  have hfr : fr ≤ lim.space := by
    have h := hok.cells
    simpa [rNeed] using h
  have hcell := rcell_lt (x := x) hpre.1 hfr
  obtain ⟨hb1, hb2, hb3⟩ := cell_bounds (dst := x.dst) (w := x.width) (q := x.q)
    hpre.1 hfr hok.space x.degree.isLt x.residue.isLt
  -- the frame values, evaluated
  have e0 : frame (rArgs x ++ [(fr : ℤ)]) Dst = (↑x.dst : ℤ) := by simp [frame, rArgs, Dst]
  have e1 : frame (rArgs x ++ [(fr : ℤ)]) Dg = (↑x.degree.val : ℤ) := by
    simp [frame, rArgs, Dg]
  have e2 : frame (rArgs x ++ [(fr : ℤ)]) Rs = (↑x.residue.val : ℤ) := by
    simp [frame, rArgs, Rs]
  have e3 : frame (rArgs x ++ [(fr : ℤ)]) Qq = (↑x.q : ℤ) := by simp [frame, rArgs, Qq]
  -- the safety of the address expression, by hand
  have hs1 : (cellExpr).Safe lim ⟨frame (rArgs x ++ [(fr : ℤ)]), μ⟩ := by
    simp only [cellExpr, Expr.Safe, Expr.val, Op.eval]
    refine ⟨trivial, ⟨⟨trivial, trivial, ?_⟩, trivial, ?_⟩, ?_⟩
    · rw [e1, e3, abs_of_nonneg (by positivity)]
      exact hb1
    · rw [e1, e3, e2, abs_of_nonneg (by positivity)]
      exact hb2
    · rw [e0, e1, e3, e2, abs_of_nonneg (by positivity)]
      exact hb3
  -- the value of the address expression
  have hval : (cellExpr).val ⟨frame (rArgs x ++ [(fr : ℤ)]), μ⟩ = ((x.cell : ℕ) : ℤ) := by
    simp only [cellExpr, Expr.val, Op.eval]
    rw [e0, e1, e3, e2]
    show (↑x.dst : ℤ) + ((↑x.degree.val : ℤ) * ↑x.q + ↑x.residue.val) =
      ((x.dst + (x.degree.val * x.q + x.residue.val) : ℕ) : ℤ)
    push_cast; ring
  unfold readBody
  refine Ends.setThen ?_ hs1 (by light_time [cellExpr])
  rw [hval]
  refine Ends.setLast ?_ ?_ (by light_time [cellExpr])
  · refine ⟨SameOn.refl, ?_⟩
    show (Function.update (Function.update (frame (rArgs x ++ [(fr : ℤ)])) Tmp
      ((x.cell : ℕ) : ℤ)) 0 (μ ((↑x.cell : ℤ).toNat))) 0 = μ x.cell
    rw [Function.update_self]
    rw [show ((x.cell : ℕ) : ℤ).toNat = x.cell from Int.toNat_natCast x.cell]
  · refine ⟨trivial, ?_⟩
    refine ⟨?_, ?_⟩
    · simp only [Expr.val]
      rw [Function.update_self]
      exact Int.natCast_nonneg _
    · simp only [Expr.val]
      rw [Function.update_self]
      exact_mod_cast hcell

/-- The read procedure solves the read task. -/
theorem read_solves (x : RInst)
    {lim : Limits} {d : ℕ} {P : Program} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : rTask.Pre x μ fr) (hok : (rNeed (x.width * x.q) x.bound).Ok lim fr d) :
    Ends lim P d readBody ⟨frame (rArgs x ++ [(fr : ℤ)]), μ⟩ 64
      (fun σ' => rTask.Post x μ fr (σ'.loc 0) σ'.mem) :=
  read_ends x hpre hok

/-- The read task is solved in `64` steps. -/
theorem read_solvedIn : SolvedIn rTask (fun _ _ => 64) := by
  refine ⟨[readBody], 0, (fun _ _ => 64), rNeed, ?_, ?_, ?_⟩
  · unfold rNeed; poly_need []
  · refine ⟨readBody, rfl, ?_⟩
    intro R lim d x μ fr hpre hok
    exact read_ends x hpre (by simpa [rNeed, rTask] using hok)
  · intro n U u hn hU hu; norm_num

/-- The write procedure's body ends having stored the value at the cell. -/
theorem write_ends (x : WInst) {μ : ℕ → ℤ} {fr : ℕ} {lim : Limits} {d : ℕ} {P : Program}
    (hpre : wTask.Pre x μ fr) (hok : (wNeed (x.width * x.q) x.bound).Ok lim fr d) :
    Ends lim P d writeBody ⟨frame (wArgs x ++ [(fr : ℤ)]), μ⟩ 64
      (fun σ' => wTask.Post x μ fr (σ'.loc 0) σ'.mem) := by
  have hfr : fr ≤ lim.space := by
    have h := hok.cells
    simpa [wNeed] using h
  have hcell := wcell_lt (x := x) hpre.1 hfr
  obtain ⟨hb1, hb2, hb3⟩ := cell_bounds (dst := x.dst) (w := x.width) (q := x.q)
    hpre.1 hfr hok.space x.degree.isLt x.residue.isLt
  have e0 : frame (wArgs x ++ [(fr : ℤ)]) Dst = (↑x.dst : ℤ) := by simp [frame, wArgs, Dst]
  have e1 : frame (wArgs x ++ [(fr : ℤ)]) Dg = (↑x.degree.val : ℤ) := by
    simp [frame, wArgs, Dg]
  have e2 : frame (wArgs x ++ [(fr : ℤ)]) Rs = (↑x.residue.val : ℤ) := by
    simp [frame, wArgs, Rs]
  have e3 : frame (wArgs x ++ [(fr : ℤ)]) Qq = (↑x.q : ℤ) := by simp [frame, wArgs, Qq]
  have hs1 : (cellExpr).Safe lim ⟨frame (wArgs x ++ [(fr : ℤ)]), μ⟩ := by
    simp only [cellExpr, Expr.Safe, Expr.val, Op.eval]
    refine ⟨trivial, ⟨⟨trivial, trivial, ?_⟩, trivial, ?_⟩, ?_⟩
    · rw [e1, e3, abs_of_nonneg (by positivity)]
      exact hb1
    · rw [e1, e3, e2, abs_of_nonneg (by positivity)]
      exact hb2
    · rw [e0, e1, e3, e2, abs_of_nonneg (by positivity)]
      exact hb3
  have hval : (cellExpr).val ⟨frame (wArgs x ++ [(fr : ℤ)]), μ⟩ = ((x.cell : ℕ) : ℤ) := by
    simp only [cellExpr, Expr.val, Op.eval]
    rw [e0, e1, e3, e2]
    show (↑x.dst : ℤ) + ((↑x.degree.val : ℤ) * ↑x.q + ↑x.residue.val) =
      ((x.dst + (x.degree.val * x.q + x.residue.val) : ℕ) : ℤ)
    push_cast; ring
  unfold writeBody
  refine Ends.setThen ?_ hs1 (by light_time [cellExpr])
  rw [hval]
  refine Ends.storeLast ?_ ?_ (by light_time [cellExpr])
  · show Function.update μ ((↑x.cell : ℤ).toNat) ((↑x.val : ℤ)) =
      Function.update μ x.cell x.val
    rw [show ((x.cell : ℕ) : ℤ).toNat = x.cell from Int.toNat_natCast x.cell]
  · refine ⟨trivial, trivial, ?_⟩
    refine ⟨?_, ?_⟩
    · simp only [Expr.val]
      rw [Function.update_self]
      exact Int.natCast_nonneg _
    · simp only [Expr.val]
      rw [Function.update_self]
      exact_mod_cast hcell

/-- The write task is solved in `64` steps. -/
theorem write_solvedIn : SolvedIn wTask (fun _ _ => 64) := by
  refine ⟨[writeBody], 0, (fun _ _ => 64), wNeed, ?_, ?_, ?_⟩
  · unfold wNeed; poly_need []
  · refine ⟨writeBody, rfl, ?_⟩
    intro R lim d x μ fr hpre hok
    exact write_ends x hpre (by simpa [wNeed, wTask] using hok)
  · intro n U u hn hU hu; norm_num

#print axioms cell_bounds
#print axioms rcell_lt
#print axioms read_solvedIn
#print axioms write_solvedIn

end Light.LowCacheOracle
