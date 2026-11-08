import Submission.ThreeSumApsp.Lang.Lib.Pass
import Submission.ThreeSumApsp.Lang.Lib.ArrayAt
import Submission.ThreeSumApsp.Lang.PolyBounded
import Submission.ThreeSumApsp.Lang.Tactics
import Mathlib.Tactic.FinCases

/-!
# Actual Light execution of the low-cache local rows

Author: Joshua Wharton, QFEX, joshua@qfex.com.

The twelve finite routines below materialize one complete coefficient row
of the normal/opposite low-cache encoder. The normal fifth row reads the
third child one auxiliary degree earlier, and writes zero for that child's
contribution in degree zero. Each input is a flat array of `width * q`
integer words. All four inputs may alias each other; the output is disjoint.

The proof concerns `Light.Ends` and its actual finite imperative syntax.
The time bound includes loop control, address arithmetic, every read, every
integer arithmetic operation, and every output store. This is one backend
component, not a whole equality oracle or APSP solver.
-/

namespace Light.LowRowMachine

abbrev Len : Nat := 0
abbrev Residues : Nat := 1
abbrev SrcA : Nat := 2
abbrev SrcB : Nat := 3
abbrev SrcC : Nat := 4
abbrev SrcD : Nat := 5
abbrev Dst : Nat := 6
abbrev Free : Nat := 7
abbrev Idx : Nat := 8

/-- The coefficient ROM agrees with the six sparse cache forms. -/
def coefficients (normal : Bool) (row : Fin 6) : Fin 4 → Int :=
  if normal then
    (![![1, 0, 1, 1], ![1, 0, 1, 0], ![0, 1, 0, -1],
       ![0, 1, 0, 0], ![-1, -1, 1, 0], ![0, 0, 0, 1]] : Fin 6 → Fin 4 → Int) row
  else
    (![![1, 1, 0, 0], ![1, -1, 0, 0], ![1, 1, -1, 0],
       ![1, -1, 1, 0], ![2, 0, 0, 0], ![0, 0, 1, 0]] : Fin 6 → Fin 4 → Int) row

def shiftsThird (normal : Bool) (row : Fin 6) : Bool := normal && decide (row = 4)

theorem coefficient_bound (normal : Bool) (row : Fin 6) (col : Fin 4) :
    |coefficients normal row col| ≤ 2 := by
  cases normal <;> fin_cases row <;> fin_cases col <;> norm_num [coefficients]

def combine (normal : Bool) (row : Fin 6) (a b c d : Int) : Int :=
  coefficients normal row 0 * a + coefficients normal row 1 * b +
    coefficients normal row 2 * c + coefficients normal row 3 * d

def thirdRead (normal : Bool) (row : Fin 6) (μ : Nat → Int) (c q i : Nat) : Int :=
  if shiftsThird normal row then
    if i < q then 0 else μ (c + (i - q))
  else μ (c + i)

def output (normal : Bool) (row : Fin 6) (μ : Nat → Int) (a b c d q i : Nat) : Int :=
  combine normal row (μ (a + i)) (μ (b + i))
    (thirdRead normal row μ c q i) (μ (d + i))

/-- Signed literals are built from the language's natural literals and an
actual subtraction; negative values are not extra syntax or free operations. -/
def signedLiteral (z : Int) : Expr := k z.toNat -' k (-z).toNat

@[simp] theorem signedLiteral_val (z : Int) (σ : State) :
    (signedLiteral z).val σ = z := by
  simp [signedLiteral]

@[simp] theorem signedLiteral_cost (z : Int) : (signedLiteral z).cost = 3 := rfl

/-- A fixed arithmetic expression with four reads and four constant scales. -/
def valueExpr (normal : Bool) (row : Fin 6) (third : Expr) : Expr :=
  ((signedLiteral (coefficients normal row 0) *' M (v SrcA +' v Idx)) +'
    (signedLiteral (coefficients normal row 1) *' M (v SrcB +' v Idx))) +'
    (signedLiteral (coefficients normal row 2) *' third) +'
    (signedLiteral (coefficients normal row 3) *' M (v SrcD +' v Idx))

/-- The branch is present only in the normal H(z) routine. -/
def roundBody (normal : Bool) (row : Fin 6) : Stmt :=
  if shiftsThird normal row then
    .ite (v Idx <' v Residues)
      (.store (v Dst +' v Idx) (valueExpr normal row (k 0)))
      (.store (v Dst +' v Idx)
        (valueExpr normal row (M (v SrcC +' (v Idx -' v Residues)))))
  else
    .store (v Dst +' v Idx) (valueExpr normal row (M (v SrcC +' v Idx)))

def body (normal : Bool) (row : Fin 6) : Stmt :=
  .for Idx (v Len) (roundBody normal row)

def time (n : Nat) : Nat := 64 * n + 8

theorem round_cost (normal : Bool) (row : Fin 6) :
    (roundBody normal row).blockCost ≤ 56 := by
  unfold roundBody
  split <;> simp [valueExpr, signedLiteral, Stmt.blockCost, Expr.cost, Cond.cost]

private theorem scaled_bounds (normal : Bool) (row : Fin 6) (a b c d U : Int)
    (_hU : 0 ≤ U) (ha : |a| ≤ U) (hb : |b| ≤ U) (hc : |c| ≤ U) (hd : |d| ≤ U) :
    |coefficients normal row 0 * a| ≤ 2 * U ∧
    |coefficients normal row 1 * b| ≤ 2 * U ∧
    |coefficients normal row 2 * c| ≤ 2 * U ∧
    |coefficients normal row 3 * d| ≤ 2 * U ∧
    |coefficients normal row 0 * a + coefficients normal row 1 * b| ≤ 4 * U ∧
    |coefficients normal row 0 * a + coefficients normal row 1 * b +
      coefficients normal row 2 * c| ≤ 6 * U ∧
    |combine normal row a b c d| ≤ 8 * U := by
  have hscale (col : Fin 4) (z : Int) (hz : |z| ≤ U) :
      |coefficients normal row col * z| ≤ 2 * U := by
    rw [abs_mul]
    exact mul_le_mul (coefficient_bound normal row col) hz (abs_nonneg _) (by omega)
  have h0 := hscale 0 a ha
  have h1 := hscale 1 b hb
  have h2 := hscale 2 c hc
  have h3 := hscale 3 d hd
  have h01 := (abs_add_le (coefficients normal row 0 * a)
    (coefficients normal row 1 * b)).trans (add_le_add h0 h1)
  have h012 := (abs_add_le (coefficients normal row 0 * a + coefficients normal row 1 * b)
    (coefficients normal row 2 * c)).trans (add_le_add h01 h2)
  have h0123 := (abs_add_le
    (coefficients normal row 0 * a + coefficients normal row 1 * b + coefficients normal row 2 * c)
    (coefficients normal row 3 * d)).trans (add_le_add h012 h3)
  exact ⟨h0, h1, h2, h3, by omega, by omega, by unfold combine; omega⟩

/-- Whole-array execution with explicit word, address, and separation facts. -/
theorem ends (normal : Bool) (row : Fin 6)
    {lim : Limits} {P : Program} {depth : Nat} {μ : Nat → Int}
    {n q a b c d dst fr : Nat} {U : Int}
    (hU : 0 ≤ U) (hq : q ≤ n)
    (hw : (lim.space : Int) ≤ lim.word) (hword : 8 * U + 2 ≤ lim.word)
    (ha : a + n ≤ lim.space) (hb : b + n ≤ lim.space)
    (hc : c + n ≤ lim.space) (hd : d + n ≤ lim.space)
    (hdst : dst + n ≤ lim.space)
    (hsepA : Apart a n dst n) (hsepB : Apart b n dst n)
    (hsepC : Apart c n dst n) (hsepD : Apart d n dst n)
    (hA : ∀ i < n, |μ (a + i)| ≤ U) (hB : ∀ i < n, |μ (b + i)| ≤ U)
    (hC : ∀ i < n, |μ (c + i)| ≤ U) (hD : ∀ i < n, |μ (d + i)| ≤ U) :
    Ends lim P depth (body normal row) ⟨frame [n, q, a, b, c, d, dst, fr], μ⟩ (time n)
      fun σ => σ.mem = wrote μ dst (output normal row μ a b c d q) n := by
  unfold body
  refine Ends.forFrame
    (fun j μ' => μ' = wrote μ dst (output normal row μ a b c d q) j)
    n wrote_zero.symm ?round ?done
    (hn := by omega) (hT := by have ht := round_cost normal row; simp [time]; nlinarith)
  case round =>
    intro j μ' hj hμ
    have readA (i : Nat) (hi : i < n) : μ' (a + i) = μ (a + i) := by
      rw [hμ, wrote_rest (by rcases hsepA with h | h <;> omega)]
    have readB (i : Nat) (hi : i < n) : μ' (b + i) = μ (b + i) := by
      rw [hμ, wrote_rest (by rcases hsepB with h | h <;> omega)]
    have readC (i : Nat) (hi : i < n) : μ' (c + i) = μ (c + i) := by
      rw [hμ, wrote_rest (by rcases hsepC with h | h <;> omega)]
    have readD (i : Nat) (hi : i < n) : μ' (d + i) = μ (d + i) := by
      rw [hμ, wrote_rest (by rcases hsepD with h | h <;> omega)]
    have hnext : Function.update μ' (dst + j) (output normal row μ a b c d q j) =
        wrote μ dst (output normal row μ a b c d q) (j + 1) := by
      rw [hμ]
      exact wrote_succ
    have h0 := coefficient_bound normal row 0
    have h1 := coefficient_bound normal row 1
    have h2 := coefficient_bound normal row 2
    have h3 := coefficient_bound normal row 3
    simp only [abs_le] at h0 h1 h2 h3
    have ha' := hA j hj
    have hb' := hB j hj
    have hd' := hD j hj
    have ra := readA j hj
    have rb := readB j hj
    have rd := readD j hj
    unfold roundBody
    split
    next hs =>
      refine Ends.iteLast (fun hjq => ?_) (fun hjq => ?_) (by light_side)
      · have hjq' : j < q := by simpa using hjq
        have hout : output normal row μ a b c d q j =
            combine normal row (μ (a + j)) (μ (b + j)) 0 (μ (d + j)) := by
          simp [output, thirdRead, hs, hjq']
        obtain ⟨h0v, h1v, h2v, h3v, h01v, h012v, houtv⟩ :=
          scaled_bounds normal row (μ (a + j)) (μ (b + j)) 0 (μ (d + j)) U
            hU ha' hb' (by simpa using hU) hd'
        simp only [combine, mul_zero, add_zero, abs_le] at h0v h1v h2v h3v h01v h012v houtv
        light_store (dst + j) (output normal row μ a b c d q j)
          using valueExpr, signedLiteral, Int.toNat_sub_toNat_neg, combine, hout, ra, rb, rd
        exact ⟨rfl, hnext⟩
      · have hjq' : q ≤ j := by
          have hn : ¬ j < q := by simpa using hjq
          omega
        have hsub : j - q < n := by omega
        have rc := readC (j - q) hsub
        have hc' := hC (j - q) hsub
        have hcast : (j : Int) - q = (j - q : Nat) := by omega
        have hout : output normal row μ a b c d q j =
            combine normal row (μ (a + j)) (μ (b + j)) (μ (c + (j - q))) (μ (d + j)) := by
          simp [output, thirdRead, hs, Nat.not_lt.mpr hjq']
        obtain ⟨h0v, h1v, h2v, h3v, h01v, h012v, houtv⟩ :=
          scaled_bounds normal row (μ (a + j)) (μ (b + j)) (μ (c + (j - q)))
            (μ (d + j)) U hU ha' hb' hc' hd'
        simp only [combine, abs_le] at h0v h1v h2v h3v h01v h012v houtv
        light_store (dst + j) (output normal row μ a b c d q j)
          using valueExpr, signedLiteral, Int.toNat_sub_toNat_neg, combine, hout, ra, rb, rc, rd, hcast
        exact ⟨rfl, hnext⟩
    next hs =>
      have rc := readC j hj
      have hc' := hC j hj
      have hout : output normal row μ a b c d q j =
          combine normal row (μ (a + j)) (μ (b + j)) (μ (c + j)) (μ (d + j)) := by
        simp [output, thirdRead, hs]
      obtain ⟨h0v, h1v, h2v, h3v, h01v, h012v, houtv⟩ :=
        scaled_bounds normal row (μ (a + j)) (μ (b + j)) (μ (c + j)) (μ (d + j)) U
          hU ha' hb' hc' hd'
      simp only [combine, abs_le] at h0v h1v h2v h3v h01v h012v houtv
      light_store (dst + j) (output normal row μ a b c d q j)
        using valueExpr, signedLiteral, Int.toNat_sub_toNat_neg, combine, hout, ra, rb, rc, rd
      exact ⟨rfl, hnext⟩
  case done =>
    intro μ' hμ
    exact hμ

/-- One physical row-materialization instance; its output buffer is supplied
by the caller and is charged in the layout precondition. -/
structure Instance where
  n : Nat
  q : Nat
  bound : Nat
  src : Fin 4 → Nat
  dst : Nat
  data : Fin 4 → List Int

def rowValue (normal : Bool) (row : Fin 6) (x : Instance) (i : Nat) : Int :=
  combine normal row ((x.data 0).getD i 0) ((x.data 1).getD i 0)
    (if shiftsThird normal row then
      if i < x.q then 0 else (x.data 2).getD (i - x.q) 0
     else (x.data 2).getD i 0)
    ((x.data 3).getD i 0)

def task (normal : Bool) (row : Fin 6) : Task where
  Inst := Instance
  size x := x.n
  bound x := x.bound
  args x := [x.n, x.q, x.src 0, x.src 1, x.src 2, x.src 3, x.dst]
  Pre x μ fr := x.q ≤ x.n ∧
    (∀ col, ArrayAt μ (x.src col) (x.data col) x.n x.bound fr) ∧
    x.dst + x.n ≤ fr ∧ ∀ col, Apart (x.src col) x.n x.dst x.n
  Post x μ _ _ μ' := SameOutside μ μ' x.dst x.n ∧
    ∀ i < x.n, μ' (x.dst + i) = rowValue normal row x i

def need (_n U : Nat) : Need where
  word := 8 * U + 2
  cells := 0
  depth := 0

def program (normal : Bool) (row : Fin 6) : Program := [body normal row]

/-- A closed specification of an actual finite procedure, stable under all
appended procedures. No execution or cost-domination premise is assumed. -/
theorem solves_in (normal : Bool) (row : Fin 6) {P : Program} {p : Nat}
    (hp : P[p]? = some (body normal row)) :
    Solves (task normal row) P p (fun n _ => time n) need := by
  refine ⟨body normal row, hp, ?_⟩
  intro R lim depth x μ fr hpre hok
  obtain ⟨hq, harrays, hdst, hsep⟩ := hpre
  have hfr : fr ≤ lim.space := by simpa [need] using hok.cells
  have hword : 8 * (x.bound : Int) + 2 ≤ lim.word := by
    simpa [need, task] using hok.word
  have he := ends normal row (P := P ++ R) (depth := depth) (fr := fr)
    (Nat.cast_nonneg x.bound) hq hok.space hword
    ((harrays 0).below.trans hfr) ((harrays 1).below.trans hfr)
    ((harrays 2).below.trans hfr) ((harrays 3).below.trans hfr) (hdst.trans hfr)
    (hsep 0) (hsep 1) (hsep 2) (hsep 3)
    (fun i hi => (harrays 0).abs_read_le hi) (fun i hi => (harrays 1).abs_read_le hi)
    (fun i hi => (harrays 2).abs_read_le hi) (fun i hi => (harrays 3).abs_read_le hi)
  change Ends lim (P ++ R) depth (body normal row)
    ⟨frame [x.n, x.q, x.src 0, x.src 1, x.src 2, x.src 3, x.dst, fr], μ⟩ (time x.n) _
  refine he.mono le_rfl ?_
  intro σ hσ
  change SameOutside μ σ.mem x.dst x.n ∧ _
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro i hi
  rw [wrote_done hi]
  unfold output rowValue
  rw [(harrays 0).read hi, (harrays 1).read hi, (harrays 3).read hi]
  congr 1
  unfold thirdRead
  split
  · split
    · rfl
    · exact (harrays 2).read (by omega)
  · exact (harrays 2).read hi

theorem solves (normal : Bool) (row : Fin 6) :
    Solves (task normal row) (program normal row) 0 (fun n _ => time n) need :=
  solves_in normal row rfl

/-- All twelve procedures in one fixed finite program, independent of all
input dimensions, memory addresses, and coefficient values. -/
def allProgram : Program :=
  List.ofFn fun i : Fin 12 =>
    body (decide (i.val < 6)) ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩

def procedureIndex (normal : Bool) (row : Fin 6) : Nat :=
  if normal then row.val else 6 + row.val

theorem procedure_in_allProgram (normal : Bool) (row : Fin 6) :
    allProgram[procedureIndex normal row]? = some (body normal row) := by
  cases normal <;> fin_cases row <;> rfl

theorem allProgram_solves (normal : Bool) (row : Fin 6) :
    Solves (task normal row) allProgram (procedureIndex normal row)
      (fun n _ => time n) need :=
  solves_in normal row (procedure_in_allProgram normal row)

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn (normal : Bool) (row : Fin 6) :
    SolvedIn (task normal row) (fun n _ => 64 * (n : Real) + 8) := by
  refine ⟨program normal row, 0, (fun n _ => time n), need,
    need_polynomial, solves normal row, ?_⟩
  intro n U u hn hU hu
  norm_num [time]

/-- The target language overhead is a fixed factor of the existing 14-site
local-row ledger, including its additive loop cost. -/
theorem ledger_overhead (q width : Nat) :
    time (width * q) ≤ 5 * (14 * q * width) + 8 := by
  unfold time
  nlinarith

#print axioms solves
#print axioms allProgram_solves
#print axioms need_polynomial
#print axioms solvedIn
#print axioms ledger_overhead

end Light.LowRowMachine
