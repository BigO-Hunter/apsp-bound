import Submission.ThreeSumApsp.LowCache.LowRowSemantics
import Submission.ThreeSumApsp.LowCache.ThinMatrix.SparseLocalForms

/-!
# Operational refinement of the actual upstream sparse local row

Author: Joshua Wharton, QFEX, joshua@qfex.com.

`SparseLocalForms` is the byte-identical file from upstream commit
225c37476e31bdb27594953cc1f7738496fb4afc. Its four dependencies are
transparently vendored with narrowed imports and one explicit equality-
transport proof adaptation. Their mathematical definitions and theorem statements
are unchanged; the integrity manifest and complete patch record this.

This file connects the existing checked Light program to the imported
`ThinMatrix.SparseLocalForms.localRow`, its materialized `denseLocalRow`,
and its actual scalar-site counter. It does not replace those definitions.
-/

namespace Light.LowRowRefinement

open ThinMatrix

theorem coefficient_rom_eq (normal : Bool) (row : Fin 6) (col : Fin 4) :
    LowRowMachine.coefficients normal row col =
      SparseLocalForms.rowCoefficients normal row col := by
  cases normal <;> rfl

theorem shift_predicate_eq (normal : Bool) (row : Fin 6) (col : Fin 4) :
    SparseLocalForms.shifted normal row col =
      (LowRowMachine.shiftsThird normal row && decide (col = 2)) := by
  cases normal <;> by_cases hr : row = 4 <;> by_cases hc : col = 2 <;>
    simp [SparseLocalForms.shifted, LowRowMachine.shiftsThird, hr, hc]

/-- The upstream finite sum is exactly the arithmetic expression executed
by the machine, with the upstream previous-degree read still explicit. -/
theorem localRow_as_combine {q width : Nat} (normal : Bool) (row : Fin 6)
    (children : Fin 4 → SparseLocalForms.CoeffVector q width)
    (degree : Fin width) (residue : Fin q) :
    SparseLocalForms.localRow normal row children degree residue =
      LowRowMachine.combine normal row
        (children 0 degree residue) (children 1 degree residue)
        (if LowRowMachine.shiftsThird normal row then
          if h : 0 < degree.val then
            children 2 ⟨degree.val - 1, by omega⟩ residue
          else 0
         else children 2 degree residue)
        (children 3 degree residue) := by
  simp [SparseLocalForms.localRow, LowRowMachine.combine, Fin.sum_univ_succ,
    ← coefficient_rom_eq, SparseLocalForms.readCell, shift_predicate_eq, add_assoc]

theorem thirdRead_flatten_pos (normal : Bool) (row : Fin 6) (μ : Nat → Int)
    (base q degree residue : Nat) (hr : residue < q) :
    LowRowMachine.thirdRead normal row μ base q (degree * q + residue) =
      if LowRowMachine.shiftsThird normal row then
        if 0 < degree then μ (base + ((degree - 1) * q + residue)) else 0
      else μ (base + (degree * q + residue)) := by
  rw [LowRowMachine.thirdRead_flatten normal row μ base q degree residue hr]
  by_cases hd : degree = 0
  · simp [hd]
  · have hp : 0 < degree := Nat.pos_of_ne_zero hd
    simp [hd, hp]

/-- The actual physical input words, viewed in the upstream coefficient grid. -/
def memoryGrid (μ : Nat → Int) (src : Fin 4 → Nat) (q width : Nat) :
    Fin 4 → SparseLocalForms.CoeffVector q width :=
  fun col degree residue => μ (src col + (degree.val * q + residue.val))

/-- The task's input lists, viewed in the same upstream coefficient grid. -/
def listGrid (data : Fin 4 → List Int) (q width : Nat) :
    Fin 4 → SparseLocalForms.CoeffVector q width :=
  fun col degree residue => (data col).getD (degree.val * q + residue.val) 0

/-- The machine's memory expression equals the imported upstream row at
every degree and residue, including the first auxiliary degree. -/
theorem output_eq_localRow {q width : Nat} (normal : Bool) (row : Fin 6)
    (μ : Nat → Int) (src : Fin 4 → Nat) (degree : Fin width) (residue : Fin q) :
    LowRowMachine.output normal row μ (src 0) (src 1) (src 2) (src 3) q
        (degree.val * q + residue.val) =
      SparseLocalForms.localRow normal row (memoryGrid μ src q width) degree residue := by
  rw [localRow_as_combine]
  unfold LowRowMachine.output
  dsimp only [memoryGrid]
  rw [thirdRead_flatten_pos normal row μ (src 2) q degree.val residue.val residue.isLt]
  simp only [dite_eq_ite]

/-- The list-based postcondition of the checked machine has exactly the
upstream local-row meaning. This lemma needs no extra memory premise. -/
theorem rowValue_eq_localRow (normal : Bool) (row : Fin 6)
    (x : LowRowMachine.Instance) (width : Nat)
    (degree : Fin width) (residue : Fin x.q) :
    LowRowMachine.rowValue normal row x (degree.val * x.q + residue.val) =
      SparseLocalForms.localRow normal row (listGrid x.data x.q width) degree residue := by
  rw [localRow_as_combine]
  unfold LowRowMachine.rowValue
  dsimp only [listGrid]
  congr 1
  simpa only [LowRowMachine.thirdRead, Nat.zero_add, dite_eq_ite] using
    thirdRead_flatten_pos normal row (fun i => (x.data 2).getD i 0)
      0 x.q degree.val residue.val residue.isLt

theorem flatten_lt {q width : Nat} (degree : Fin width) (residue : Fin q) :
    degree.val * q + residue.val < width * q := by
  calc
    degree.val * q + residue.val < degree.val * q + q := Nat.add_lt_add_left residue.isLt _
    _ = (degree.val + 1) * q := by ring
    _ ≤ width * q := Nat.mul_le_mul_right q degree.isLt

/-- The upstream materialization has the same exact coefficient values. -/
theorem output_eq_denseLocalRow {q width : Nat} (normal : Bool) (row : Fin 6)
    (μ : Nat → Int) (src : Fin 4 → Nat) (degree : Fin width) (residue : Fin q) :
    LowRowMachine.output normal row μ (src 0) (src 1) (src 2) (src 3) q
        (degree.val * q + residue.val) =
      SparseLocalForms.denseRead
        (SparseLocalForms.denseLocalRow normal row
          (fun col => SparseLocalForms.toDense (memoryGrid μ src q width col))) degree residue := by
  rw [SparseLocalForms.denseLocalRow_correct]
  simpa only [SparseLocalForms.denseRead_toDense] using
    output_eq_localRow normal row μ src degree residue

/-- A physical coefficient-array task with an explicit rectangular shape.
`shape` is an input-layout fact, not a correctness or execution premise. -/
structure GridInstance where
  flat : LowRowMachine.Instance
  width : Nat
  shape : flat.n = width * flat.q

/-- The postcondition names the preserved upstream definition itself. -/
def task (normal : Bool) (row : Fin 6) : Task where
  Inst := GridInstance
  size x := x.flat.n
  bound x := x.flat.bound
  args x := (LowRowMachine.task normal row).args x.flat
  Pre x μ fr := (LowRowMachine.task normal row).Pre x.flat μ fr
  Post x μ _ _ μ' := SameOutside μ μ' x.flat.dst x.flat.n ∧
    ∀ (degree : Fin x.width) (residue : Fin x.flat.q),
      μ' (x.flat.dst + (degree.val * x.flat.q + residue.val)) =
        SparseLocalForms.localRow normal row (listGrid x.flat.data x.flat.q x.width) degree residue

/-- This is the actual `Solves` execution contract for the upstream local
row, obtained by refining the postcondition of the existing finite code. -/
theorem solves_in (normal : Bool) (row : Fin 6) {P : Program} {p : Nat}
    (hp : P[p]? = some (LowRowMachine.body normal row)) :
    Solves (task normal row) P p (fun n _ => LowRowMachine.time n) LowRowMachine.need := by
  obtain ⟨code, hcode, hbody⟩ := LowRowMachine.solves_in normal row hp
  refine ⟨code, hcode, ?_⟩
  intro R lim depth x μ fr hpre hok
  have hrun := hbody R lim depth x.flat μ fr hpre hok
  refine hrun.mono le_rfl ?_
  intro σ hpost
  obtain ⟨houtside, hvalues⟩ := hpost
  refine ⟨houtside, ?_⟩
  intro degree residue
  have hi : degree.val * x.flat.q + residue.val < x.flat.n := by
    rw [x.shape]
    exact flatten_lt degree residue
  exact (hvalues _ hi).trans (rowValue_eq_localRow normal row x.flat x.width degree residue)

theorem solves (normal : Bool) (row : Fin 6) :
    Solves (task normal row) (LowRowMachine.program normal row) 0
      (fun n _ => LowRowMachine.time n) LowRowMachine.need :=
  solves_in normal row rfl

theorem allProgram_solves (normal : Bool) (row : Fin 6) :
    Solves (task normal row) LowRowMachine.allProgram (LowRowMachine.procedureIndex normal row)
      (fun n _ => LowRowMachine.time n) LowRowMachine.need :=
  solves_in normal row (LowRowMachine.procedure_in_allProgram normal row)

theorem solvedIn (normal : Bool) (row : Fin 6) :
    SolvedIn (task normal row) (fun n _ => 64 * (n : Real) + 8) := by
  refine ⟨LowRowMachine.program normal row, 0, (fun n _ => LowRowMachine.time n),
    LowRowMachine.need, LowRowMachine.need_polynomial, solves normal row, ?_⟩
  intro n U u hn hU hu
  norm_num [LowRowMachine.time]

/-- A proved comparison with the imported upstream counter, using actual
Light execution time on the left. No counter-to-execution premise is used. -/
theorem time_le_materializeScalarCost (q width : Nat) (normal : Bool) (row : Fin 6) :
    LowRowMachine.time (width * q) ≤
      5 * SparseLocalForms.materializeScalarCost q width normal row + 8 := by
  rw [SparseLocalForms.materializeScalarCost_eq]
  exact LowRowMachine.ledger_overhead q width

#print axioms output_eq_localRow
#print axioms output_eq_denseLocalRow
#print axioms solves
#print axioms allProgram_solves
#print axioms solvedIn
#print axioms time_le_materializeScalarCost

end Light.LowRowRefinement
