/-
Copyright (c) 2026. APSP port campaign: L1 row↔cache integration.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the target construction: aligned Walsh embedding,
  polynomial query cache, composite-incidence reduction. `BinaryLowEncoder.rowBlock`
  is ported from thin-matrix-results at 225c37476e31bdb27594953cc1f7738496fb4afc.
- Josh Alman and Virginia Vassilevska Williams — source paper, arXiv:2610.06783.
- Li Xuanji — the verified ten-term batched construction and the word-RAM
  compiler implemented by the `Submission/` tree this module lands in.
- Joshua Wharton (QFEX) — the checked `LowRowMachine` / `LowRowRefinement`
  components and the rational retune; those proofs are ported unmodified here.
- Hrishik Sai Bojnal — the verified frontier this work refines.

# L1: the physical low-row programs are `BinaryLowEncoder.rowBlock` payloads

`Submission.ThreeSumApsp.LowCache.LowRowMachine` proves twelve finite Light
procedures (`Light.Solves`, actual executions) that materialize the six normal
and six opposite low-cache coefficient rows. `LowRowRefinement` proves each
physical output equals `ThinMatrix.SparseLocalForms.localRow`.

`BinaryLowEncoder.rowBlock` at the shresh pin is a *charged* functional block:
`abbrev Block (q width : ℕ) := Vector (Vector Cell q) width`, and the checked
upstream theorem `BinaryLowEncoder.rowBlock_view` states

    payloadView (rowBlock normal row children)
      = SparseLocalForms.denseLocalRow normal row (fun c => blockView (children c)).

This module lands the ℤ-erasure of that interface in the board tree — the
binary `Cell` layer (bounded-word arithmetic) is L3 work — and states the named
refinement: for every normal/opposite row, the physical Light output equals the
erased `rowBlock` payload at every degree and residue. The erasure is faithful
by construction: `blockView` maps every `BinaryCell` to `BinaryCell.view`, and
`rowBlock_view` identifies the resulting vector with `denseLocalRow`.
-/
import Submission.ThreeSumApsp.LowCache.LowRowRefinement

namespace Light.LowCacheRowBlock

open Light
open ThinMatrix

/-- ℤ-erasure of `BinaryLowEncoder.Block` (shresh pin 225c37476): the block
payload after `BinaryCell.view` is applied to every cell. This is
`SparseLocalForms.DenseVector`, the type `BinaryLowEncoder.blockView` returns. -/
abbrev BlockPayload (q width : ℕ) := SparseLocalForms.DenseVector q width

/-- ℤ-erasure of `BinaryLowEncoder.rowBlock`. The upstream checked theorem
`BinaryLowEncoder.rowBlock_view` proves the charged block's `payloadView` is
exactly `SparseLocalForms.denseLocalRow normal row (blockView ∘ children)`;
after erasing `Cell → ℤ` the payload is this definition. -/
def rowBlock {q width : ℕ} (normal : Bool) (row : Fin 6)
    (children : Fin 4 → BlockPayload q width) : BlockPayload q width :=
  SparseLocalForms.denseLocalRow normal row children

/-- Reading the erased `rowBlock` payload is the upstream local row. -/
theorem rowBlock_read {q width : ℕ} (normal : Bool) (row : Fin 6)
    (children : Fin 4 → BlockPayload q width) (degree : Fin width) (residue : Fin q) :
    SparseLocalForms.denseRead (rowBlock normal row children) degree residue =
      SparseLocalForms.localRow normal row
        (fun col => SparseLocalForms.denseRead (children col)) degree residue := by
  unfold rowBlock
  exact congrFun (congrFun
    (SparseLocalForms.denseLocalRow_correct normal row children) degree) residue

/-- **The named row refinement.** The physical Light row output equals the
erased `BinaryLowEncoder.rowBlock` payload read at every degree and residue. -/
theorem output_eq_rowBlock {q width : ℕ} (normal : Bool) (row : Fin 6)
    (μ : Nat → Int) (src : Fin 4 → Nat) (degree : Fin width) (residue : Fin q) :
    LowRowMachine.output normal row μ (src 0) (src 1) (src 2) (src 3) q
        (degree.val * q + residue.val) =
      SparseLocalForms.denseRead
        (rowBlock normal row
          (fun col => SparseLocalForms.toDense (LowRowRefinement.memoryGrid μ src q width col)))
        degree residue := by
  rw [rowBlock_read]
  simpa only [SparseLocalForms.denseRead_toDense] using
    LowRowRefinement.output_eq_localRow normal row μ src degree residue

/-- The same agreement over the task's input lists. -/
theorem rowValue_eq_rowBlock (normal : Bool) (row : Fin 6)
    (x : LowRowMachine.Instance) (width : Nat)
    (degree : Fin width) (residue : Fin x.q) :
    LowRowMachine.rowValue normal row x (degree.val * x.q + residue.val) =
      SparseLocalForms.denseRead
        (rowBlock normal row
          (fun col => SparseLocalForms.toDense (LowRowRefinement.listGrid x.data x.q width col)))
        degree residue := by
  rw [rowBlock_read]
  simpa only [SparseLocalForms.denseRead_toDense] using
    LowRowRefinement.rowValue_eq_localRow normal row x width degree residue

/-- A physical coefficient-array task (Wharton's `GridInstance` shape) whose
postcondition names the erased `rowBlock` payload itself. Layout facts only;
no correctness or execution premise. -/
structure GridInstance where
  flat : LowRowMachine.Instance
  width : Nat
  shape : flat.n = width * flat.q

/-- The `rowBlock`-named postcondition: the output array is the erased
`BinaryLowEncoder.rowBlock` payload over the four input coefficient arrays. -/
def rowBlockTask (normal : Bool) (row : Fin 6) : Task where
  Inst := GridInstance
  size x := x.flat.n
  bound x := x.flat.bound
  args x := (LowRowMachine.task normal row).args x.flat
  Pre x μ fr := (LowRowMachine.task normal row).Pre x.flat μ fr
  Post x μ _ _ μ' := SameOutside μ μ' x.flat.dst x.flat.n ∧
    ∀ (degree : Fin x.width) (residue : Fin x.flat.q),
      μ' (x.flat.dst + (degree.val * x.flat.q + residue.val)) =
        SparseLocalForms.denseRead
          (rowBlock normal row
            (fun col => SparseLocalForms.toDense (LowRowRefinement.listGrid x.flat.data x.flat.q x.width col)))
          degree residue

/-- The actual execution contract: each of the twelve procedures satisfies the
`rowBlock`-named task inside any program containing the twelve-procedure body. -/
theorem rowBlockTask_solves (normal : Bool) (row : Fin 6) :
    Solves (rowBlockTask normal row) LowRowMachine.allProgram
      (LowRowMachine.procedureIndex normal row)
      (fun n _ => LowRowMachine.time n) LowRowMachine.need := by
  obtain ⟨code, hcode, hbody⟩ := LowRowMachine.solves_in normal row
    (LowRowMachine.procedure_in_allProgram normal row)
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
    exact LowRowRefinement.flatten_lt degree residue
  exact (hvalues _ hi).trans
    (rowValue_eq_rowBlock normal row x.flat x.width degree residue)

/-- The `rowBlock`-named task has a polynomial resource requirement. -/
theorem rowBlockTask_need_polynomial (_normal : Bool) (_row : Fin 6) :
    PolyNeed LowRowMachine.need :=
  LowRowMachine.need_polynomial

/-- The `rowBlock`-named task is solved in `64 n + 8` actual Light steps. -/
theorem rowBlockTask_solvedIn (normal : Bool) (row : Fin 6) :
    SolvedIn (rowBlockTask normal row) (fun n _ => 64 * (n : Real) + 8) := by
  refine ⟨LowRowMachine.allProgram, LowRowMachine.procedureIndex normal row,
    (fun n _ => LowRowMachine.time n), LowRowMachine.need,
    rowBlockTask_need_polynomial normal row, rowBlockTask_solves normal row, ?_⟩
  intro n U u hn hU hu
  norm_num [LowRowMachine.time]

#print axioms output_eq_rowBlock
#print axioms rowValue_eq_rowBlock
#print axioms rowBlockTask_solves
#print axioms rowBlockTask_solvedIn

end Light.LowCacheRowBlock
