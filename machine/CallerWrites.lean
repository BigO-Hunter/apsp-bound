import MinPlusCaller
import CallerBodyStep
import CallerDataflow

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the writes session: the bracket-cell semantics and the assembly writes.

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

# The writes session: the bracket cells and the assembly writes

- `bracketCell` — the per-(i, j) bracket-state cell: the memory address
  `x.c + i * x.n + j` in the product region, holding the level-t coarse
  estimate of the (min,+) entry.
- `refineWrite` — the per-round cell-update rule: the level-(t+1) cell
  from the level-t cell and the round's two adaptive tests — the design's
  `refineStep` applied at the cell (upstream `MinPlusReduction.refine`'s
  if-then-else at the pinning).
- `bracketAccumulate` — the mpRounds-fold: the bracket cells after the
  whole schedule, given the cells before and the per-round test outcomes
  — the accumulation whose final state IS the (min,+) product entries
  (the `minPlusList` identity rides the oracle premise — D7's boundary).
- `mpBodyWritesEntry` / `mpBodyWritesRow` — the Light statements of the
  write steps at the pinned layout: the per-entry store into
  `c + i * x.n + j` (the `v Out +' v Candidate` addressing shape, byte-
  formed like the landed `DenseScoreTablePass.roundBody`'s store), and
  the per-row loop skeleton. SHAPE ONLY: the execution derivation awaits
  the parameter concretization (DATAFLOW.md's named sub-design — the
  mod-p/band encoding premise; D7's boundary stands, the oracle is a
  premise, never claimed as proved).

THE REMAINING SLICES: the execution derivation of the writes (the Seg
half of `mpBody`'s run — the bracket cells' final state = the
`minPlusList` entries, through the oracle functional chain); the step
count for `CallerHdom`. Until they land, `CallerTarget(Layered)` and the
twin stay conditional — honestly: no solver is postulated, no (min,+)
product is claimed.
-/

namespace ThinMatrix.CallerWrites

open ThreeSumApsp Light

/-! ## The bracket cells -/

/-- The per-(i, j) bracket-state cell: the memory address in the product
region holding the level-t coarse estimate of the (min,+) entry. -/
def bracketCell (x : MatInst) (i j : ℕ) : ℕ := x.c + i * x.n + j

/-- The per-round cell-update rule: the level-(t+1) cell from the
level-t cell and the round's two adaptive tests — the design's
`refineStep` at the cell. -/
def refineWrite (C : ℤ) (lower upper : Bool) : ℤ :=
  if lower then 2 * C else if upper then 2 * C + 1 else 2 * C + 2

/-- The mpRounds-fold: the bracket cell after the whole schedule, given
the cell before and the per-round adaptive tests. The final state's
identity with the (min,+) entry rides the oracle premise (D7's
boundary). -/
def bracketAccumulate (C : ℤ) (tests : ℕ → Bool × Bool) (rounds : ℕ) : ℤ :=
  (List.range rounds).foldl (fun c t => refineWrite c (tests t).1 (tests t).2) C

/-! ## The write statements' shape (the pinned layout) -/

/-- The per-entry write: store the refined bracket value into the
product cell `c + i * x.n + j` — the `v Out +' v Candidate` addressing
shape, byte-formed like the landed `DenseScoreTablePass.roundBody`'s
store. Register map: `Out` = the product base (x.c), `Idx` = the entry
index i * x.n + j, `Score` = the refined bracket value. -/
def mpBodyWritesEntry (Out Idx Score : ℕ) : Light.Stmt :=
  Light.Stmt.store (v Out +' v Idx) (v Score)

/-- The per-row write skeleton: the entries of one row, stored
sequentially — the row's j-loop unrolled as the store sequence over the
entry indices `i * x.n + j` for `j < x.n`. SHAPE ONLY: the loop control
and the score computation ride the body's remaining slices. -/
def mpBodyWritesRow (Out Base : ℕ) (x : MatInst) (i : ℕ) : Light.Stmt :=
  (List.range x.n).foldl
    (fun s j => Light.Stmt.seq s
      (mpBodyWritesEntry Out (i * x.n + j) (Base + j))) Light.Stmt.skip

#print axioms refineWrite

end ThinMatrix.CallerWrites
