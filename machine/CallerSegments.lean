import MinPlusCaller
import CallerBodyStep
import CallerRounds

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
slice 3a: the stage-to-matrix KeptBut corollary and the Seg-half target.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# Slice 3a: the stage-to-matrix frame delivery and the Seg-half target

- `chain_keptBut` — the stage-to-matrix frame delivery: a chain run at
  the caller's scratch layout (the five buffers at the caller's free
  pointer, `CallerBodyStep`'s layout) delivers the matrix instance's
  `KeptBut μ₀ σ'.mem fr x.c (x.n * x.n)` — every cell below the caller's
  free pointer and outside the product region is preserved. The frame
  half of the body's run, at the matrix instance.
- `SegTarget` — the Seg half's machine bridge, stated as the named
  remainder: the caller program's run leaves `minPlusList x.n x.A x.B` at
  the product region. THE BRIDGE'S CONTENT: the caller's data-flow design
  — how the stage outcomes (`cs₁`-selected rows, the cached rows, the
  oracle answers) meet the ten-term product entries. That design is the
  next body session's core task; this module states the target and does
  not fake it.

THE ORACLE PREMISE (D7's boundary): the Seg half's functional consumption
conditions on `MinPlusReduction.OracleCorrect O` — upstream's own shape
(the premise `bounded_signed_eq_minPlus` and the stored chapter's
`bitScale_value`/`apsp_correct` take). The `DenseOracleCorrect`
connection rides with Fill 1's cache body
(`semanticOracle_correct`). No (min,+) product is claimed here.
-/

namespace ThinMatrix.CallerSegments

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerBodyStep ThinMatrix.CallerRounds

/-- THE STAGE-TO-MATRIX FRAME DELIVERY: a chain run at the caller's
scratch layout delivers the matrix instance's `KeptBut` — every cell
below the caller's free pointer and outside the product region is
preserved across the whole schedule. -/
theorem chain_keptBut
    {x : MatInst} {lim : Limits} {d : ℕ}
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ} {μ₀ : ℕ → ℤ}
    {R : Light.Program} (W : ℕ)
    (xpre : x.Pre μ₀ fr)
    (hchain : Ends lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      d (roundCalls (mpRounds W))
      ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]),
        μ₀⟩ T
      (fun σ' => SameOutside3 μ₀ σ'.mem (callerSb fr P I) P
        (callerBb fr P I) I (callerMb fr P I) P)) :
    Ends lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      d (roundCalls (mpRounds W))
      ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]),
        μ₀⟩ T
      (fun σ' => KeptBut μ₀ σ'.mem fr x.c (x.n * x.n)) := by
  obtain ⟨σ'', c, he, hc, hq⟩ := hchain
  refine ⟨σ'', c, he, hc, ?_⟩
  exact keptBut_of_chain xpre hq

/-- THE SEG HALF'S MACHINE BRIDGE, stated as the named remainder: the
caller program's run leaves `minPlusList x.n x.A x.B` at the product
region — the (min,+) product of the matrix instance's entries. The
BRIDGE'S CONTENT is the caller's data-flow design (how the stage
outcomes meet the ten-term product entries) — the next body session's
core task; this module states the target and does not fake it. The
functional consumption rides the oracle premise
(`MinPlusReduction.OracleCorrect` — upstream's own shape; D7's boundary
stands). -/
def SegTarget
    {x : MatInst} {lim : Limits} {d : ℕ}
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ} {μ₀ : ℕ → ℤ}
    (W : ℕ) (R : Light.Program) : Prop :=
  Ends lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
    d (roundCalls (mpRounds W))
    ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]),
      μ₀⟩ T
    (fun σ' => Seg σ'.mem x.c (ThreeSumApsp.Spec.minPlusList x.n x.A x.B) ∧
      KeptBut μ₀ σ'.mem fr x.c (x.n * x.n))

#print axioms chain_keptBut

end ThinMatrix.CallerSegments
