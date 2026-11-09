import MinPlusCaller
import CallerBody
import CallerRounds
import CallerChain

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
slice 2: `mpBody`'s Light statement and the shifted-chain bridge.

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

# Slice 2: `mpBody`'s statement — the layered caller program and the
shifted schedule

- `callerProgramLayered` — the caller's fixed program in the LAYERED
  `Program.behind` shape: `[mpBody]` innermost (the product core at
  procedure 0 = `mpProc`), then the restore layer, then the cache layer,
  with `program cs` (the L5/L6 round program, the certified stage at its
  procedure 6) innermost-behind. Each layer's `Program.behind` shifts the
  inner layers' call indices by its length — the sanctioned route
  (`Ends` is not prepend-stable).
- `mpBody` — the product core's Light statement: the mpRounds schedule of
  certified stage invocations, as the shifted schedule term
  `((roundCalls (mpRounds W)).shift 1).shift restoreProg.length).shift
  cacheProg.length` — the schedule `CallerRounds.roundCalls` with every
  stage call at the layered stage index. THE CONTROL-FLOW SKELETON: the
  assembly semantics (the stage outcomes into the product entries) ride
  the oracle chain premise (slice 3's Seg half).
- `CallerTargetLayered` — the phase target at the layered program.
- `chain_shifted` — THE SHIFT-COMPOSITION BRIDGE: `chain_runs`' round
  chain, transferred into the layered caller program by three composed
  `Ends.shift_append`s (one per layer). This is the execution
  derivation's skeleton step: the frame half of the body's run, at the
  caller program.

THE REMAINING SLICES: the product core's assembly glue (the stage
outcomes into the product entries — the Seg half through the oracle
functional chain, `DenseOracleCorrect`-conditioned, upstream's own
shape), and the step count for `CallerHdom`. D7's boundary stands: no
(min,+) product is claimed in this module.
-/

namespace ThinMatrix.CallerBodyStmt

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerBody ThinMatrix.CallerRounds ThinMatrix.CallerChain

/-! ## The layered caller program -/

/-- The caller's fixed program in the layered shape: `[mpBody]` carries
the product core at procedure 0; the restore layer and the cache layer
ride behind it; the round program (the certified stage at its procedure
6) is innermost-behind. Each layer's `Program.behind` shifts the inner
call indices by its length. -/
def callerProgramLayered (mpBody : Light.Stmt)
    (cacheProg restoreProg : Light.Program) (cs : Inst) : Light.Program :=
  Program.behind cacheProg
    (Program.behind restoreProg (Program.behind [mpBody] (program cs)))

/-- The layered stage index: procedure 6 of the round program, shifted
behind the product core, the restore layer and the cache layer. -/
abbrev stageProcLayered (cacheProg restoreProg : Light.Program) : ℕ :=
  cacheProg.length + restoreProg.length + (1 + 6)

/-! ## `mpBody`: the product core's statement -/

/-- THE PRODUCT CORE'S STATEMENT: the mpRounds schedule of certified
stage invocations, as the shifted schedule term — every stage call at
the layered stage index. The control-flow skeleton; the assembly
semantics ride the oracle chain premise (slice 3). -/
def mpBody (cacheProg restoreProg : Light.Program) (cs : Inst) (W : ℕ) :
    Light.Stmt :=
  (((roundCalls (mpRounds W)).shift 1).shift restoreProg.length).shift
    cacheProg.length

/-- The phase target at the layered program: SummitSlot's `hs` component
at `callerProgramLayered` — the layered `CallerTarget`. -/
def CallerTargetLayered (mpBody : Light.Stmt)
    (cacheProg restoreProg : Light.Program) (cs : Inst)
    (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Light.Need) : Prop :=
  Light.Solves Light.mpTask
    (callerProgramLayered mpBody cacheProg restoreProg cs) 0 Tn need

/-! ## The shift-composition bridge -/

/-- A run over `P ++ []` is a run over `P`. -/
theorem exec_append_nil {lim : Limits} {d : ℕ} {P : Program} {s : Stmt}
    {σ σ' : State} {c : ℕ} (h : Exec lim (P ++ []) d s σ σ' c) :
    Exec lim P d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ h₄ ih =>
      refine .call h₁ ?_ h₃ ih
      have hlen : (P ++ []).length = P.length := by simp
      have hs := List.getElem?_eq_some_iff.1 h₂
      obtain ⟨hi, -⟩ := hs
      rw [hlen] at hi
      exact (List.getElem?_append_left hi).symm.trans h₂

/-- A chain over the empty-trailing program is the chain over the bare
round program. -/
theorem chain_nil {lim : Limits} {d : ℕ} {P : Program} {s : Stmt}
    {σ : State} {T : ℕ} {post : State → Prop} (h : Ends lim (P ++ []) d s σ T post) :
    Ends lim P d s σ T post := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, exec_append_nil he, hc, hq⟩

/-- THE SHIFT-COMPOSITION BRIDGE: the round chain, transferred into the
layered caller program by three composed `Ends.shift`s — one per layer
(`[mpBody]`, then the restore layer, then the cache layer) — and one
append for the caller's trailing program. The statement lands exactly on
`mpBody` (the thrice-shifted schedule), the state on the round chain's
start frame, and the post on the caller's three-region frame. Premises
are `chain_runs`'s, unchanged. -/
theorem chain_shifted (r₀ : ℤ)
    {lim : Limits} {d : ℕ}
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ} {μ₀ : ℕ → ℤ}
    {cacheProg restoreProg : Light.Program} (W : ℕ)
    (hdim : d < lim.depth)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hslots : ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
      StageReads P I active mask rows ab rb mb μ →
      kt ≤ (flagged P mask).card →
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ [])
        6 (d + 1) (argsOf (callSite P kt I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
        (Tt kt)
        (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr))
    (hTt : ∀ kt : ℕ, 9 + 2 + Tt kt ≤ B)
    (hflag : ∀ mask : ℕ → Bool, k ≤ (flagged P mask).card)
    (hok : ∀ (mask : ℕ → Bool) (kt : ℕ),
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hreads₀ : StageReads P I active remaining rows ab rb mb μ₀)
    (hT : mpRounds W * B ≤ T)
    (R : Light.Program) :
    Ends lim
      (Program.behind cacheProg (Program.behind restoreProg
        (Program.behind [mpBody cacheProg restoreProg cs W]
          (program (callSite P k I h active remaining rows ab rb sb mb bb)))) ++ R)
      (d)
      ((((roundCalls (mpRounds W)).shift 1).shift restoreProg.length).shift cacheProg.length)
      ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]),
        μ₀⟩ T
      (fun σ' => SameOutside3 μ₀ σ'.mem sb P bb I mb P) :=
    Ends.append
      (Ends.shift (Ends.shift (Ends.shift (chain_nil
        (chain_runs r₀ W hdim hbound hlay hslots hTt hflag hok hreads₀ hT (R := [])))
        [mpBody cacheProg restoreProg cs W]) restoreProg) cacheProg) R

#print axioms exec_append_nil
#print axioms chain_nil
#print axioms chain_shifted

end ThinMatrix.CallerBodyStmt
