import MinPlusCaller
import CallerBody
import CallerSummit
import TwinRaceBound

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
session (b): the Post-assembly packaging.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  landed `Race.bound` (2.995560766) is the root sibling.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# Session (b): the Post-assembly packaging — the twin's fire-condition

`CallerTarget` (the body phase's named target: the caller program's
`Solves mpTask` at the entry procedure) plus two sockets — the polynomial
need and the `completeCost` domination at the caller's own clock — is
EXACTLY the summit's existence slot, witnessed by the caller's own fixed
program:

- `CallerHdom` — the domination socket at the caller's clock: the
  adapter's `hdom` binder, verbatim.
- `summit_of_CallerTarget` — the packaging: `CallerTarget + hn + hdom`
  yields `ThinMatrix.Summit.SummitSlot`, with `callerProgram` /
  `mpProc` as the witness.
- `twin_of_CallerTarget` — the twin's fire-condition: the conservative
  `Race.bound` form (2.994999) fires from `CallerTarget + hn + hdom`
  directly — when the product-round body lands, the filing theorem is
  THIS theorem, no further composition.

THE REMAINING BODY SESSIONS (named; D7's boundary stands):
- the product-round body itself (the mpTask solver's core procedure) and
  its execution derivation — the mpRounds chaining (`chain_runs`) is the
  frame half; the Post's `KeptBut` half assembles through the caller's
  frame (`mpPost_interior`/`cert_keptBut` are the interior bricks) and
  the `Seg` half through the oracle functional chain
  (`StoredMinPlusAPSP.apsp_correct` / `MinPlusReduction.bounded_signed_eq_minPlus`,
  `DenseOracleCorrect`-conditioned — the oracle is a premise in upstream's
  own shape; no (min,+) product is claimed here);
- the step count for `CallerHdom`: the product body's own scan over the
  mpRounds schedule plus the certified stage clocks — the bricks
  (`taskTime_le_of_size` / `instanceSize_le` / `mpRounds_eq`, and the
  chain's per-round budget structure `B` / `Tt` / `9+2`) pin its shape;
  `AsymptoticCosts.costBoundOfEventualDomination` is the turnstile.

Until those land, the twin stays conditional — honestly: no solver is
postulated, no (min,+) product is claimed, nothing here closes `hs` by
assertion.
-/

namespace ThinMatrix.CallerPost

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerBody ThinMatrix.Summit

/-- The domination socket at the caller's clock: the canonical adapter's
`hdom` binder, at the caller's own `Tn`. -/
def CallerHdom (Tn : ℕ → ℕ → ℕ) : Prop :=
  ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
    Light.timeUpTo (Light.Sec3.apTime Tn) n
      ((n : Real) ^ (κ : Real)) ≤
      C * AsymptoticCosts.completeCost k n

/-- The packaging: `CallerTarget` (the caller program's `Solves mpTask`
at the entry procedure) plus the need and domination sockets is the
summit's existence slot, witnessed by the caller's own fixed program —
`callerProgram mpBody cacheProg restoreProg cs` at procedure `mpProc`. -/
theorem summit_of_CallerTarget
    {mpBody : Light.Stmt} {cacheProg restoreProg : Light.Program}
    {cs : Inst} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Light.Need}
    (htarget : ThinMatrix.CallerBody.CallerTarget mpBody cacheProg restoreProg cs
      Tn need)
    (hn : Light.PolyNeed need)
    (hdom : CallerHdom Tn) :
    SummitSlot := by
  refine ⟨ThinMatrix.CallerBody.callerProgram mpBody cacheProg restoreProg cs,
    ThinMatrix.CallerBody.mpProc, Tn, need, htarget, hn, hdom⟩

/-- The twin's fire-condition: the conservative `Race.bound` form
(2.994999) fires from `CallerTarget + hn + hdom` directly. When the
product-round body lands, the filing theorem is this theorem — no
further composition. -/
theorem twin_of_CallerTarget
    {mpBody : Light.Stmt} {cacheProg restoreProg : Light.Program}
    {cs : Inst} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Light.Need}
    (htarget : ThinMatrix.CallerBody.CallerTarget mpBody cacheProg restoreProg cs
      Tn need)
    (hn : Light.PolyNeed need)
    (hdom : CallerHdom Tn) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) :=
  twin_of_summit (summit_of_CallerTarget htarget hn hdom)

#print axioms summit_of_CallerTarget
#print axioms twin_of_CallerTarget

end ThinMatrix.CallerPost
