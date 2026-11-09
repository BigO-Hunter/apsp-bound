import MinPlusCaller
import CacheFill
import RestoreFill
import CallerCompose
import CallerSchedule

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3, piece 3 — the
composition chaining.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds the slots drive
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations
  record this composition answers to.
- Hrishik Sai Bojnal — the verified frontier being refined.

# FILL 3, piece 3: the composition chaining

The fixed-program shape is PINNED (STMTS.md, "FILL 3 composition shape"):
the stage, cache and restore procedures ride INSIDE the caller's own
program `P` — they are procedures the `mpTask`-solver body invokes — and
the append direction is reserved for the upstream host, which appends its
four finite procedures AFTER `P` (`MachineAdapter.appendAPSP` via
`Light.Sec3.isHost_ap`: the host builds
`[apInitBody, clipBody, apOutBody, apBody p P.length …]` at indices
`P.length + k`). `Light.Solves.append` is therefore the chaining
primitive while the port lands the caller's procedures: each landed
procedure's contract survives the composed program growing behind it,
with the entry index fixed.

What this module proves (the chaining content that closes from the landed
slots; the fills' bodies and the caller's product-round body still trail
board-side — MACHINE_OBLIGATIONS' "actual caller matching mpTask" row):

- `cacheSlot_append` / `restoreSlot_append` — the two fill slots' contracts
  persist under a trailing append (`Solves.append`), so the cache and
  restore procedures compose into the growing caller program with their
  entry indices fixed;
- `thread_step_append` — the schedule threading's two-stage run persists
  under a trailing append (`Ends.append`), the form the mpRounds schedule
  chains over (the single-stage analog is piece 1's
  `stageEnds_behind_append`).

THE NAMED SUMMIT (not discharged here; D7's boundary stands): the
`hsShape` target — `Light.Solves Light.mpTask P p Tn need` — awaits the
caller's product-round body and its execution derivation over the
mpRounds schedule (the obligations record's "actual caller matching
mpTask, including all arrays, scans, control flow, and word bounds"), and
`hdom` awaits that program's step-count bound against
`AsymptoticCosts.completeCost`. No sorry, no native_decide; nothing false
is claimed.
-/

namespace ThinMatrix.CallerSolves

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CacheFill ThinMatrix.RestoreFill
  ThinMatrix.CallerCompose ThinMatrix.CallerSchedule

/-! ## The fill slots persist under the composed program's growth -/

/-- FILL 1's slot: the cache program's contract survives a trailing
append — the cache procedure composes into the caller's growing program
with its entry index fixed. -/
theorem cacheSlot_append {cacheProg : Light.Program} {cacheProc : ℕ}
    {cacheTime : ℕ → ℕ → ℕ} {cacheNeed : ℕ → ℕ → Light.Need}
    (hs : Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed)
    (R : Light.Program) :
    Light.Solves cacheTask (cacheProg ++ R) cacheProc cacheTime cacheNeed :=
  Light.Solves.append hs R

/-- FILL 2's slot: the restore program's contract survives a trailing
append — the restore procedure composes into the caller's growing program
with its entry index fixed. -/
theorem restoreSlot_append {restoreProg : Light.Program} {restoreProc : ℕ}
    {restoreTime : ℕ → ℕ → ℕ} {restoreNeed : ℕ → ℕ → Light.Need}
    (hs : Light.Solves restoreTask restoreProg restoreProc restoreTime restoreNeed)
    (R : Light.Program) :
    Light.Solves restoreTask (restoreProg ++ R) restoreProc restoreTime restoreNeed :=
  Light.Solves.append hs R

/-! ## The schedule threading persists under the composed program's growth -/

/-- Piece 2's two-stage threading survives a trailing append — the form
the mpRounds schedule chains over (the single-stage analog is piece 1's
`stageEnds_behind_append`). Premises are thread_step's, unchanged. -/
theorem thread_step_append
    {lim : Limits} {d : ℕ}
    {P k₁ k₂ I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {T₁ T₂ T : ℕ} {μ₀ : ℕ → ℤ}
    (hdim : d < lim.depth)
    (hT : 9 + 2 + T₁ + (9 + 2 + T₂) ≤ T)
    (hAR : ∀ i < I, μ₀ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ₀ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ₀ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR₁ : k₁ ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k₁ I h active remaining rows ab rb sb mb bb))
      (callSite P k₁ I h active remaining rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hR₂ : ∀ cs₁ : List ℕ, cs₁.length = k₁ → cs₁.Nodup →
      (∀ c ∈ cs₁, c < P ∧ remaining c = true) →
      k₂ ≤ (flagged P (maskCleared cs₁.toFinset remaining)).card)
    (hok₂ : ∀ cs₁ : List ℕ, cs₁.length = k₁ → cs₁.Nodup →
      (∀ c ∈ cs₁, c < P ∧ remaining c = true) →
      (need (instanceSize (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
        ab rb sb mb bb))
        (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
          ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hsafe₁ : ∀ e ∈ callArgs,
      e.Safe lim ⟨frame (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++
        [(fr : ℤ)]), μ₀⟩)
    (hloc₁ : ∀ k : ℕ, k < 9 →
      (callArgs.map (fun e => e.val ⟨frame (argsOf (callSite P k₁ I h active remaining rows
        ab rb sb mb bb) ++ [(fr : ℤ)]), μ₀⟩)).getD k 0 =
      (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]).getD k 0)
    (hsafe₂ : ∀ (r₁ : ℤ) (μ₁ : ℕ → ℤ), ∀ e ∈ callArgs,
      e.Safe lim ⟨Function.update (frame (argsOf (callSite P k₁ I h active remaining rows
        ab rb sb mb bb) ++ [(fr : ℤ)])) 10 r₁, μ₁⟩)
    (hloc₂ : ∀ (r₁ : ℤ) (μ₁ : ℕ → ℤ) (k : ℕ), k < 9 →
      (callArgs.map (fun e => e.val ⟨Function.update (frame (argsOf (callSite P k₁ I h active
        remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])) 10 r₁, μ₁⟩)).getD k 0 =
      (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]).getD k 0)
    (h1 : Meets lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [])
      6 (d + 1) (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ₀ T₁
      (pinnedPost (callSite P k₁ I h active remaining rows ab rb sb mb bb) μ₀ fr))
    (h2 : ∀ (μ₁ : ℕ → ℤ) (cs₁ : List ℕ), cs₁.length = k₁ → cs₁.Nodup →
      (∀ c ∈ cs₁, c < P ∧ remaining c = true) →
      SameOutside3 μ₀ μ₁ sb P bb I mb P →
      (∀ i < I, μ₁ (ab + i) = DenseScorePass.bit (active i)) →
      (∀ p < P, ∀ i < I, μ₁ (rb + p * I + i) = rows p i) →
      (∀ p < P, μ₁ (mb + p) = DenseArgminPass.bit (maskCleared cs₁.toFinset remaining p)) →
      k₂ ≤ (flagged P (maskCleared cs₁.toFinset remaining)).card →
      (need (instanceSize (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
        ab rb sb mb bb))
        (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
          ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [])
      6 (d + 1) (argsOf (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
        ab rb sb mb bb) ++ [(fr : ℤ)]) μ₁ T₂
      (pinnedPost (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
        ab rb sb mb bb) μ₁ fr))
    (R : Light.Program) :
    Ends lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ R)
      d
      (.call 6 callArgs Tmp ;; .call 6 callArgs Tmp)
      ⟨frame (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]), μ₀⟩ T
      fun σ' => SameOutside3 μ₀ σ'.mem sb P bb I mb P := by
    simpa [List.append_assoc] using
      Ends.append (thread_step hdim hT hAR hRR hbound hfl hR₁ hlay hok hR₂ hok₂
        hsafe₁ hloc₁ hsafe₂ hloc₂ h1 h2) R

#print axioms cacheSlot_append
#print axioms restoreSlot_append
#print axioms thread_step_append

end ThinMatrix.CallerSolves
