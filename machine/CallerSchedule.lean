import MinPlusCaller
import ThreeSumApsp.Lang.Renumber

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3, piece 2 — the
schedule threading.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds this threading drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement and the checked
  selection round / restart-loop driver the rounds instantiate.
- Hrishik Sai Bojnal — the verified frontier being refined.

# FILL 3, piece 2: the schedule threading step

Two certified stage calls in the driver's own composed program, threaded
through the EVOLVED state: round 1's certified post supplies round 2's read
premises — the persisted active/rows reads (from the post's `SameOutside3`
frame) and the EVOLVED mask reads (from the post's cleared-mask clause,
`maskCleared cs₁.toFinset remaining` — L5's loop logic at caller scale).
The calling-convention premises — `Safe` and the evaluated-arguments bridge
for the driver's own `callArgs`, under the round-1 frame and under the
`Tmp`-updated frame — are definitional: the nine `callArgs` read locals 0–8
of the pinned frame (the loop file's e0–e8 prelude values,
`DenseRestartSelectionLoop.lean` 349–378), so both evaluated-arguments
bridges close by `rfl` — the `Tmp = 10` update touches no argument
register. Round 2's task premises at the evolved mask (the flag
budget and the `Ok` fit) are caller-supplied in `h2`'s own shape, pinned
over the chosen list. The pair runs as one sequential statement
(`Ends.callThen` nesting). The `mpRounds` general threading rides this step
with the caller's pinning schedule; the Solves composition into `hsShape`
and `hdom` are the remaining FILL 3 mass. D7's boundary stands.
-/

namespace ThinMatrix.CallerSchedule

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light

/-- The threading step: two certified stage calls in the driver's own
composed program, threaded through the evolved state. Round 1's certified
post supplies round 2's read premises (persisted active/rows reads via the
`SameOutside3` frame; the evolved mask via the cleared-mask clause). The
calling-convention premises follow the loop file's `hloc` pattern: the
caller supplies `Safe` and the evaluated-arguments bridge under the round-1
frame and under the `Tmp`-updated frame (the update touches local 10 only;
`callArgs` reads locals 0–8). -/
theorem thread_step
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
    -- round 2's task premises at the evolved mask (h2's own contract,
    -- pinned over the chosen list)
    (hR₂ : ∀ cs₁ : List ℕ, cs₁.length = k₁ → cs₁.Nodup →
      (∀ c ∈ cs₁, c < P ∧ remaining c = true) →
      k₂ ≤ (flagged P (maskCleared cs₁.toFinset remaining)).card)
    (hok₂ : ∀ cs₁ : List ℕ, cs₁.length = k₁ → cs₁.Nodup →
      (∀ c ∈ cs₁, c < P ∧ remaining c = true) →
      (need (instanceSize (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
        ab rb sb mb bb))
        (callSite P k₂ I h active (maskCleared cs₁.toFinset remaining) rows
          ab rb sb mb bb).height).Ok lim fr (d + 1))
    -- the calling-convention premises (the driver's own `callArgs`)
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
    -- round 1: the certified stage slot in the driver's own composed program
    (h1 : Meets lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [])
      6 (d + 1) (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ₀ T₁
      (pinnedPost (callSite P k₁ I h active remaining rows ab rb sb mb bb) μ₀ fr))
    -- round 2: the certified stage slot in the driver's own composed program
    -- (the same procedure 6 the first call runs), at the evolved pinning's
    -- task: uniformly in the evolved memory and round 1's outcome
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
        ab rb sb mb bb) μ₁ fr)) :
    Ends lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [])
      d
      (.call 6 callArgs Tmp ;; .call 6 callArgs Tmp)
      ⟨frame (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]), μ₀⟩ T
      fun σ' => SameOutside3 μ₀ σ'.mem sb P bb I mb P := by
  -- the calling-convention premises are definitional: `callArgs` reads the
  -- nine round registers (locals 0–8 — the loop file's e0–e8 prelude values,
  -- DenseRestartSelectionLoop.lean:349–378), so the evaluated-arguments
  -- bridges close by `rfl`; the `Tmp = 10` update touches no argument
  -- register. Only the cost clocks need the loop file's `callArgs_cost`.
  refine Ends.callThen h1 ?_ ⟨hsafe₁, rfl⟩ hdim (hT := by rw [callArgs_cost]; omega)
  intro r₁ μ₁ hpost₁
  obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, -, -⟩ := hpost₁
  -- the frame, in the caller's atom variables (the pinnedPost path unfolds)
  have hsam' : SameOutside3 μ₀ μ₁ sb P bb I mb P := hsam
  have hAR₂ : ∀ i < I, μ₁ (ab + i) = DenseScorePass.bit (active i) := by
    intro i hi
    rw [hsam' (ab + i) ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
    exact hAR i hi
  have hRR₂ : ∀ p < P, ∀ i < I, μ₁ (rb + p * I + i) = rows p i := by
    intro p hp i hi
    have hlt : p * I + i < P * I := by nlinarith
    rw [hsam' (rb + p * I + i) ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
    exact hRR p hp i hi
  have h2' := h2 μ₁ cs₁ hlen hnd hmem hsam' hAR₂ hRR₂ (fun p hp => hmask p hp)
    (hR₂ cs₁ hlen hnd hmem) (hok₂ cs₁ hlen hnd hmem)
  -- the evolved frame: the `Tmp = 10` update touches no argument register,
  -- so round 2's calling-convention premises close the same way
  refine Ends.callLast h2' ?_
    ⟨fun e he => hsafe₂ r₁ μ₁ e he, rfl⟩ (by omega)
    (hT := by
      show (callArgs.map Expr.cost).sum + 2 + T₂ ≤
        T - ((callArgs.map Expr.cost).sum + 2 + T₁)
      rw [callArgs_cost]
      omega)
  intro r₂ μ₂ hpost₂
  obtain ⟨-, -, -, -, -, hsamP, -, -⟩ := hpost₂
  intro x hx
  exact (hsamP x hx).trans (hsam' x hx)

#print axioms thread_step

end ThinMatrix.CallerSchedule
