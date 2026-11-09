import DenseRestartSelectionLoop

/-!
Copyright (c) 2026. APSP port campaign: L6 min-plus caller.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence reduction and its greedy stage
  (`ArrayCompositeAlgorithm.stage`, thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler
  (`Submission/`) whose Light language these procedures execute in.
- Joshua Wharton (QFEX) — the checked selection round and the restart-loop
  driver this caller wires.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L6(a): the min-plus caller's composite-incidence certification

`ArrayCompositeAlgorithm.stage` runs
`greedy O active primes k 1 remaining blockSizes []`: `k` restarts of the
selection round over the `P`-candidate pool, at incidence length `I`, with the
greedy premise `k ≤ (pool primes remaining).card` — exactly the
`enoughFlags` form (`R ≤ (flagged P remaining).card`) the L5 driver pins.

This file is the caller. It builds the pinned call site
(`DenseRestartSelectionLoop.callSite P k I h …`) from the stage's parameters,
supplies `pre_of_reads`' five physical reads as the pinned task's `Pre`
(`certTask_pre`), and consumes `callSite_meets` / `pinnedTask_solvedIn`
inside the composite-incidence certification the `mpTask` Post demands:
the certified post (`cert_post`), the chosen restarts (`cert_chosen`), the
cleared mask (`cert_mask`), the active-incidence scores (`cert_scores`), the
selected row (`cert_row`), the per-round argmin chain (`cert_argmin`), the
memory frame (`cert_frame`, `cert_zero`), the pool cardinality the
certification finish consumes (`cert_pool`), and the polynomial clock
(`cert_solvedIn`). Nothing here re-proves the loop: every clause is extracted
from the wrapper's `Meets`/`Post` conclusions.

Statements touch no board-model text; the D7 boundary stands (no
bit-cost → Light-step translation).
-/

namespace Light.DenseCompositeCaller

open Light DenseRestartSelectionLoop

/-! ## The pinned call site, packaged as the caller's task -/

/-- The caller's composite-incidence certification task: the pinned restart
task at the stage's `(P, k)` call site. Upstream this is `stage`'s
`greedy O active primes k 1 remaining blockSizes []` — `k` restarts over the
`P`-sized pool at incidence length `I`, row bound `h`, five ordered regions. -/
def certTask (P k I h : ℕ) (active remaining : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (ab rb sb mb bb : ℕ) : Task :=
  pinnedTask (callSite P k I h active remaining rows ab rb sb mb bb)

/-- The stage's physical reads assemble into the certification task's
premise: active-incidence bits, the rows table, the row bound, the plain flag
memory, the greedy pool premise, and the five-region layout — `pre_of_reads`
supplies the pinned task's `Pre` at the call site. -/
theorem certTask_pre {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {μ : ℕ → ℤ}
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)]) :
    (certTask P k I h active remaining rows ab rb sb mb bb).Pre
      ⟨callSite P k I h active remaining rows ab rb sb mb bb, rfl⟩ μ fr :=
  pre_of_reads hAR hRR hbound hfl hR hlay

/-! ## The caller's contracts, consumed from the wrapper -/

/-- The composite-incidence certification contract the `mpTask` Post demands,
at the n×n call site: procedure `6` of the driver program meets the pinned
certification within the pinned clock, in every appended program. This is
`callSite_meets` at the stage's `(P, k)` — consumed, not re-proved. -/
theorem cert_meets {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {lim : Limits} {d : ℕ}
    {μ : ℕ → ℤ} {Prog : Program}
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
      (callSite P k I h active remaining rows ab rb sb mb bb).height).Ok lim fr d) :
    Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ Prog) 6 d
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
      (taskTime (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
        (callSite P k I h active remaining rows ab rb sb mb bb).height)
      (pinnedPost (callSite P k I h active remaining rows ab rb sb mb bb) μ fr) :=
  callSite_meets (Prog := Prog) hAR hRR hbound hfl hR hlay hok

/-- The certification task is solved in the pinned polynomial clock
`100·n² + 98·n` — the caller's side of the resource ledger, consumed from
`pinnedTask_solvedIn`. -/
theorem cert_solvedIn (P k I h : ℕ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (ab rb sb mb bb : ℕ) :
    SolvedIn (certTask P k I h active remaining rows ab rb sb mb bb)
      (fun n _ => ((100 * n * n + 98 * n : ℕ) : ℝ)) :=
  pinnedTask_solvedIn _

/-- The certification post holds after the caller's driver runs: some final
memory carries the full composite-incidence certification. The single
extraction every consumable below reads from. -/
theorem cert_post {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {lim : Limits} {d : ℕ}
    {μ : ℕ → ℤ} {Prog : Program}
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
      (callSite P k I h active remaining rows ab rb sb mb bb).height).Ok lim fr d) :
    ∃ μ' : ℕ → ℤ,
      Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ' := by
  obtain ⟨body, -, hE⟩ := cert_meets (Prog := []) hAR hRR hbound hfl hR hlay hok
  obtain ⟨σ', c, -, -, hq⟩ := hE
  exact ⟨σ'.mem, hq⟩

/-! ## The four consumable facts

Each reads one clause of the certified post; the chosen-restart list is the
same `cs` throughout a single post, so list-shaped facts stay in `∃` form to
preserve that linkage. -/

/-- The chosen restarts: exactly `k`, distinct, all flagged candidates. -/
theorem cert_chosen {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ cs : List ℕ, cs.length = k ∧ cs.Nodup ∧
      ∀ c ∈ cs, c < P ∧ remaining c = true := by
  obtain ⟨cs, hlen, hnd, hmem, -, -, -, -⟩ := hpost
  exact ⟨cs, hlen, hnd, hmem⟩

/-- The cleared mask: every flag reads the original mask with exactly the
chosen restarts forced off. -/
theorem cert_mask {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ cs : List ℕ, ∀ p < P,
      μ' (mb + p) = DenseArgminPass.bit (maskCleared cs.toFinset remaining p) := by
  obtain ⟨cs, -, -, -, hflags, -, -, -⟩ := hpost
  exact ⟨cs, hflags⟩

/-- Score selection: the scores region holds the active-incidence scores. -/
theorem cert_scores {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hk : 0 < k)
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ')
    (p : ℕ) (hp : p < P) :
    μ' (sb + p) = (DenseScoreTablePass.scores active rows I p : ℤ) := by
  obtain ⟨cs, -, -, -, -, -, -, hpos⟩ := hpost
  obtain ⟨c, -, -, hsc, -⟩ := hpos hk
  exact hsc p hp

/-- The certification rule: the base buffer holds a flagged candidate's
complete row — the last restart's selection. -/
theorem cert_row {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hk : 0 < k)
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ c : ℕ, (∀ i < I, μ' (bb + i) = rows c i) ∧ c < P ∧ remaining c = true := by
  obtain ⟨cs, -, -, hmem, -, -, -, hpos⟩ := hpost
  obtain ⟨c, hget, hrow, -, -⟩ := hpos hk
  have hcm : c ∈ cs := List.mem_of_getLast? hget
  exact ⟨c, hrow, hmem c hcm⟩

/-- The argmin chain: each restart chose a minimum-score candidate over the
mask cleared by the restarts before it. -/
theorem cert_argmin {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hk : 0 < k)
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ cs : List ℕ, cs.length = k ∧ cs.Nodup ∧
      ∀ j : ℕ, j < cs.length →
        DenseArgminPass.IsArgmin
          (maskCleared (cs.take j).toFinset remaining)
          (DenseScoreTablePass.scores active rows I) P (cs.getD j 0) := by
  obtain ⟨cs, hlen, hnd, -, -, -, -, hpos⟩ := hpost
  obtain ⟨c, -, -, -, hchain⟩ := hpos hk
  exact ⟨cs, hlen, hnd, hchain⟩

/-- The memory frame: everything outside the scores, base and remaining
regions is preserved. -/
theorem cert_frame {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    SameOutside3 μ μ' sb P bb I mb P := by
  obtain ⟨cs, -, -, -, -, hframe, -, -⟩ := hpost
  exact hframe

/-- With zero restarts the caller's memory is untouched. -/
theorem cert_zero {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hk : k = 0)
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    μ' = μ := by
  obtain ⟨cs, -, -, -, -, -, hzero, -⟩ := hpost
  exact hzero hk

/-! ## The mask count

The certification finish consumes a pool scalar; computing it is the
enclosing controller's job. This is the computation: the surviving flags are
the flagged candidates minus the chosen restarts. -/

/-- Mask count: after `k` distinct flagged restarts, exactly
`(flagged P remaining).card - k` candidates survive. -/
theorem cert_pool {P k : ℕ} {remaining : ℕ → Bool} {cs : List ℕ}
    (hlen : cs.length = k) (hnd : cs.Nodup)
    (hmem : ∀ c ∈ cs, c < P ∧ remaining c = true) :
    ((Finset.range P).filter (fun p => maskCleared cs.toFinset remaining p)).card
      = (flagged P remaining).card - k := by
  have hsub : cs.toFinset ⊆ flagged P remaining := by
    intro a ha
    have ha' : a ∈ cs := List.mem_toFinset.mp ha
    simp only [flagged, Finset.mem_filter, Finset.mem_range]
    exact ⟨(hmem a ha').1, (hmem a ha').2⟩
  have hcard : cs.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have hfilter : (Finset.range P).filter (fun p => maskCleared cs.toFinset remaining p)
      = flagged P remaining \ cs.toFinset := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, flagged, maskCleared]
    simp
    tauto
  rw [hfilter, Finset.card_sdiff_of_subset hsub, hcard]

end Light.DenseCompositeCaller

#print axioms Light.DenseCompositeCaller.certTask_pre
#print axioms Light.DenseCompositeCaller.cert_meets
#print axioms Light.DenseCompositeCaller.cert_solvedIn
#print axioms Light.DenseCompositeCaller.cert_post
#print axioms Light.DenseCompositeCaller.cert_chosen
#print axioms Light.DenseCompositeCaller.cert_mask
#print axioms Light.DenseCompositeCaller.cert_scores
#print axioms Light.DenseCompositeCaller.cert_row
#print axioms Light.DenseCompositeCaller.cert_argmin
#print axioms Light.DenseCompositeCaller.cert_frame
#print axioms Light.DenseCompositeCaller.cert_zero
#print axioms Light.DenseCompositeCaller.cert_pool
