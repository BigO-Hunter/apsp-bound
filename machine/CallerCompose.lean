import MinPlusCaller
import ThreeSumApsp.Lang.Renumber

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3, piece 1 — the
renumbering keystone.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds this composition drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language and its renumbering machinery (`Stmt.shift`,
  `Program.behind`) are the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement and the checked
  selection round / restart-loop driver the rounds instantiate.
- Hrishik Sai Bojnal — the verified frontier being refined.

# FILL 3, piece 1: the renumbering keystone

`Ends` is deliberately not prepend-stable: a cache-first program layout
shifts the driver's internal procedure indices (the loop calls procedure 5
of `program cs`). The Lang's renumbering machinery is the sanctioned route:
`Program.behind cacheProg P = cacheProg ++ P.map (Stmt.shift cacheProg.length)`
re-targets every internal call, and

- `Program.getElem?_behind_right` re-indexes the procedure lookup,
- `Ends.shift` / `Ends.shift_append` transport the run.

`stageMeets_behind` is the keystone: the certified stage slot
(`stageSlot_any`'s `Meets`, byte-identical premises) re-indexed into the
composed round program `roundProgram cacheProg rest cs` at procedure
`cacheProg.length + 6`, with the shifted body. `stageEnds_behind_append`
adds the trailing-append stability the schedule threading composes over.

The schedule threading itself (`mpRounds` rounds with round-to-round state
threading — the mask/flags evolve per round) is the remaining FILL 3 mass;
it composes `stageMeets_behind` per round. D7's boundary stands.
-/

namespace ThinMatrix.CallerCompose

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light.DenseCompositeCaller
  Light.DenseCompositeLedger Light.DenseMinPlusPost Light

/-- The composed round program: the cache/restore procedures placed BEHIND
the driver's six and the trailing `rest`, with every internal call index
shifted by `cacheProg.length` (`Program.behind` — the sanctioned route;
`Ends` is not prepend-stable). -/
def roundProgram (cacheProg rest : Program) (cs : Inst) : Program :=
  Program.behind cacheProg (program cs ++ rest)

/-- THE KEYSTONE: the certified stage slot, renumbered into the composed
round program. The premises are byte-identical to `stageSlot_any`'s; the
procedure is `cacheProg.length + 6` and the body is shifted. -/
theorem stageMeets_behind (P k I h : ℕ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (ab rb sb mb bb fr : ℕ) (lim : Limits) (d : ℕ)
    (μ : ℕ → ℤ) (cacheProg rest : Program)
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
      (callSite P k I h active remaining rows ab rb sb mb bb).height).Ok lim fr d) :
    Meets lim (roundProgram cacheProg rest
        (callSite P k I h active remaining rows ab rb sb mb bb))
      (cacheProg.length + 6) d
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
      (taskTime (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
        (callSite P k I h active remaining rows ab rb sb mb bb).height)
      (pinnedPost (callSite P k I h active remaining rows ab rb sb mb bb) μ fr) := by
  obtain ⟨body, hb, hE⟩ := stageSlot_any P k I h active remaining rows ab rb sb
    mb bb fr lim d μ rest hAR hRR hbound hfl hR hlay hok
  refine ⟨body.shift cacheProg.length, ?_, Ends.shift hE cacheProg⟩
  rw [Nat.add_comm]
  exact Program.getElem?_behind_right cacheProg hb

/-- The keystone's run persists under a further trailing append — the form
the schedule threading composes over. -/
theorem stageEnds_behind_append (P k I h : ℕ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (ab rb sb mb bb fr : ℕ) (lim : Limits) (d : ℕ)
    (μ : ℕ → ℤ) (cacheProg rest rest' : Program)
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
      (callSite P k I h active remaining rows ab rb sb mb bb).height).Ok lim fr d) :
    ∃ body : Stmt,
      (roundProgram cacheProg rest
        (callSite P k I h active remaining rows ab rb sb mb bb))[cacheProg.length + 6]?
        = some body ∧
      Ends lim (roundProgram cacheProg rest
        (callSite P k I h active remaining rows ab rb sb mb bb) ++ rest') d body
        ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]), μ⟩
        (taskTime (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
          (callSite P k I h active remaining rows ab rb sb mb bb).height)
        fun σ' => pinnedPost (callSite P k I h active remaining rows ab rb sb mb bb) μ fr (σ'.loc 0) σ'.mem := by
  have hm := stageMeets_behind P k I h active remaining rows ab rb sb mb bb fr
    lim d μ cacheProg rest hAR hRR hbound hfl hR hlay hok
  obtain ⟨body, hb, hE⟩ := hm
  exact ⟨body, hb, Ends.append hE rest'⟩

#print axioms roundProgram
#print axioms stageMeets_behind
#print axioms stageEnds_behind_append

end ThinMatrix.CallerCompose
