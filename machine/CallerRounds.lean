import MinPlusCaller
import CallerBody

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
session (a): the mpRounds schedule shape and the one-round threading.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds this schedule drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# Session (a): the mpRounds schedule shape + the one-round threading

- `roundCalls` — the schedule's call-sequence shape: `n` certified stage
  calls at the caller program's stage slot (procedure 6 of the round
  program, `stageProcIn` inside the caller program). The caller-side
  generalization of the loop file's own `loopBody` (which chains the same
  call at procedure 5).
- `roundCalls_add_two` — the two-round block shape: the schedule factors
  into `thread_step`'s two-call blocks.
- `mpRounds_even` — the schedule's round count is even
  (`mpRounds_eq`: `mpRounds W = 2 * ((2 * W).log2 + 1)`), so the whole
  schedule is a whole number of two-round blocks.
- `thread_one` — THE KEYSTONE: one certified stage call threaded through
  the caller's state, with the EVOLUTION-EXPOSING post — the run's
  continuation exposes the chosen list and evolved memory exactly as the
  pinned post carries them (`pinnedPost`), which is what the round-chain
  induction needs to feed the next round's slots (`thread_step`'s
  frame-only post hides them). The safe/map socket closes definitionally
  (the nine `v`-registers; `callArgs_cost`), mirroring piece 2's
  calling-convention closes.
- `ChainTarget` — the session's remaining target, stated as a definition:
  the mpRounds schedule's round-chain `Ends` at the caller program with
  the frame post. The induction over round-pairs (base: `thread_one`;
  step: compose through the evolved mask/flags via the pinned-post
  extraction) is the next session's core; (b)'s Post assembly consumes
  its conclusion.

BOUNDARY (unchanged): no (min,+) product is claimed; the oracle premise
is upstream's own shape (`DenseOracleCorrect`-conditioned). D7's boundary
stands.
-/

namespace ThinMatrix.CallerRounds

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerBody

/-! ## The schedule's call-sequence shape -/

/-- The schedule's call sequence: `n` certified stage calls at the round
program's procedure 6 (the L5/L6 pinning), each threading the evolved
state. The caller-side generalization of the loop file's `loopBody`. -/
def roundCalls : ℕ → Stmt
  | 0 => .skip
  | n + 1 => .call 6 callArgs Tmp ;; roundCalls n

/-- The one-call unfolding. -/
theorem roundCalls_succ (n : ℕ) :
    roundCalls (n + 1) = (.call 6 callArgs Tmp ;; roundCalls n) := rfl

/-- The two-round block: the schedule factors into `thread_step`'s
two-call blocks. -/
theorem roundCalls_add_two (n : ℕ) :
    roundCalls (n + 2) =
      (.call 6 callArgs Tmp ;; .call 6 callArgs Tmp ;; roundCalls n) := rfl

/-- The schedule's round count is even — `mpRounds W` two-call blocks
whole (`mpRounds_eq`: `mpRounds W = 2 * ((2 * W).log2 + 1)`). -/
theorem mpRounds_even (W : ℕ) : ∃ h : ℕ, mpRounds W = 2 * h :=
  ⟨(2 * W).log2 + 1, mpRounds_eq W⟩

/-! ## The one-round threading (the chain's keystone) -/

/-- One certified stage call threaded through the caller's state, with
the EVOLUTION-EXPOSING post: the run's continuation state is the
`Tmp`-updated frame with the evolved memory, and the pinned post carries
the chosen list, the cleared mask and the memory frame exactly as the
round-chain induction consumes them. Premises are round 1's certified
slot (`h1`, `stageSlot_any`'s shape at any pinning) plus the caller's
depth and time budget. -/
theorem thread_one
    {lim : Limits} {d : ℕ}
    {P k₁ I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {T₁ T : ℕ} {μ₀ : ℕ → ℤ}
    (hdim : d < lim.depth)
    (hT : 9 + 2 + T₁ ≤ T)
    (h1 : Meets lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [])
      6 (d + 1) (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ₀ T₁
      (pinnedPost (callSite P k₁ I h active remaining rows ab rb sb mb bb) μ₀ fr))
    (R : Light.Program) :
    Ends lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ R)
      d
      (.call 6 callArgs Tmp)
      ⟨frame (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]), μ₀⟩ T
      (fun σ' => ∃ (r₁ : ℤ) (μ₁ : ℕ → ℤ),
        σ' = ⟨Function.update (frame (argsOf (callSite P k₁ I h active remaining rows
          ab rb sb mb bb) ++ [(fr : ℤ)])) Tmp r₁, μ₁⟩ ∧
        pinnedPost (callSite P k₁ I h active remaining rows ab rb sb mb bb) μ₀ fr r₁ μ₁) := by
  refine Ends.callLast (Meets.append h1 R) (fun r₁ μ₁ hR => ⟨r₁, μ₁, rfl, hR⟩) ⟨?_, rfl⟩ hdim ?_
  · intro e he
    simp only [callArgs, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact absurd h (by simp)
  · rw [callArgs_cost]
    omega

/-! ## The chain target (stated; the induction is the next session) -/

/-- The session's remaining target — the mpRounds schedule's round-chain
`Ends` at the caller program: the whole schedule run threads the evolved
state and preserves the caller's three regions (the frame). Stated as a
definition; the induction over round-pairs (base: `thread_one`; step:
compose through the evolved mask/flags via the pinned-post extraction)
discharges it, and (b)'s Post assembly consumes its conclusion. -/
def ChainTarget
    {lim : Limits} {d : ℕ}
    {P k₁ I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {T : ℕ} {μ₀ : ℕ → ℤ}
    (W : ℕ) (R : Light.Program) : Prop :=
  Ends lim (program (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ R)
    d
    (roundCalls (mpRounds W))
    ⟨frame (argsOf (callSite P k₁ I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]), μ₀⟩ T
    (fun σ' => SameOutside3 μ₀ σ'.mem sb P bb I mb P)

#print axioms roundCalls_succ
#print axioms roundCalls_add_two
#print axioms mpRounds_even
#print axioms thread_one

end ThinMatrix.CallerRounds
