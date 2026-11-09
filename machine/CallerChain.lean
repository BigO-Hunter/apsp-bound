import MinPlusCaller
import CallerRounds

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
session (a′): the round-chain induction.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds this chain drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# Session (a′): the round-chain induction — ChainTarget closed

- `StageReads` — the stage's read bundle: active bits, rows table, plain
  flags at the current mask.
- `reads_carry` — the frame-carried reads: the round's pinned post
  preserves the active/rows reads (they lie below the scores region — the
  layout, omega) and re-states the flag reads at the cleared mask
  (the post's own clause). This is thread_step's evolved-read extraction,
  packaged once and reused by every round of the chain.
- `chain_from` — THE INDUCTION: from a uniform per-round slot family
  (`hslots`: for every flag state, restart pinning and memory satisfying
  the reads — plus the flag budget and the Ok fit — the round's certified
  slot meets within its pinned clock), the mpRounds schedule's round
  sequence threads the evolved state and preserves the caller's three
  regions. Base: the skip's reflexive frame (`Ends.skip` + `SameOn.refl`).
  Step: `Ends.callThen` on the round's slot; the continuation extracts the
  round's outcome from the pinned-post witness (the
  `obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, -, -⟩` pattern), carries the
  reads by `reads_carry`, re-enters the induction at the cleared mask, and
  bridges the frame anchor through the post's `SameOutside3`
  (`Ends.mono` + `SameOn`-transitivity). The calling-convention socket
  closes definitionally at every step (the nine `v`-registers; the
  `Tmp`-updates touch no argument register — piece 2's closes, at every
  nested-update frame).
- `chain_runs` — the session's target: `ChainTarget` (the mpRounds
  schedule's round-chain `Ends` at the caller program with the frame
  post) discharged by the induction at the schedule's own round count
  (the first round glued manually at the plain frame, the rest by
  `chain_from`). This is the premise (b)'s Post assembly consumes.

BOUNDARY (unchanged): no (min,+) product is claimed; the oracle premise
is upstream's own shape (`DenseOracleCorrect`-conditioned). D7's boundary
stands.
-/

namespace ThinMatrix.CallerChain

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerRounds

/-! ## The stage's read bundle -/

/-- The stage's reads: active bits at the active base, the rows table at
the rows base, plain flag bits at the remaining base — all at the current
flag state `mask`. -/
def StageReads (P I : ℕ) (active mask : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (ab rb mb : ℕ) (μ : ℕ → ℤ) : Prop :=
  (∀ i < I, μ (ab + i) = DenseScorePass.bit (active i)) ∧
  (∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i) ∧
  (∀ p < P, μ (mb + p) = DenseArgminPass.bit (mask p))

/-- The frame-carried reads: the round's pinned post preserves the
active/rows reads (they lie below the scores region — the layout) and
re-states the flag reads at the cleared mask (the post's own clause). -/
theorem reads_carry
    {P I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {cs₁ : List ℕ} {μ μ₁ : ℕ → ℤ}
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hreads : StageReads P I active remaining rows ab rb mb μ)
    (hsam : SameOutside3 μ μ₁ sb P bb I mb P)
    (hmask : ∀ p < P, μ₁ (mb + p) = DenseArgminPass.bit (maskCleared cs₁.toFinset remaining p)) :
    StageReads P I active (maskCleared cs₁.toFinset remaining) rows ab rb mb μ₁ := by
  refine ⟨fun i hi => ?_, fun p hp i hi => ?_, hmask⟩
  · rw [hsam (ab + i) ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
    exact hreads.1 i hi
  · have hlt : p * I + i < P * I := by nlinarith
    rw [hsam (rb + p * I + i) ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
    exact hreads.2.1 p hp i hi

/-! ## The round-chain induction -/

/-- THE INDUCTION: from a uniform per-round slot family, the schedule's
round sequence threads the evolved state and preserves the caller's three
regions. The slot family is the caller's contract: for every flag state,
restart pinning and memory satisfying the reads — plus the flag budget
and the Ok fit — the round's certified slot meets within its pinned
clock, in the driver's own program (piece 2's correction, family form).
The per-round time budget `B` dominates every slot's clock; the total
budget shrinks by it each round. -/
theorem chain_from (n : ℕ)
    {lim : Limits} {d : ℕ}
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {B : ℕ} {Tt : ℕ → ℕ} {R : Light.Program}
    (hdim : d < lim.depth)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hslots : ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
      StageReads P I active mask rows ab rb mb μ →
      kt ≤ (flagged P mask).card →
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        6 (d + 1) (argsOf (callSite P kt I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
        (Tt kt)
        (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr))
    (hTt : ∀ kt : ℕ, 9 + 2 + Tt kt ≤ B)
    (hflag : ∀ mask : ℕ → Bool, k ≤ (flagged P mask).card)
    (hok : ∀ (mask : ℕ → Bool) (kt : ℕ),
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1)) :
    ∀ (r₀ : ℤ) (T : ℕ), n * B ≤ T → ∀ (l : ℕ → ℤ) (mask : ℕ → Bool) (μ : ℕ → ℤ),
      (∀ k < 9, l k =
        (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]).getD k 0) →
      StageReads P I active mask rows ab rb mb μ →
      Ends lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        d (roundCalls n) ⟨l, μ⟩ T
        (fun σ' => SameOutside3 μ σ'.mem sb P bb I mb P) := by
  induction n with
  | zero =>
    intro r₀ T hT l mask μ hloc hreads
    rw [roundCalls]
    exact Ends.skip SameOn.refl
  | succ n ih =>
    intro r₀ T hT l mask μ hloc hreads
    have hBlin : B ≤ (n + 1) * B :=
      Nat.le_mul_of_pos_left B (Nat.succ_pos n)
    rw [roundCalls_succ]
    refine Ends.callThen (hslots mask k μ hreads (hflag mask) (hok mask k))
      (fun r₁ μ₁ hR => ?_) ⟨fun e he => ?_, ?_⟩ hdim ?_
    · obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, -, -⟩ := hR
      have hTlin : (n + 1) * B = n * B + B := by ring
      have h1 : n * B + B ≤ T := by rw [hTlin] at hT; exact hT
      have h2 : n * B + (9 + 2 + Tt k) ≤ n * B + B :=
        Nat.add_le_add_left (hTt k) (n * B)
      have hbudget : n * B ≤ T - (9 + 2 + Tt k) := by omega
      have hmono : (T - (9 + 2 + Tt k)) ≤
          (T - ((List.map Expr.cost callArgs).sum + 2 + Tt k)) := by
        rw [callArgs_cost]
      have hupd : ∀ k < 9, Function.update l 10 r₁ k = l k := by
        intro k hk
        have h10 : ¬(k = 10) := by omega
        exact dif_neg h10
      refine (ih r₁ (T - (9 + 2 + Tt k)) hbudget (Function.update l 10 r₁)
        (maskCleared cs₁.toFinset mask) μ₁
        (fun k hk => by rw [hupd k hk]; exact hloc k hk)
        (reads_carry (h := h) hlay hreads hsam hmask)).mono hmono
        (fun σ'' hσ'' => SameOn.trans hsam hσ'')
    · simp only [callArgs, List.mem_cons] at he
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
    · -- the map socket: the loc holds the round registers on 0–8
      have hlits : callArgs.map (fun e => e.val ⟨l, μ⟩) =
          [l Candidates, l Len, l Height, l Active, l Rows, l Scores, l Remaining,
            l Base, l Free] := rfl
      rw [hlits, hloc 0 (by omega), hloc 1 (by omega), hloc 2 (by omega),
        hloc 3 (by omega), hloc 4 (by omega), hloc 5 (by omega),
        hloc 6 (by omega), hloc 7 (by omega), hloc 8 (by omega)]
      rfl
    · rw [callArgs_cost]
      have hTtk := hTt k
      omega

/-! ## The session target: ChainTarget discharged -/

/-- THE SESSION TARGET: the mpRounds schedule's round-chain `Ends` at the
caller program — `ThinMatrix.CallerRounds.ChainTarget` — discharged by the
induction at the schedule's own round count (the first round glued
manually at the plain frame, the rest by `chain_from`; the count's budget
is the schedule's own `mpRounds`-fold round budget). -/
theorem chain_runs (r₀ : ℤ)
    {lim : Limits} {d : ℕ}
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ} {μ₀ : ℕ → ℤ} {R : Light.Program} (W : ℕ)
    (hdim : d < lim.depth)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hslots : ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
      StageReads P I active mask rows ab rb mb μ →
      kt ≤ (flagged P mask).card →
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        6 (d + 1) (argsOf (callSite P kt I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
        (Tt kt)
        (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr))
    (hTt : ∀ kt : ℕ, 9 + 2 + Tt kt ≤ B)
    (hflag : ∀ mask : ℕ → Bool, k ≤ (flagged P mask).card)
    (hok : ∀ (mask : ℕ → Bool) (kt : ℕ),
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hreads₀ : StageReads P I active remaining rows ab rb mb μ₀)
    (hT : mpRounds W * B ≤ T) :
    @ThinMatrix.CallerRounds.ChainTarget lim d P k I h active remaining rows
      ab rb sb mb bb fr T μ₀ W R := by
  unfold ThinMatrix.CallerRounds.ChainTarget
  have h2 : 2 ≤ mpRounds W := by
    rw [mpRounds_eq W]
    have hpos := Nat.succ_pos (2 * W).log2
    omega
  have hBle : 2 * B ≤ mpRounds W * B := by
    rw [Nat.mul_comm 2 B, Nat.mul_comm (mpRounds W) B]
    exact Nat.mul_le_mul_left B h2
  have hTtk : 9 + 2 + Tt k ≤ B := hTt k
  have hmul : mpRounds W * B = (mpRounds W - 2) * B + 2 * B := by
    rw [Nat.sub_mul]
    exact (Nat.sub_add_cancel hBle).symm
  have hsplit : roundCalls (mpRounds W) =
      (.call 6 callArgs Tmp ;; .call 6 callArgs Tmp ;;
        roundCalls (mpRounds W - 2)) := by
    have h2' : mpRounds W = (mpRounds W - 2) + 2 := by omega
    rw [h2', roundCalls_add_two, Nat.add_sub_cancel]
  rw [hsplit]
  -- the first two rounds glue manually at the plain frame; the rest is
  -- the induction at the twice-updated state
  refine Ends.callThen (hslots remaining k μ₀ hreads₀ (hflag remaining) (hok remaining k))
    (fun r₁ μ₁ hR => ?_) ⟨fun e he => ?_, rfl⟩ hdim ?_
  · obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, -, -⟩ := hR
    have hreads₁ : StageReads P I active (maskCleared cs₁.toFinset remaining) rows
        ab rb mb μ₁ :=
      reads_carry (h := h) hlay hreads₀ hsam hmask
    refine Ends.callThen (hslots (maskCleared cs₁.toFinset remaining) k μ₁ hreads₁
      (hflag (maskCleared cs₁.toFinset remaining)) (hok (maskCleared cs₁.toFinset remaining) k))
      (fun r₂ μ₂ hR₂ => ?_) ⟨fun e he => ?_, rfl⟩ hdim ?_
    · obtain ⟨cs₂, -, -, -, hmask₂, hsam₂, -, -⟩ := hR₂
      have hreads₂ : StageReads P I active
          (maskCleared cs₂.toFinset (maskCleared cs₁.toFinset remaining)) rows ab rb mb μ₂ :=
        reads_carry (h := h) hlay hreads₁ hsam₂ hmask₂
      have hsub : (mpRounds W - 2) * B ≤
          T - (9 + 2 + Tt k) - (9 + 2 + Tt k) := by omega
      have hmono : (T - (9 + 2 + Tt k) - (9 + 2 + Tt k)) ≤
          (T - (9 + 2 + Tt k) - ((List.map Expr.cost callArgs).sum + 2 + Tt k)) := by
        rw [callArgs_cost]
      refine (chain_from (mpRounds W - 2) hdim hbound hlay hslots hTt hflag hok r₂
        (T - (9 + 2 + Tt k) - (9 + 2 + Tt k)) hsub
        (Function.update (Function.update (frame (argsOf (callSite P k I h active remaining rows
          ab rb sb mb bb) ++ [(fr : ℤ)])) 10 r₁) Tmp r₂)
        (maskCleared cs₂.toFinset (maskCleared cs₁.toFinset remaining)) μ₂
        (fun k hk => by
          have h10 : ¬(k = 10) := by omega
          exact Eq.trans (dif_neg h10) (Eq.trans (dif_neg h10) rfl))
        hreads₂).mono hmono
        (fun σ'' hσ'' => SameOn.trans (SameOn.trans hsam hsam₂) hσ'')
    · simp only [callArgs, List.mem_cons] at he
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
  · simp only [callArgs, List.mem_cons] at he
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

#print axioms reads_carry
#print axioms chain_from
#print axioms chain_runs

end ThinMatrix.CallerChain
