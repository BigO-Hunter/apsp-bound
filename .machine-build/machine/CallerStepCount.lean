import MinPlusCaller
import CallerPost

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the step-count session: the budget structure B / Tt / 9+2 over mpRounds,
the caller's need, and the `completeCost` domination.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds this budget drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language and the `AsymptoticCosts` complete-cost ledger are the
  pinned statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations
  record; the tight stage clock is the selection round's own cost
  comparison (`time <= 25*(P*I + 6*P + I)`).
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The step count: the B / Tt / 9+2 budget and the CallerHdom domination

The product-round body's clock (PRODUCT_BODY.md §6): per round, the
call's argument cost 9 (`callArgs_cost`) + the call overhead 2 + the tight
stage clock `callerTt` (the selection round's cost comparison at the
concretized pinning `P = I = n`) + the row pass (`x.n` stores at
`callerBw = 5` each: two `var`s, an `op`, a `var`, the store) + one step
of slack. The total:

- `callerTn n U := mpRounds U * callerB n` — logarithmic in U (the
  schedule, `mpRounds U = 2·((2U).log2 + 1)`), quadratic in n.
- `callerHdom : CallerHdom callerTn` — the host's lifted clock
  `apTime Tn = Nat.clog 2 n * (Tn n (3nU) + 23n² + 29) + …` is
  `O(n² · log² n)` per fixed κ, and `completeCost k n` carries
  `log^(k+R+10) n · n²` with `R = 10⁹` — k := 0 dominates eventually.
- `callerNeed` + `callerNeed_poly` — the resource need (the scratch
  layout `n² + 4n + 8` cells, the word bound, depth 2) and its polynomial
  witness — the summit's `hn` socket.

D7's boundary stands: no (min,+) product is claimed; the tight-clock slot
family (`hslots` at `callerTt`) is a named premise of the assembly module
(PRODUCT_BODY.md §4, Tier-B).
-/

namespace ThinMatrix.CallerStepCount

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerPost

/-! ## The budget structure -/

/-- The tight stage clock at the concretized pinning `P = I = n`: the
selection round's cost comparison `time ≤ 25·(P·I + 6·P + I)` at
`P = I = n` (MACHINE_OBLIGATIONS' "cost comparison" row). -/
def callerTt (n : ℕ) : ℕ := 25 * (n * n + 6 * n + n)

/-- The row pass's per-store bound: the address `v Out +' v Idx` (two
`var`s and an `op`), the value `v (Tmp + u)` (one `var`), the store. -/
def callerBw : ℕ := 5

/-- The per-round budget: the call's arguments (9, `callArgs_cost`), the
call overhead (2), the tight stage clock, the row pass, and one step of
slack. -/
def callerB (n : ℕ) : ℕ := 9 + 2 + callerTt n + callerBw * n + 1

/-- The caller's clock: `mpRounds U` rounds at the per-round budget. -/
def callerTn (n U : ℕ) : ℕ := mpRounds U * callerB n

/-- The schedule is at most `2·log₂ U + 6`. -/
theorem mpRounds_le_two_log_succ (U : ℕ) :
    mpRounds U ≤ 2 * Nat.log2 U + 6 := by
  rw [mpRounds_eq]
  rcases Nat.eq_zero_or_pos U with h0 | h0
  · subst h0; simp
  · have h2 : Nat.log2 (2 * U) = Nat.log2 U + 1 := by
      have h1 : Nat.log 2 (2 * U) = Nat.log 2 U + 1 := by
        rw [Nat.mul_comm]
        exact Nat.log_mul_base (by norm_num) (ne_of_gt h0)
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact h1
    omega

/-- The wire's per-round socket: the call's arguments, the overhead, the
tight stage clock, and the row pass fit the budget. -/
theorem hround_budget (n : ℕ) :
    (callArgs.map Expr.cost).sum + 2 + callerTt n + n * callerBw
      ≤ callerB n := by
  rw [callArgs_cost]
  simp only [callerB, callerTt, callerBw]
  omega

/-- The chain's per-round slot clock fits the budget (the shape
`chain_from` consumes). -/
theorem hTt_budget (n _kt : ℕ) : 9 + 2 + callerTt n ≤ callerB n := by
  simp only [callerB, callerTt, callerBw]
  omega

/-- The per-store cost socket: every row-pass store costs at most
`callerBw` steps. -/
theorem hcost_budget (Out Idx u : ℕ) :
    (v Out +' v (Idx + u)).cost + (v (Tmp + u)).cost + 1 ≤ callerBw := by
  simp only [callerBw, Expr.cost]
  omega

/-- The caller's clock bounds the schedule at the budget: the shape the
wire's `hT` consumes. -/
theorem hT_budget (n U : ℕ) : mpRounds U * callerB n ≤ callerTn n U :=
  le_refl _

/-- The budget is quadratic. -/
theorem callerB_le (n : ℕ) (hn : 1 ≤ n) : callerB n ≤ 217 * n * n := by
  have h1 : n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
  simp only [callerB, callerTt, callerBw]
  have h2 : 5 * n ≤ 5 * (n * n) := by nlinarith
  have h3 : 6 * n ≤ 6 * (n * n) := by nlinarith
  nlinarith

/-! ## The caller's need -/

/-- The caller's resource need: the scratch layout (`n² + 4n + 8` cells —
the five buffers at the caller's free pointer), the word bound, depth 2
(the entry procedure plus the certified stage call). -/
def callerNeed (a U : ℕ) : Light.Need where
  word := 6 * (a * U) + 64
  cells := a * a + 4 * a + 8
  depth := 2

/-- The need is polynomially bounded — the summit's `hn` socket. -/
theorem callerNeed_poly : Light.PolyNeed callerNeed := by
  refine ⟨7, 2, ?_⟩
  intro n U
  simp only [polyBound, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, Nat.mul_one]
  have hq1 : 1 ≤ (n + 1) * (U + 1) := by nlinarith
  constructor
  · -- the word bound: 6·n·U + 64 ≤ 6·q² + 64·q² = 70·q² ≤ 128·q²
    have hw1 : n * U ≤ ((n + 1) * (U + 1)) ^ 2 := by
      have hle : ((n + 1) * (U + 1)) ^ 2
          = ((n + 1) * (U + 1)) * ((n + 1) * (U + 1)) := by ring
      nlinarith
    have hw : 6 * (n * U) + 64 ≤ 70 * ((n + 1) * (U + 1)) ^ 2 := by
      have h64 : (64 : ℕ) ≤ 64 * ((n + 1) * (U + 1)) ^ 2 := by nlinarith
      nlinarith
    calc (callerNeed n U).word
        = 6 * (n * U) + 64 := rfl
      _ ≤ 70 * ((n + 1) * (U + 1)) ^ 2 := hw
      _ ≤ 2 ^ 7 * ((n + 1) * (U + 1)) ^ 2 := by nlinarith
  · constructor
    · -- the cells bound: n² + 4n + 8 ≤ 13·q² ≤ 128·q²
      have hc1 : n ≤ (n + 1) * (U + 1) := by nlinarith
      have hc2 : n * n ≤ ((n + 1) * (U + 1)) ^ 2 := by
        have hle : ((n + 1) * (U + 1)) ^ 2
            = ((n + 1) * (U + 1)) * ((n + 1) * (U + 1)) := by ring
        have := Nat.mul_le_mul hc1 hc1
        nlinarith
      have hc : n * n + 4 * n + 8 ≤ 13 * ((n + 1) * (U + 1)) ^ 2 := by
        have hc3 : 4 * n ≤ 4 * ((n + 1) * (U + 1)) ^ 2 := by nlinarith
        have hc4 : (8 : ℕ) ≤ 8 * ((n + 1) * (U + 1)) ^ 2 := by nlinarith
        nlinarith
      calc (callerNeed n U).cells
          = n * n + 4 * n + 8 := rfl
        _ ≤ 13 * ((n + 1) * (U + 1)) ^ 2 := hc
        _ ≤ 2 ^ 7 * ((n + 1) * (U + 1)) ^ 2 := by nlinarith
    · -- the depth bound
      calc (callerNeed n U).depth
          = 2 := rfl
        _ ≤ 2 ^ 7 * ((n + 1) * (U + 1)) ^ 2 := by nlinarith

/-! ## The completeCost domination -/

/-- `1/2 < log 2`, from the pinned bound `exp 1 < 2.718… < 4`:
`1 = log (exp 1) < log 4 = 2·log 2`. -/
private theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h4 : Real.exp 1 < (4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h1 : Real.log (Real.exp 1) < Real.log 4 :=
    Real.log_lt_log (Real.exp_pos 1) h4
  rw [Real.log_exp, (by norm_num : (4 : ℝ) = 2 * 2),
    Real.log_mul (by norm_num) (by norm_num)] at h1
  linarith

/-- The binary log sits below twice the natural log (from `n ≥ 2`):
`2^(log₂ n) ≤ n` and `log 2 > 1/2` give `log₂ n · log 2 ≤ log n`. -/
private theorem log2_le_two_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hspec : ((2 : ℕ) ^ Nat.log2 n : ℕ) ≤ n := by
    have h := Nat.pow_log_le_self (b := 2) (x := n) (by omega)
    rwa [Nat.log2_eq_log_two.symm] at h
  have hcast : ((2 : ℝ) ^ (Nat.log2 n : ℕ)) ≤ (n : ℝ) := by
    exact_mod_cast hspec
  have hmono : Real.log ((2 : ℝ) ^ (Nat.log2 n : ℕ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hcast
  have hpow : Real.log ((2 : ℝ) ^ (Nat.log2 n : ℕ))
      = (Nat.log2 n : ℝ) * Real.log 2 := Real.log_pow 2 _
  nlinarith [half_lt_log_two]

/-- `Nat.clog 2` is one past the binary log. -/
private theorem clog_two_le (n : ℕ) :
    Nat.clog 2 n ≤ Nat.log2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have h0c := Nat.clog_of_right_le_one (n := 0) (by omega) 2
    omega
  · have hlt : n < (2 : ℕ) ^ (Nat.log2 n + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      have h2 : Nat.log 2 n = Nat.log2 n := Nat.log2_eq_log_two.symm
      rwa [h2, Nat.succ_eq_add_one] at h
    have := Nat.clog_le_of_le_pow (b := 2) (Nat.le_of_lt hlt)
    omega

set_option maxHeartbeats 2000000 in
/-- The `completeCost` lower bound at `k = 0`: the ledger carries
`(R+1)² · log^(R+10) n · n²` from its own first summand — the other
terms are natural-number ceilings, so they only add. -/
theorem completeCost_ge_log_sq (n : ℕ) (hn : 8 ≤ n) :
    ((n : ℝ) * (n : ℝ)) * (Real.log (n : ℝ)) ^ 2
      ≤ AsymptoticCosts.completeCost 0 n := by
  have hlog1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have h8 : Real.log 8 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h8' : (1 : ℝ) ≤ Real.log 8 := by
      have hp : Real.log ((2 : ℝ) ^ 3) = 3 * Real.log 2 := Real.log_pow 2 3
      rw [(by norm_num : ((2 : ℝ) ^ 3) = 8)] at hp
      have := half_lt_log_two
      linarith
    nlinarith
  have hrp : AsymptoticCosts.roundedPower 2 n = ((n : ℝ) * (n : ℝ)) := by
    have h : Nat.ceil ((n : ℝ) * (n : ℝ)) = n * n := by
      rw [← Nat.cast_mul]
      exact Nat.ceil_natCast (n * n)
    unfold AsymptoticCosts.roundedPower
    rw [Real.rpow_two, pow_two, h]
    push_cast
    ring
  -- the real-square as the ledger's first summand
  have hx2 : ((n : ℝ) * (n : ℝ)) = AsymptoticCosts.roundedPower 2 n := hrp.symm
  have hW : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by positivity
  -- the ledger's terms beyond the first summand are nonnegative
  have hrest : (0 : ℝ) ≤ AsymptoticCosts.roundedPower
      (3 - (AsymptoticCosts.b - AsymptoticCosts.eta)) n +
      ∑ j : Fin (AlignedCertificate.R + 1), ∑ i : Fin 6,
        AsymptoticCosts.roundedPower
          (3 - AsymptoticCosts.stageSaving j i) n := by
    refine add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
  have hpow2 : (Real.log (n : ℝ)) ^ 2
      ≤ (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10) := by
    refine pow_right_mono₀ hlog1 ?_
    have hR : (0 : ℕ) ≤ AlignedCertificate.R := Nat.zero_le _
    have h2 : (2 : ℕ) ≤ 0 + AlignedCertificate.R + 10 := by omega
    exact h2
  have hf : (1 : ℝ) ≤ ((AlignedCertificate.R : ℝ) + 1) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (AlignedCertificate.R : ℝ) + 1 := by
      exact_mod_cast (by omega : (0 : ℕ) ≤ AlignedCertificate.R + 1)
    have h2 : (1 : ℝ) ≤ (AlignedCertificate.R : ℝ) + 1 := by
      exact_mod_cast (by omega : (1 : ℕ) ≤ AlignedCertificate.R + 1)
    nlinarith
  have hunfold : (AsymptoticCosts.completeCost 0 n) =
      (((AlignedCertificate.R : ℝ) + 1) ^ 2
        * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10)
        * (AsymptoticCosts.roundedPower 2 n
          + AsymptoticCosts.roundedPower
              (3 - (AsymptoticCosts.b - AsymptoticCosts.eta)) n
          + ∑ j : Fin (AlignedCertificate.R + 1), ∑ i : Fin 6,
              AsymptoticCosts.roundedPower
                (3 - AsymptoticCosts.stageSaving j i) n)) := rfl
  rw [hunfold]
  have hLbig : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10) := by
    refine pow_nonneg ?_ _
    have := hlog1
    linarith
  have hWL : (0 : ℝ) ≤ ((n : ℝ) * (n : ℝ))
      * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10) := mul_nonneg hW hLbig
  calc ((n : ℝ) * (n : ℝ)) * (Real.log (n : ℝ)) ^ 2
      ≤ (1 : ℝ) * ((n : ℝ) * (n : ℝ))
        * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10) := by
        nlinarith
    _ = ((n : ℝ) * (n : ℝ))
        * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10) := by ring
    _ ≤ ((AlignedCertificate.R : ℝ) + 1) ^ 2
        * (((n : ℝ) * (n : ℝ))
          * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10)) := by
        have h1 := mul_le_mul_of_nonneg_right hf hWL
        rw [one_mul] at h1
        exact h1
    _ = ((AlignedCertificate.R : ℝ) + 1) ^ 2
        * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10)
        * ((n : ℝ) * (n : ℝ)) := by ring
    _ ≤ ((AlignedCertificate.R : ℝ) + 1) ^ 2
        * (Real.log (n : ℝ)) ^ (0 + AlignedCertificate.R + 10)
        * (AsymptoticCosts.roundedPower 2 n
          + AsymptoticCosts.roundedPower
              (3 - (AsymptoticCosts.b - AsymptoticCosts.eta)) n
          + ∑ j : Fin (AlignedCertificate.R + 1), ∑ i : Fin 6,
              AsymptoticCosts.roundedPower
                (3 - AsymptoticCosts.stageSaving j i) n) := by
        rw [hx2]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hrest]

set_option maxHeartbeats 2000000 in
/-- The host's lifted clock at the caller's `Tn` is `O(n² · log² n)`,
uniformly over `U ≤ n^κ` — per fixed κ. The constant is generous; only
its κ-linearity matters. -/
theorem apTime_le_sq_log (κ : Nat) (n U : ℕ) (hn3 : 3 ≤ n) (hU : U ≤ n ^ κ) :
    ((Light.Sec3.apTime callerTn n U : ℕ) : ℝ)
      ≤ (4 * (7000 * (κ : ℝ) + 30000))
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hn2 : 2 ≤ n := by omega
  have hnn : (1 : ℝ) ≤ ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n * n := by nlinarith
    exact_mod_cast this
  set L := (Nat.log2 n : ℝ) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    have hb2 : (1 : ℕ) < 2 := by norm_num
    have hpos := Nat.log_pos (b := 2) (n := n) hb2 (by omega)
    rw [← Nat.log2_eq_log_two] at hpos
    have h1n : (1 : ℕ) ≤ Nat.log2 n := hpos
    show (1 : ℝ) ≤ ((Nat.log2 n : ℕ) : ℝ)
    exact Nat.one_le_cast.2 h1n
  have hLn : L ≤ 2 * Real.log (n : ℝ) := log2_le_two_log n hn2
  -- (a) the schedule at the host's bound 3nU: log₂(3nU) ≤ (κ+2)(log₂ n + 1)
  have hlt : n < (2 : ℕ) ^ (Nat.log2 n + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have h2 : Nat.log 2 n = Nat.log2 n := Nat.log2_eq_log_two.symm
    rwa [h2, Nat.succ_eq_add_one] at h
  have hnle : n ^ (κ + 2) ≤ (2 : ℕ) ^ ((κ + 2) * (Nat.log2 n + 1)) := by
    have h1 : n ^ (κ + 2) ≤ ((2 : ℕ) ^ (Nat.log2 n + 1)) ^ (κ + 2) :=
      Nat.pow_le_pow_left (Nat.le_of_lt hlt) _
    rw [← Nat.pow_mul, Nat.mul_comm] at h1
    exact h1
  have h3le : 3 * n * U ≤ n ^ (κ + 2) := by
    have hstep : n ^ (κ + 2) = n ^ κ * (n * n) := by
      rw [Nat.pow_succ, Nat.pow_succ]; ring
    have hmul : U * (n * n) ≤ n ^ κ * (n * n) :=
      Nat.mul_le_mul_right _ hU
    have h3n : 3 * n ≤ n * n := by nlinarith
    calc 3 * n * U ≤ (n * n) * U := by nlinarith
      _ = U * (n * n) := Nat.mul_comm _ _
      _ ≤ n ^ κ * (n * n) := hmul
      _ = n ^ (κ + 2) := hstep.symm
  have hlog3 : Nat.log2 (3 * n * U) ≤ (κ + 2) * (Nat.log2 n + 1) := by
    rcases Nat.eq_zero_or_pos U with hU0 | hU0
    · subst hU0
      simp
    · have hp : (2 : ℕ) ^ (Nat.log2 n + 1)
        ≤ (2 : ℕ) ^ ((κ + 2) * (Nat.log2 n + 1) + 1) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h1 : (1 : ℕ) ≤ κ + 2 := by omega
        have h2 := Nat.le_mul_of_pos_right (Nat.log2 n + 1) h1
        rw [Nat.mul_comm] at h2
        omega
      have hlt2 : 3 * n * U < (2 : ℕ) ^ ((κ + 2) * (Nat.log2 n + 1) + 1) :=
        lt_of_le_of_lt h3le (lt_of_le_of_lt hnle
          (Nat.pow_lt_pow_right (by norm_num) (by omega)))
      have hy0 : (3 : ℕ) * n * U ≠ 0 := by
        exact ne_of_gt (Nat.mul_pos (by omega : (0 : ℕ) < 3 * n) hU0)
      have h := (Nat.log_lt_iff_lt_pow (b := 2) (y := 3 * n * U)
        (by norm_num) hy0).2 hlt2
      rw [Nat.log2_eq_log_two.symm] at h
      linarith
  -- (b) callerTn n (3nU) ≤ (2(κ+2)(L+1) + 6) · 217 n²
  have hpos1 : (0 : ℝ) ≤ ((mpRounds (3 * n * U) : ℕ) : ℝ) := by positivity
  have hpos2 : (0 : ℝ) ≤ ((callerB n : ℕ) : ℝ) := by positivity
  have hcast1 : ((mpRounds (3 * n * U) : ℕ) : ℝ)
      ≤ ((2 * Nat.log2 (3 * n * U) + 6 : ℕ) : ℝ) := by
    have h1 := mpRounds_le_two_log_succ (3 * n * U)
    exact_mod_cast h1
  have h6r : ((2 * Nat.log2 (3 * n * U) + 6 : ℕ) : ℝ)
      ≤ (2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6 := by
    have h1 : ((2 * Nat.log2 (3 * n * U) + 6 : ℕ) : ℝ)
        ≤ ((2 * ((κ + 2) * (Nat.log2 n + 1)) + 6 : ℕ) : ℝ) := by
      refine Nat.cast_le.2 ?_
      omega
    have h2 : ((2 * ((κ + 2) * (Nat.log2 n + 1)) + 6 : ℕ) : ℝ)
        ≤ (2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      push_cast
      linarith
    linarith
  have hTn : ((callerTn n (3 * n * U) : ℕ) : ℝ)
      ≤ ((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
        * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
    have hunfold : ((callerTn n (3 * n * U) : ℕ) : ℝ)
        = ((mpRounds (3 * n * U) : ℕ) : ℝ) * ((callerB n : ℕ) : ℝ) := by
      unfold callerTn; rw [Nat.cast_mul]
    have hBq : ((callerB n : ℕ) : ℝ)
        ≤ (217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
      have := callerB_le n (by omega)
      exact_mod_cast this
    calc ((callerTn n (3 * n * U) : ℕ) : ℝ)
        = ((mpRounds (3 * n * U) : ℕ) : ℝ) * ((callerB n : ℕ) : ℝ) := hunfold
      _ ≤ ((2 * Nat.log2 (3 * n * U) + 6 : ℕ) : ℝ) * ((callerB n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hcast1 hpos2
      _ ≤ ((2 * Nat.log2 (3 * n * U) + 6 : ℕ) : ℝ)
          * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hBq (by positivity)
      _ ≤ ((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
          * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right h6r (by positivity)
  -- (c) the clog step and the constant folds, all into n² L²
  have hclogr : ((Nat.clog 2 n : ℕ) : ℝ) ≤ L + 1 := by
    have h := clog_two_le n
    show ((Nat.clog 2 n : ℕ) : ℝ) ≤ ((Nat.log2 n : ℕ) : ℝ) + 1
    have h2 : (((Nat.log2 n + 1 : ℕ) : ℝ))
        = ((Nat.log2 n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [← h2]
    exact Nat.cast_le.2 h
  have h23 : ((23 * n * n + 29 : ℕ) : ℝ)
      ≤ (52 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
    calc ((23 * n * n + 29 : ℕ) : ℝ)
        ≤ ((52 * (n * n) : ℕ) : ℝ) := by
            refine Nat.cast_le.2 ?_
            nlinarith
      _ = (52 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
            rw [Nat.cast_mul]
            push_cast
            ring
  have htail : ((53 * n * n + 17 * n + 65 : ℕ) : ℝ)
      ≤ (140 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
    calc ((53 * n * n + 17 * n + 65 : ℕ) : ℝ)
        ≤ ((140 * (n * n) : ℕ) : ℝ) := by
            refine Nat.cast_le.2 ?_
            have h1 : n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
            nlinarith
      _ = (140 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
            rw [Nat.cast_mul]
            push_cast
            ring
  -- the fold's atoms (shared by hcore and hmain)
  have hL2 : (L + (1 : ℝ)) ≤ (2 : ℝ) * L := by linarith
  have hL3 : (L : ℝ) ≤ L * L := by nlinarith
  have hκp : (0 : ℝ) ≤ (κ : ℝ) + 2 := by positivity
  have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by positivity
  have hκL1 : (0 : ℝ) ≤ ((κ : ℝ) + 2) * L := mul_nonneg hκp (by linarith)
  -- the fold: 2L·((2(κ+2)(L+1)+6)·217 + 52) + 140 ≤ (7000κ + 30000)·L² for L ≥ 1
  have hcore : ((2 : ℝ) * L) * (((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
        * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
        + (52 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
      + (140 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
      ≤ ((7000 * (κ : ℝ) + 30000) : ℝ)
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L) := by
    have hkey : ((κ : ℝ) + 2) * (L + 1) * L
        ≤ ((κ : ℝ) + 2) * ((2 : ℝ) * L) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL2 hκp) (by linarith)
    nlinarith [hL1, hL2, hL3, hκp, hnn, hκL1, hkey]
  -- assemble
  have hTX : (0 : ℝ) ≤ ((callerTn n (3 * n * U) : ℕ) : ℝ)
      + ((23 * n * n + 29 : ℕ) : ℝ) := by positivity
  have h2L0 : (0 : ℝ) ≤ (2 : ℝ) * L := by positivity
  have hstep1 : ((Nat.clog 2 n : ℕ) : ℝ)
      * (((callerTn n (3 * n * U) : ℕ) : ℝ) + ((23 * n * n + 29 : ℕ) : ℝ))
      ≤ ((2 : ℝ) * L) * (((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
        * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
        + (52 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
    have hR1 : ((callerTn n (3 * n * U) : ℕ) : ℝ)
        ≤ ((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
          * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := hTn
    have hp1 : ((Nat.clog 2 n : ℕ) : ℝ)
        * (((callerTn n (3 * n * U) : ℕ) : ℝ) + ((23 * n * n + 29 : ℕ) : ℝ))
        ≤ (L + 1) * (((callerTn n (3 * n * U) : ℕ) : ℝ)
          + ((23 * n * n + 29 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hclogr hTX
    have hp2 : (L + 1) * (((callerTn n (3 * n * U) : ℕ) : ℝ)
        + ((23 * n * n + 29 : ℕ) : ℝ))
        ≤ ((2 : ℝ) * L) * (((callerTn n (3 * n * U) : ℕ) : ℝ)
          + ((23 * n * n + 29 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hL2 hTX
    have hp5 : ((2 : ℝ) * L) * (((callerTn n (3 * n * U) : ℕ) : ℝ)
        + ((23 * n * n + 29 : ℕ) : ℝ))
        ≤ ((2 : ℝ) * L) * (((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
          * ((217 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
          + (52 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hR1, h23]) h2L0
    linarith [hp1, hp2, hp5]
  have hmain : ((Nat.clog 2 n * (callerTn n (3 * n * U) + 23 * n * n + 29)
      + 53 * n * n + 17 * n + 65 : ℕ) : ℝ)
      ≤ ((7000 * (κ : ℝ) + 30000) : ℝ)
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L) := by
    have hsum : ((Nat.clog 2 n : ℕ) : ℝ)
        * (((callerTn n (3 * n * U) : ℕ) : ℝ) + ((23 * n * n + 29 : ℕ) : ℝ))
        + ((53 * n * n + 17 * n + 65 : ℕ) : ℝ)
        = ((Nat.clog 2 n * (callerTn n (3 * n * U) + 23 * n * n + 29)
          + 53 * n * n + 17 * n + 65 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [← hsum]
    linarith [hstep1, htail, hcore]
  have hcast : ((Light.Sec3.apTime callerTn n U : ℕ) : ℝ)
      = ((Nat.clog 2 n * (callerTn n (3 * n * U) + 23 * n * n + 29)
          + 53 * n * n + 17 * n + 65 : ℕ) : ℝ) := by
    unfold Light.Sec3.apTime
    congr 1
    ring
  rw [hcast]
  calc ((Nat.clog 2 n * (callerTn n (3 * n * U) + 23 * n * n + 29)
        + 53 * n * n + 17 * n + 65 : ℕ) : ℝ)
      ≤ ((7000 * (κ : ℝ) + 30000) : ℝ)
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L) := hmain
    _ ≤ (4 * (7000 * (κ : ℝ) + 30000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
        * (Real.log (n : ℝ)) ^ 2 := by
        have hLL : L * L ≤ (2 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) := by
          nlinarith
        have hlog2 : Real.log (n : ℝ) ^ 2
            = Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
        have hκn2 : (0 : ℝ) ≤ (κ : ℝ) * (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
          positivity
        have hstep : ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L)
            ≤ ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
              * ((2 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hLL (by positivity)
        nlinarith [hstep, hlog2, hκn2, hnn]

set_option maxHeartbeats 2000000 in
/-- THE STEP COUNT'S TURNSTILE: the caller's clock is `completeCost`-
dominated — `CallerHdom callerTn`, the summit's `hdom` socket, at
`k := 0` and the κ-linear constant. -/
theorem callerHdom : CallerHdom callerTn := by
  intro κ
  refine ⟨0, 4 * (7000 * (κ : ℝ) + 30000), ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn8
  have hn3 : 3 ≤ n := by omega
  -- timeUpTo is a sup over U ≤ n^κ; the bound is uniform in U
  have hsup : Light.timeUpTo (Light.Sec3.apTime callerTn) n ((n : ℝ) ^ (κ : ℝ))
      ≤ (4 * (7000 * (κ : ℝ) + 30000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
        * (Real.log (n : ℝ)) ^ 2 := by
    refine Light.timeUpTo_le (Tn := Light.Sec3.apTime callerTn) (n := n)
      (u := ((n : ℝ) ^ (κ : ℝ))) (B := _) ?_
    intro U hU
    have hpos : 0 ≤ ((n : ℝ) ^ (κ : ℝ)) := by positivity
    have hmax' := hU
    rw [max_eq_left hpos] at hmax'
    have hUn : U ≤ n ^ κ := by exact_mod_cast hmax'
    exact apTime_le_sq_log κ n U hn3 hUn
  calc Light.timeUpTo (Light.Sec3.apTime callerTn) n ((n : ℝ) ^ (κ : ℝ))
      ≤ (4 * (7000 * (κ : ℝ) + 30000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
        * (Real.log (n : ℝ)) ^ 2 := hsup
    _ ≤ (4 * (7000 * (κ : ℝ) + 30000)) * AsymptoticCosts.completeCost 0 n := by
        have hcc := completeCost_ge_log_sq n hn8
        have hC0 : (0 : ℝ) ≤ (4 : ℝ) * (7000 * (κ : ℝ) + 30000) := by positivity
        have hcd : ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) := rfl
        have hκn2 : (0 : ℝ) ≤ (κ : ℝ) * (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
          positivity
        have hnn2 : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by positivity
        calc (4 * (7000 * (κ : ℝ) + 30000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
            * (Real.log (n : ℝ)) ^ 2
            = (4 * (7000 * (κ : ℝ) + 30000))
              * (((n : ℝ) * (n : ℝ)) * (Real.log (n : ℝ)) ^ 2) := by rw [hcd]; ring
          _ ≤ (4 * (7000 * (κ : ℝ) + 30000)) * AsymptoticCosts.completeCost 0 n :=
              mul_le_mul_of_nonneg_left hcc hC0

#print axioms callerB_le
#print axioms callerNeed_poly
#print axioms completeCost_ge_log_sq
#print axioms apTime_le_sq_log
#print axioms callerHdom

end ThinMatrix.CallerStepCount
