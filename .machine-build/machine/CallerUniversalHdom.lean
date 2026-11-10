import CallerUniversalBody

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the clock transfer.

# `hdom` at `univTn`: the composite's domination, DERIVED

`twinUniv_of` and `twinUniv_socket` take the domination as a hypothesis written
at the whole composite clock:

  `∀ κ, ∃ k C, eventually  timeUpTo (apTime (univTn cacheTime)) n (n^κ) ≤ C · completeCost k n`

That shape is class (iii) — image arithmetic — and it was the LAST opaque name
in the filing's premise list. It is opaque in the wrong place: a caller of the
bundle cannot justify a domination statement about a composite whose largest
term (`cacheTime (n²) U`) belongs to somebody else's solver.

This module replaces the SHAPE, not just the proof obligation:

* `apTime_univ_le_sq_log` — for every `κ`, `apTime (univTn cacheTime) n U` is
  `O(n² · log² n)` UNIFORMLY over `U ≤ n^κ`, PROVIDED the cache's clock fits one
  `(2·log₂U + 6)·770·n²` arm (the hypothesis `univTn_le` already carries).
* `univHdom` — `CallerHdom (univTn cacheTime)` from that hypothesis. The
  domination of the composite is now a THEOREM; it leaves the premise list.
* `twinUniv_of_clock` / `twinUniv_socket_clock` — the firing theorems with
  `hdom` replaced by the cache clock's budget.

## The named form is the BUNDLED one, on purpose

The arm `(2·log₂U + 6)·770·n²` has to carry the cache call's own `univCallB = 18`
argument+call-rule steps as well as `cacheTime`, because `univTn` adds them
together before anything bounds the sum:

  `univCallB + cacheTime (n²) U ≤ (2·log₂U + 6)·(770·n²)`.

A "pure" clock bound (`cacheTime ≤ that arm`) is strictly WEAKER and does NOT
imply this — `18 + c ≤ A` does not follow from `c ≤ A`. An earlier draft of this
module carried a `hcT_of_cacheClock` bridge asserting exactly that implication;
it is FALSE, it was caught by `omega` in elaboration (the counterexample is
`c = A`, `univCallB = 18`), and it is not here. Anyone naming this premise must
name the bundled form.

## What this does and does not buy — stated before any number

IT CLOSES the `hdom` slot as a *name*. It does NOT make the premise list
premise-free, and the honest reason is arithmetic, not laziness: `univTn` has
`cacheTime (n²) U` as a free function argument, and `Light.Solves` bounds a run
ABOVE by its claimed clock — a larger `Tn` is a WEAKER claim that is still true
(`Solves` says "ends within `T` steps", so nothing bounds `T` from above). No
in-tree fact therefore bounds `cacheTime`, and the domination of `univTn` is
FALSE for an adversarial clock. The remaining class (iii) name is exactly:

  **the cache solver's own clock budget** — `cacheTime (n²) U ≤ (2·log₂U+6)·(770·n²)`.

That name is a fact about the CACHE, in the cache boundary's own vocabulary: the
same party that lands `Solves cacheTask cacheProg cacheProc cacheTime univSocket`
is the party that knows its clock. It is NOT weaker than `hdom` (it is uniform
in `U` while `hdom` is a sup over `U ≤ n^κ`); it is *justifiable*, which `hdom`
was not. Disclosed rather than smoothed over.

## Where the cache term goes (the "absorption", measured)

`univTn_le` already puts `univCallB + cacheTime (n²) U` inside one
`(2·log₂U+6)·(770·n²)` arm; the schedule's `mpRounds U · univUnitB n` fits the
same arm (`univUnitB_le`, `mpRounds_le_two_log_succ`); the prologue's `27n + 64`
is `O(n²)`. So the whole clock is `O(n² log U)`, and `Nat.log2 (3nU) =
O((κ+2)·log₂ n)` for `U ≤ n^κ` collapses it to `O(n² log² n)` — which is the
`log^(k+R+10)·n²` arm of `AsymptoticCosts.completeCost` at `k = 0`
(`completeCost_ge_log_sq`, `n ≥ 8`). The constant is generous on purpose; only
its κ-linearity is load-bearing.
-/

namespace ThinMatrix.CallerUniversalBody

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerPost ThinMatrix.CallerStepCount ThinMatrix.Summit
  ThinMatrix.CallerWrites ThinMatrix.CallerRun ThinMatrix.CallerBodyStep
  ThinMatrix.CacheFill

/-! ## Two `private` lemmas, restated here because `private` does not cross a module

`CallerStepCount`'s `log2_le_two_log` and `half_lt_log_two` are `private`, so they
are mangled per-file and are NOT reachable from an importing module. Re-stated
(the statements, not new mathematics) rather than made public, which would change
a landed module for a consumer's convenience. -/

/-- `1/2 < log 2`, from the pinned bound `exp 1 < 2.718… < 4`. -/
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

set_option maxHeartbeats 2000000 in
/-- THE HOST'S LIFTED CLOCK AT THE UNIVERSAL BODY'S `Tn` IS `O(n² · log² n)`,
uniformly over `U ≤ n^κ` — per fixed `κ`, given the cache clock's arm.

The proof is `CallerStepCount.apTime_le_sq_log`'s, re-run at `univTn`: the same
`clog ≤ log₂ + 1 ≤ 2·log₂`, the same `log₂(3nU) ≤ (κ+2)(log₂ n + 1)`, and the
one substitution that matters — `callerTn`'s `mpRounds · callerB` arm becomes
`univTn_le`'s `2·((2·log₂U + 6)·770n²) + 27n + 64`. -/
theorem apTime_univ_le_sq_log (cacheTime : ℕ → ℕ → ℕ)
    (hcT : ∀ (n U : ℕ), 1 ≤ n →
      univCallB + cacheTime (n * n) U ≤ (2 * Nat.log2 U + 6) * (770 * (n * n)))
    (κ : Nat) (n U : ℕ) (hn8 : 8 ≤ n) (hU : U ≤ n ^ κ) :
    ((Light.Sec3.apTime (univTn cacheTime) n U : ℕ) : ℝ)
      ≤ (4 * (13000 * (κ : ℝ) + 46000))
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hn3 : 3 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn1
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
  -- (a) `clog 2 n ≤ log₂ n + 1`, and `Nat.clog`'s own bound
  have hlt : n < (2 : ℕ) ^ (Nat.log2 n + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have h2 : Nat.log 2 n = Nat.log2 n := Nat.log2_eq_log_two.symm
    rwa [h2, Nat.succ_eq_add_one] at h
  have hclogr : ((Nat.clog 2 n : ℕ) : ℝ) ≤ L + 1 := by
    have h := Nat.clog_le_of_le_pow (b := 2) (Nat.le_of_lt hlt)
    have h2 : ((Nat.clog 2 n : ℕ) : ℝ) ≤ ((Nat.log2 n + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    have h3 : ((Nat.log2 n + 1 : ℕ) : ℝ) = L + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ← hLdef]
    linarith
  -- (b) the schedule's bound `3nU` has log ≤ (κ+2)(log₂ n + 1)
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
  -- (c) the universal budget at the host's bound `3nU`
  have hA_nat : 2 * Nat.log2 (3 * n * U) + 6
      ≤ 2 * ((κ + 2) * (Nat.log2 n + 1)) + 6 := by
    have h2 := Nat.mul_le_mul_left 2 hlog3
    omega
  have hstep : univTn cacheTime n (3 * n * U)
      ≤ 2 * ((2 * ((κ + 2) * (Nat.log2 n + 1)) + 6) * (770 * (n * n))) + 27 * n + 64 := by
    have h := univTn_le cacheTime n (3 * n * U) (by omega) (hcT n (3 * n * U) (by omega))
    have hm : (2 * Nat.log2 (3 * n * U) + 6) * (770 * (n * n))
        ≤ (2 * ((κ + 2) * (Nat.log2 n + 1)) + 6) * (770 * (n * n)) :=
      Nat.mul_le_mul_right _ hA_nat
    have hm2 := Nat.mul_le_mul_left 2 hm
    omega
  have hTnR : ((univTn cacheTime n (3 * n * U) : ℕ) : ℝ)
      ≤ (2 : ℝ) * (((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
          * (770 * (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)))) + 27 * ((n : ℕ) : ℝ) + 64 := by
    have hc : ((univTn cacheTime n (3 * n * U) : ℕ) : ℝ)
        ≤ ((2 * ((2 * ((κ + 2) * (Nat.log2 n + 1)) + 6) * (770 * (n * n)))
          + 27 * n + 64 : ℕ) : ℝ) := by
      exact_mod_cast hstep
    push_cast at hc
    rw [← hLdef] at hc
    linarith [hc]
  -- (d) the two `O(n²)` corrections and the prologue's
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
  have hpro : (27 : ℝ) * ((n : ℕ) : ℝ) + 64
      ≤ (91 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
    nlinarith [hnR, hnn]
  -- (e) the fold's atoms
  have hL2 : (L + (1 : ℝ)) ≤ (2 : ℝ) * L := by linarith
  have hL3 : (L : ℝ) ≤ L * L := by nlinarith
  have hκp : (0 : ℝ) ≤ (κ : ℝ) + 2 := by positivity
  have hκL1 : (0 : ℝ) ≤ ((κ : ℝ) + 2) * L := mul_nonneg hκp (by linarith)
  have hkey : ((κ : ℝ) + 2) * (L + 1) * L
      ≤ ((κ : ℝ) + 2) * ((2 : ℝ) * L) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 hκp) (by linarith)
  -- (f) the fold: `2L·(1540·A + 143)·n² + 140n² ≤ (13000κ + 46000)·n²·L²`
  have hcore : ((2 : ℝ) * L) * (((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
        * ((1540 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
        + (143 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
      + (140 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
      ≤ ((13000 * (κ : ℝ) + 46000) : ℝ)
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L) := by
    nlinarith [hL1, hL2, hL3, hκp, hnn, hκL1, hkey]
  -- (g) multiply by `clog 2 n ≤ 2L`, monotone in the inner factor
  have hTX : (0 : ℝ) ≤ ((univTn cacheTime n (3 * n * U) : ℕ) : ℝ)
      + ((23 * n * n + 29 : ℕ) : ℝ) := by positivity
  have h2L0 : (0 : ℝ) ≤ (2 : ℝ) * L := by positivity
  have hinner : ((univTn cacheTime n (3 * n * U) : ℕ) : ℝ)
        + ((23 * n * n + 29 : ℕ) : ℝ)
      ≤ ((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
          * ((1540 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
        + (143 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
    linarith [hTnR, hpro, h23]
  have hstep1 : ((Nat.clog 2 n : ℕ) : ℝ)
      * (((univTn cacheTime n (3 * n * U) : ℕ) : ℝ) + ((23 * n * n + 29 : ℕ) : ℝ))
      ≤ ((2 : ℝ) * L) * (((2 : ℝ) * ((κ : ℝ) + 2) * (L + 1) + 6)
        * ((1540 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))
        + (143 : ℝ) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
    have hp1 := mul_le_mul_of_nonneg_right hclogr hTX
    have hp2 := mul_le_mul_of_nonneg_right hL2 hTX
    have hp5 := mul_le_mul_of_nonneg_left hinner h2L0
    linarith [hp1, hp2, hp5]
  -- (h) `apTime`'s own shape, and the sum
  have hcast_nat : Light.Sec3.apTime (univTn cacheTime) n U
      = Nat.clog 2 n * (univTn cacheTime n (3 * n * U) + 23 * n * n + 29)
        + 53 * n * n + 17 * n + 65 := by
    unfold Light.Sec3.apTime
    congr 1
    ring_nf
  have hcastR : ((Light.Sec3.apTime (univTn cacheTime) n U : ℕ) : ℝ)
      = ((Nat.clog 2 n : ℕ) : ℝ)
        * (((univTn cacheTime n (3 * n * U) : ℕ) : ℝ) + ((23 * n * n + 29 : ℕ) : ℝ))
        + ((53 * n * n + 17 * n + 65 : ℕ) : ℝ) := by
    rw [hcast_nat]
    push_cast
    ring
  have hmain : ((Nat.clog 2 n : ℕ) : ℝ)
      * (((univTn cacheTime n (3 * n * U) : ℕ) : ℝ) + ((23 * n * n + 29 : ℕ) : ℝ))
      + ((53 * n * n + 17 * n + 65 : ℕ) : ℝ)
      ≤ ((13000 * (κ : ℝ) + 46000) : ℝ)
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L) := by
    linarith [hstep1, htail, hcore]
  -- (i) `L² ≤ 4·log²`, and the generous constant absorbs the 4
  have hscale : ((13000 * (κ : ℝ) + 46000) : ℝ)
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (L * L)
      ≤ (4 * (13000 * (κ : ℝ) + 46000))
        * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    have hLL : L * L ≤ (2 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) := by
      nlinarith [hLn, hL1]
    have hf : (0 : ℝ) ≤ ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by positivity
    have hC : (0 : ℝ) ≤ 13000 * (κ : ℝ) + 46000 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hLL (mul_nonneg hC hf)
    nlinarith [h1]
  rw [hcastR]
  linarith [hmain, hscale]

#print axioms apTime_univ_le_sq_log

/-- THE TRANSFER: the universal body's domination, from the CACHE's clock.

`hdom` — `CallerHdom (univTn cacheTime)` — is what `twinUniv_of` and
`twinUniv_socket` were carrying. It is now a theorem, and the only thing it
asks is a bound on the cache solver's own clock. `∃`-constant `4·(13000κ +
46000)`; `k := 0` (the `log^(0+R+10)·n²` arm of the ledger). -/
theorem univHdom (cacheTime : ℕ → ℕ → ℕ)
    (hcT : ∀ (n U : ℕ), 1 ≤ n →
      univCallB + cacheTime (n * n) U ≤ (2 * Nat.log2 U + 6) * (770 * (n * n))) :
    CallerHdom (univTn cacheTime) := by
  intro κ
  refine ⟨0, 4 * (13000 * (κ : ℝ) + 46000), ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn8
  have hsup : Light.timeUpTo (Light.Sec3.apTime (univTn cacheTime)) n ((n : ℝ) ^ (κ : ℝ))
      ≤ (4 * (13000 * (κ : ℝ) + 46000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
        * (Real.log (n : ℝ)) ^ 2 := by
    refine Light.timeUpTo_le (Tn := Light.Sec3.apTime (univTn cacheTime)) (n := n)
      (u := ((n : ℝ) ^ (κ : ℝ))) (B := _) ?_
    intro U hU
    have hpos : 0 ≤ ((n : ℝ) ^ (κ : ℝ)) := by positivity
    rw [max_eq_left hpos] at hU
    have hUn : U ≤ n ^ κ := by exact_mod_cast hU
    exact apTime_univ_le_sq_log cacheTime hcT κ n U hn8 hUn
  calc Light.timeUpTo (Light.Sec3.apTime (univTn cacheTime)) n ((n : ℝ) ^ (κ : ℝ))
      ≤ (4 * (13000 * (κ : ℝ) + 46000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
        * (Real.log (n : ℝ)) ^ 2 := hsup
    _ ≤ (4 * (13000 * (κ : ℝ) + 46000)) * AsymptoticCosts.completeCost 0 n := by
        have hcc := completeCost_ge_log_sq n hn8
        have hC0 : (0 : ℝ) ≤ 4 * (13000 * (κ : ℝ) + 46000) := by positivity
        have hcd : ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) := rfl
        calc (4 * (13000 * (κ : ℝ) + 46000)) * ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)
            * (Real.log (n : ℝ)) ^ 2
            = (4 * (13000 * (κ : ℝ) + 46000))
              * (((n : ℝ) * (n : ℝ)) * (Real.log (n : ℝ)) ^ 2) := by rw [hcd]; ring
          _ ≤ (4 * (13000 * (κ : ℝ) + 46000)) * AsymptoticCosts.completeCost 0 n :=
              mul_le_mul_of_nonneg_left hcc hC0

#print axioms univHdom


/-- THE TWIN, FIRED FROM THE BUNDLE **AND THE CACHE'S CLOCK** — `hdom` gone.
Same conclusion as `twinUniv_of`, one premise SWAPPED for a fact about the
cache solver rather than a domination statement about the composite. -/
theorem twinUniv_of_clock (stage cacheProc : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (need : ℕ → ℕ → Light.Need) (cacheTime : ℕ → ℕ → ℕ)
    (hb : UnivBundle stage cacheProc cacheProg restoreProg cs cacheTime need)
    (hcov : NeedCovers need)
    (hn : Light.PolyNeed need)
    (hcT : ∀ (n U : ℕ), 1 ≤ n →
      univCallB + cacheTime (n * n) U ≤ (2 * Nat.log2 U + 6) * (770 * (n * n))) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) :=
  twinUniv_of stage cacheProc cacheProg restoreProg cs need cacheTime hb hcov hn
    (univHdom cacheTime hcT)

#print axioms twinUniv_of_clock

/-- THE FILING THEOREM — the `hdom`-free form at the one witness term. This is
the shape the filing draft's premise list names: the bundle's four (i)/(ii)
conjuncts, and the cache's clock. -/
theorem twinUniv_socket_clock (stage cacheProc : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (cacheTime : ℕ → ℕ → ℕ)
    (hb : UnivBundle stage cacheProc cacheProg restoreProg cs cacheTime univNeed)
    (hcT : ∀ (n U : ℕ), 1 ≤ n →
      univCallB + cacheTime (n * n) U ≤ (2 * Nat.log2 U + 6) * (770 * (n * n))) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) :=
  twinUniv_socket stage cacheProc cacheProg restoreProg cs cacheTime hb
    (univHdom cacheTime hcT)

#print axioms twinUniv_socket_clock

end ThinMatrix.CallerUniversalBody
