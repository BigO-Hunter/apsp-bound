import MachineAdapter
import CoreCompatibility

/-!
Copyright (c) 2026. APSP port campaign: D7(a) the conservative adapter.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the aligned-cache construction whose min-plus solver
  contract (`Light.Solves mpTask …`) this adapter consumes.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  EndStatement.APSP target and `Realized` machinery are the pinned Anthropic
  statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement
  (`MachineAdapter`/`CanonicalMachineAdapter`) this file mirrors at the
  conservative bound; the retune whose certificate the conservative row
  de-risks.
- Hrishik Sai Bojnal — the verified frontier being refined.

# D7(a): the EndStatement.APSP adapter at the conservative bound

The upstream canonical adapter
(`MachineAdapter.rationalStatementOfMinPlusExecution`, fed by
`CanonicalMachineAdapter.rationalStatementOfLedger`) closes
`EndStatement.APSP.SolvedInTime 299294792/100000000` from three hypotheses:
an actual min-plus solver (`hs`), its polynomial need (`hn`), and an
eventual pointwise bound on the host's exact runtime (`hb`).

This file is that adapter at the conservative filing bound
`2994999/1000000` (= 2.994999; the conservative row's exponent, M3e/M3f).
The analytic side is WEAKER than the upstream chain's: the dominated
exponent in `hb`/`hdom` is the upstream constant `299294792/100000000`
(exactly what `AsymptoticCosts.costBoundOfDomination` certifies from a
`completeCost` domination), and `299294792/10^8 ≤ 2994999/10^6`, so the
exponent weakening is arithmetic. The hypothesis shapes are byte-identical
to the upstream adapters'. This closes NOTHING by itself:

- `hs` awaits the actual min-plus Light program from the ported machine
  components (L1–L6c deliver the interior contracts; the enclosing caller
  program with its execution derivation is the named remainder);
- `hdom` awaits the step-count bound of that program against
  `AsymptoticCosts.completeCost` (the same future step the upstream
  adapter's own `hb` awaits).

No (min,+) product is constructed here; D7's boundary stands.
-/

namespace ThinMatrix.ConservativeAdapter

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam

/-- The conservative filing bound: the exponent r in O(n^r), as the
canonical reduced rational 2994999/1000000 (= 2.994999). -/
def conservativeExponent : Rat := 2994999 / 1000000

/-- The weakening: the upstream chain's dominated exponent sits below the
conservative bound. -/
theorem targetExponent_cast :
    ((MachineAdapter.targetExponent : ℚ) : ℝ) = ((299294792 : ℕ) : ℝ) / 100000000 := by
  norm_num [MachineAdapter.targetExponent]

theorem targetExponent_le :
    ((MachineAdapter.targetExponent : ℚ) : ℝ) ≤ ((conservativeExponent : ℚ) : ℝ) := by
  rw [targetExponent_cast]
  norm_num [conservativeExponent]

/-- The conservative adapter: the upstream
`MachineAdapter.rationalStatementOfMinPlusExecution` at the conservative
bound. `hb`'s dominated exponent is the upstream chain's own constant
(`MachineAdapter.targetExponent = 299294792/100000000`). -/
theorem conservativeStatementOfMinPlusExecution {P : Light.Program} {p : Nat}
    {Tn : Nat → Nat → Nat} {need : Nat → Nat → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need)
    (hb : ∀ κ : Nat, ∃ C : Real, ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n
        ((n : Real) ^ (κ : Real)) ≤
      C * (n : Real) ^ ((MachineAdapter.targetExponent : Real))) :
    EndStatement.APSP.SolvedInTime conservativeExponent := by
  have hpow : ∀ n : ℕ, 1 ≤ n →
      (n : Real) ^ ((MachineAdapter.targetExponent : Real)) ≤
        (n : Real) ^ (((conservativeExponent : ℚ) : Real)) := fun n hn1 =>
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) targetExponent_le
  have hb' : ∀ κ : Nat, ∃ C : Real, ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n
        ((n : Real) ^ (κ : Real)) ≤
      C * (n : Real) ^ (((conservativeExponent : ℚ) : Real)) := by
    intro κ
    obtain ⟨C, hC⟩ := hb κ
    refine ⟨max C 0, ?_⟩
    have hCnn : 0 ≤ (max C 0 : ℝ) := le_max_right C 0
    filter_upwards [hC, eventually_ge_atTop (1 : ℕ)] with n hn1 hge
    have hle : (n : Real) ^ ((MachineAdapter.targetExponent : Real)) ≤
        (n : Real) ^ (((conservativeExponent : ℚ) : Real)) := hpow n hge
    have hnn : 0 ≤ (n : Real) ^ (((conservativeExponent : ℚ) : Real)) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _
    calc Light.timeUpTo (Light.Sec3.apTime Tn) n ((n : Real) ^ (κ : Real))
        ≤ C * (n : Real) ^ ((MachineAdapter.targetExponent : Real)) := hn1
      _ ≤ max C 0 * (n : Real) ^ ((MachineAdapter.targetExponent : Real)) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0)
          (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _)
      _ ≤ max C 0 * (n : Real) ^ (((conservativeExponent : ℚ) : Real)) :=
        mul_le_mul_of_nonneg_left hle hCnn
  apply ThreeSumApsp.WordRam.SolvedInTime.endStatement
    (a := ((conservativeExponent : ℚ) : Real)) ?_ rfl
    (by norm_num [conservativeExponent])
  intro κ
  obtain ⟨C, hC⟩ := hb' κ
  exact ThreeSumApsp.FromClaims.solvedAt_of_realized _ κ
    (MachineAdapter.realizedFromMinPlus hs hn) (C := C)
    (by simpa only [pow_zero, mul_one] using hC)

/-- The ledger-side conservative adapter: the upstream
`CanonicalMachineAdapter.rationalStatementOfLedger` at the conservative
bound. `hdom`'s shape is byte-identical to that adapter's `hb` — the
eventual pointwise domination of the host's exact runtime by the
construction's complete cost; `AsymptoticCosts.costBoundOfDomination`
turns it into the exponent bound, and the weakening is arithmetic. -/
theorem conservativeStatementOfLedger {P : Light.Program} {p : Nat}
    {Tn : Nat → Nat → Nat} {need : Nat → Nat → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need)
    (hdom : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n
        ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime conservativeExponent := by
  have hte : ((MachineAdapter.targetExponent : ℚ) : Real) =
      (299294792 / 100000000 : Real) := by
    norm_num [MachineAdapter.targetExponent]
  refine conservativeStatementOfMinPlusExecution hs hn ?_
  intro κ
  have htime : ∀ n : ℕ, 0 ≤ Light.timeUpTo (Light.Sec3.apTime Tn) n
      ((n : Real) ^ (κ : Real)) := fun n => by
    unfold Light.timeUpTo
    positivity
  obtain ⟨k, C, hC⟩ := hdom κ
  have hbigO : (fun n : ℕ => Light.timeUpTo (Light.Sec3.apTime Tn) n
      ((n : Real) ^ (κ : Real))) =O[atTop]
      (fun n : ℕ => (n : Real) ^ ((MachineAdapter.targetExponent : Real))) := by
    rw [hte]
    apply AsymptoticCosts.costBoundOfDomination _ k
    apply IsBigO.of_bound C
    filter_upwards [hC, eventually_ge_atTop (1 : ℕ)] with n hCn hn
    rw [Real.norm_eq_abs, abs_of_nonneg (htime n), Real.norm_eq_abs,
      abs_of_nonneg (AsymptoticCosts.completeCostNonnegative k n hn)]
    exact hCn
  obtain ⟨C', hC'⟩ := isBigO_iff.mp hbigO
  refine ⟨C', ?_⟩
  filter_upwards [hC', eventually_ge_atTop (1 : ℕ)] with n hn1 _
  have habs : |Light.timeUpTo (Light.Sec3.apTime Tn) n ((n : Real) ^ (κ : Real))|
      = Light.timeUpTo (Light.Sec3.apTime Tn) n ((n : Real) ^ (κ : Real)) :=
    abs_of_nonneg (htime n)
  have habs2 : |(n : Real) ^ ((MachineAdapter.targetExponent : Real))|
      = (n : Real) ^ ((MachineAdapter.targetExponent : Real)) :=
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [Real.norm_of_nonneg (htime n), Real.norm_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hn1
  exact hn1

#print axioms conservativeExponent
#print axioms targetExponent_cast
#print axioms targetExponent_le
#print axioms conservativeStatementOfMinPlusExecution
#print axioms conservativeStatementOfLedger

end ThinMatrix.ConservativeAdapter
