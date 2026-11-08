import Submission.ThreeSumApsp.LowCache.LowRowMachine

/-!
# Exact coefficient formulas for the compiled low-cache rows

Author: Joshua Wharton, QFEX, joshua@qfex.com.

These lemmas expose the twelve formulas and the flat-to-two-dimensional
index relation independently of the target-language execution proof.
-/

namespace Light.LowRowMachine

theorem normal_formulas (μ : Nat → Int) (a b c d q i : Nat) :
    (fun row => output true row μ a b c d q i) =
      ![μ (a + i) + μ (c + i) + μ (d + i),
        μ (a + i) + μ (c + i),
        μ (b + i) - μ (d + i),
        μ (b + i),
        -μ (a + i) - μ (b + i) + (if i < q then 0 else μ (c + (i - q))),
        μ (d + i)] := by
  funext row
  fin_cases row <;>
    simp [output, thirdRead, combine, shiftsThird, coefficients] <;> ring

theorem opposite_formulas (μ : Nat → Int) (a b c d q i : Nat) :
    (fun row => output false row μ a b c d q i) =
      ![μ (a + i) + μ (b + i),
        μ (a + i) - μ (b + i),
        μ (a + i) + μ (b + i) - μ (c + i),
        μ (a + i) - μ (b + i) + μ (c + i),
        2 * μ (a + i),
        μ (c + i)] := by
  funext row
  fin_cases row <;>
    simp [output, thirdRead, combine, shiftsThird, coefficients] <;> ring

/-- Subtracting one cyclic-vector length means moving back one auxiliary
degree, without mixing different cyclic residues. -/
theorem thirdRead_flatten (normal : Bool) (row : Fin 6) (μ : Nat → Int)
    (c q degree residue : Nat) (hr : residue < q) :
    thirdRead normal row μ c q (degree * q + residue) =
      if shiftsThird normal row then
        if degree = 0 then 0 else μ (c + ((degree - 1) * q + residue))
      else μ (c + (degree * q + residue)) := by
  unfold thirdRead
  split
  · by_cases hd : degree = 0
    · simp [hd, hr]
    · have hpos : 1 ≤ degree := by omega
      have hrepr : degree * q + residue = (degree - 1) * q + residue + q := by
        calc
          degree * q + residue = ((degree - 1) + 1) * q + residue := by
            rw [Nat.sub_add_cancel hpos]
          _ = (degree - 1) * q + residue + q := by ring
      have hge : q ≤ degree * q + residue := by omega
      have hsub : degree * q + residue - q = (degree - 1) * q + residue := by omega
      simp [hd, Nat.not_lt.mpr hge, hsub]
  · rfl

/-- A source index produced by the previous-degree branch stays inside its
input array whenever the current degree and residue do. -/
theorem shifted_source_in_range (q width degree residue : Nat)
    (hd : degree < width) (hr : residue < q) (hpos : 0 < degree) :
    (degree - 1) * q + residue < width * q := by
  have h1 : (degree - 1) * q + residue < degree * q := by
    calc
      (degree - 1) * q + residue < (degree - 1) * q + q := Nat.add_lt_add_left hr _
      _ = degree * q := by
        calc
          (degree - 1) * q + q = ((degree - 1) + 1) * q := by ring
          _ = degree * q := by rw [Nat.sub_add_cancel hpos]
  exact h1.trans_le (Nat.mul_le_mul_right q hd.le)

#print axioms normal_formulas
#print axioms opposite_formulas
#print axioms thirdRead_flatten

end Light.LowRowMachine
