/-
Author: Joshua Wharton, QFEX, joshua@qfex.com.

Targeted imports for the transparently vendored upstream modules.
No upstream mathematical definition or theorem statement is altered.
The separate source patch records one explicit equality-transport proof adaptation.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
The pinned Mathlib represents additive monoid algebras by a structure with
field `coeff`. The preserved upstream source uses its previous function
application notation and three previous lemma names. This compatibility
layer restores only those coefficient reads and aliases, and derives the
Fin-indexed vector read rule from the existing GetElem rule. It does not
replace addition, multiplication, casts, or any arithmetic definition.
-/

namespace ThinMatrix.LocalMathlibCompat

instance addMonoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (AddMonoidAlgebra R M) (fun _ => M → R) where
  coe a := a.coeff

@[simp] theorem vectorGetOfFn {α : Type*} {n : Nat}
    (f : Fin n → α) (i : Fin n) : (Vector.ofFn f).get i = f i := by
  exact Vector.getElem_ofFn i.isLt

end ThinMatrix.LocalMathlibCompat

namespace AddMonoidAlgebra

-- The structure's coefficient projection reduces to `Finsupp.single`.
-- Alias the underlying evaluation theorem so `simp` can use it after
-- that projection has reduced as well as before reduction.
alias single_apply := Finsupp.single_apply
alias mul_apply_left := coeff_mul_apply_left
alias single_zero_mul_apply := coeff_single_zero_mul

end AddMonoidAlgebra
