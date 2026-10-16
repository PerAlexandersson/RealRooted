module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic

/-!
# The monic polynomial with prescribed roots

`rootPolynomial s = ∏_{r ∈ s} (X - C r)` for a multiset `s` of reals; a list `xs` enters as
`rootPolynomial ↑xs`.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted

/-- The monic polynomial with root multiset `s`. -/
def rootPolynomial (s : Multiset ℝ) : ℝ[X] :=
  (s.map fun r => X - C r).prod

/-- For a list, `rootPolynomial` is the product of the linear factors along the list. -/
theorem rootPolynomial_coe (xs : List ℝ) :
    rootPolynomial (xs : Multiset ℝ) = (xs.map fun r => X - C r).prod := by
  rw [rootPolynomial, Multiset.map_coe, Multiset.prod_coe]

/-- The roots of `rootPolynomial s`, with multiplicity, are exactly `s`. -/
@[simp] theorem roots_rootPolynomial (s : Multiset ℝ) :
    (rootPolynomial s).roots = s :=
  Polynomial.roots_multiset_prod_X_sub_C s

/-- `rootPolynomial s` is monic. -/
theorem rootPolynomial_monic (s : Multiset ℝ) : (rootPolynomial s).Monic :=
  Polynomial.monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r

/-- `rootPolynomial s` is nonzero. -/
theorem rootPolynomial_ne_zero (s : Multiset ℝ) : rootPolynomial s ≠ 0 :=
  (rootPolynomial_monic s).ne_zero

/-- The degree of `rootPolynomial s` is the cardinality of `s`. -/
@[simp] theorem natDegree_rootPolynomial (s : Multiset ℝ) :
    (rootPolynomial s).natDegree = s.card := by
  rw [rootPolynomial, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

/-- `rootPolynomial s` splits over the reals. -/
theorem rootPolynomial_splits (s : Multiset ℝ) : (rootPolynomial s).Splits :=
  Polynomial.splits_iff_card_roots.mpr (by simp)

end RealRooted
