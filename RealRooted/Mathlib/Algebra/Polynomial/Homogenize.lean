import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Polynomial homogenization compatibility lemmas

This file supplies root-factor formulas for `Polynomial.homogenize`.
-/

open Polynomial

namespace Polynomial

/-- The natural degree of a product of monic linear root factors is the number
of factors. -/
theorem natDegree_rootFactorProduct {R : Type*} [CommRing R] [IsDomain R]
    (roots : Multiset R) :
    (roots.map (fun r => X - C r)).prod.natDegree = roots.card := by
  rw [natDegree_multiset_prod]
  · simp
  · simp [X_sub_C_ne_zero]

/-- Homogenizing a monic linear root factor gives its usual bivariate form. -/
theorem homogenize_X_sub_C {R : Type*} [CommRing R] (r : R) :
    (X - C r).homogenize 1 =
      (MvPolynomial.X 0 - MvPolynomial.C r * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) R) := by
  simp [homogenize_sub, homogenize_X, homogenize_C]

/-- Homogenization sends a product of monic linear root factors to the product
of their homogeneous bivariate forms. -/
theorem homogenize_rootFactorProduct {R : Type*} [CommRing R] [IsDomain R]
    (roots : Multiset R) :
    (roots.map (fun r => X - C r)).prod.homogenize roots.card =
      (roots.map (fun r =>
        MvPolynomial.X 0 - MvPolynomial.C r * MvPolynomial.X 1)).prod := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons r roots ih =>
      have hdeg :
          (roots.map (fun r => X - C r)).prod.natDegree ≤ roots.card := by
        simp
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
        Nat.add_comm roots.card 1,
        homogenize_mul _ _ (natDegree_X_sub_C_le r) hdeg, ih]
      simp

end Polynomial
