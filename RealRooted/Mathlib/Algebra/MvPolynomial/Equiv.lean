import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degree bounds for univariate multivariate-polynomial equivalences

This file contains Mathlib-shaped compatibility lemmas for
`MvPolynomial.uniqueAlgEquiv`.
-/

namespace MvPolynomial

/-- Passing from a uniquely indexed multivariate polynomial to a univariate
polynomial does not increase total degree. -/
theorem natDegree_uniqueAlgEquiv_le_totalDegree
    {σ R : Type*} [Unique σ] [CommSemiring R] (p : MvPolynomial σ R) :
    (MvPolynomial.uniqueAlgEquiv R σ p).natDegree ≤ p.totalDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra hcoeff
  have hsupp : Finsupp.single default n ∈ p.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hle := MvPolynomial.le_totalDegree hsupp
  exact (not_le_of_gt hn) (by simpa using hle)

/-- The degree in the unique variable after converting a univariate polynomial
to an `MvPolynomial` is its natural degree. -/
theorem degreeOf_uniqueAlgEquiv_symm
    {σ R : Type*} [Unique σ] [CommSemiring R] (p : Polynomial R) :
    degreeOf default ((MvPolynomial.uniqueAlgEquiv R σ).symm p) =
      p.natDegree := by
  apply le_antisymm
  · rw [degreeOf_le_iff]
    intro d hd
    have hcoeff : p.coeff (d default) ≠ 0 := by
      rw [← MvPolynomial.coeff_uniqueAlgEquiv_symm R p d]
      exact MvPolynomial.mem_support_iff.mp hd
    exact Polynomial.le_natDegree_of_ne_zero hcoeff
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have hnotmem :
        Finsupp.single default n ∉
          ((MvPolynomial.uniqueAlgEquiv R σ).symm p).support := by
      apply MvPolynomial.notMem_support_of_degreeOf_lt default
      simpa using hn
    have hzero := MvPolynomial.notMem_support_iff.mp hnotmem
    rw [MvPolynomial.coeff_uniqueAlgEquiv_symm R p
      (Finsupp.single default n)] at hzero
    simpa using hzero

end MvPolynomial
