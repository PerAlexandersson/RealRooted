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

end MvPolynomial
