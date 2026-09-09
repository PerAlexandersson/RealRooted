import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Extensions to homogeneous multivariate polynomials

This file contains results intended for upstreaming to
`Mathlib.RingTheory.MvPolynomial.Homogeneous`.
-/

namespace MvPolynomial

/-- The homogeneous component in the total degree of a nonzero polynomial is
nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero
    {σ R : Type*} [CommSemiring R] {P : MvPolynomial σ R} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  obtain ⟨m, hm, hdegree⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hP) (fun d => d.degree)
  have htotal : P.totalDegree = m.degree := by
    have hfun :
        (fun s : σ →₀ ℕ => s.sum fun _ e => e) =
          fun s => s.degree := by
      funext s
      rw [Finsupp.degree_apply]
      rfl
    rw [MvPolynomial.totalDegree, hfun]
    exact hdegree
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff m) hzero
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos htotal.symm] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff

end MvPolynomial
