import RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix
import RealRooted.PolynomialValueEulerNumerator.PF

/-!
# PF canonical Euler numerators from polynomial-value sequences

This leaf iterates the checked causal Pólya-frequency closure through a
polynomial's actual degree and then uses the exact numerator-coefficient
identity.
-/

open Filter Polynomial Topology

namespace RealRooted

/-- A Pólya-frequency polynomial-value sequence has a Pólya-frequency
canonical Euler numerator. -/
theorem isPFPolynomial_polynomialValueEulerNumerator_of_polyaFreqSeq
    {p : ℝ[X]} (ha : IsPolyaFreqSeq (polynomialValueSeq p)) :
    IsPFPolynomial (polynomialValueEulerNumerator p) := by
  by_cases hp : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  have hiter : ∀ k : ℕ, k ≤ p.natDegree + 1 →
      IsPolyaFreqSeq ((Function.causalFwdDiff^[k]) (polynomialValueSeq p)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa
    | succ k ih =>
      intro hk
      have hpfk := ih (by lia)
      have hkdeg : k ≤ p.natDegree := by lia
      rw [Function.iterate_succ_apply']
      exact hpfk.causalFwdDiff_of_eventually_polynomial
        (Polynomial.causalFwdDiffPolynomial_iter_ne_zero_of_le_natDegree hp hkdeg)
        (Polynomial.eventually_eq_eval_causalFwdDiff_iter
          (Filter.Eventually.of_forall fun n => rfl) k)
  apply IsPFPolynomial.of_polyaFreqSeq
  rw [← causalFwdDiff_iter_polynomialValueSeq_eq_eulerNumerator_coeff]
  exact hiter _ le_rfl

end RealRooted
