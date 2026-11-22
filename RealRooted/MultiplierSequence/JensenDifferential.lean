module

public import RealRooted.MultiplierSequence.PolyaSchur.Analytic
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialRange
import RealRooted.Mathlib.Analysis.SpecificLimits.DescFactorialWeights

/-!
# Jensen approximations to infinite differential symbols

Finite rescaled Jensen symbols give regular finite sums of the differential
series. Pointwise convergence of the ordinary series, including conditional
convergence, therefore identifies the pointwise limit of these finite operators.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

/-- Rescaling does not increase the prescribed degree of a Jensen polynomial. -/
theorem natDegree_rescaledJensenPolynomial_le (n : ℕ) (a : ℕ → ℝ) :
    (rescaledJensenPolynomial n a).natDegree ≤ n := by
  unfold rescaledJensenPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- A finite Jensen differential symbol is the falling-factorial weighted sum
of the corresponding formal infinite differential series. -/
theorem differentialApply_rescaledJensenPolynomial (a : ℕ → ℝ) (f : ℂ → ℂ)
    (n : ℕ) (z : ℂ) :
    ((rescaledJensenPolynomial n a).map ofRealHom).differentialApply f z =
      ∑ j ∈ Finset.range (n + 1),
        ((n.descFactorial j : ℝ) / (n : ℝ) ^ j) •
          ((a j : ℂ) * iteratedDeriv j f z / j.factorial) := by
  rw [Polynomial.differentialApply_eq_sum_range _ _
    ((natDegree_map_le).trans (natDegree_rescaledJensenPolynomial_le n a))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [coeff_map, coeff_rescaledJensenPolynomial, ite_eq_left hjn,
    ofRealHom_eq_coe, smul_eq_mul, Complex.real_smul, ofReal_mul, ofReal_pow,
    ofReal_inv, ofReal_div, ofReal_natCast]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp [hfac]
  ring

/-- Convergence of the ordinary differential series at a point implies
convergence of its finite Jensen-symbol approximations to the same value. -/
theorem tendsto_differentialApply_rescaledJensenPolynomial (a : ℕ → ℝ) (f : ℂ → ℂ)
    (z w : ℂ)
    (h : Tendsto (fun n => ∑ j ∈ Finset.range n,
      (a j : ℂ) * iteratedDeriv j f z / j.factorial) atTop (𝓝 w)) :
    Tendsto (fun n =>
      ((rescaledJensenPolynomial n a).map ofRealHom).differentialApply f z)
      atTop (𝓝 w) := by
  simpa only [differentialApply_rescaledJensenPolynomial] using
    Nat.tendsto_sum_descFactorial_smul h

end RealRooted
