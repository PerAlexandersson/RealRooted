module

public import RealRooted.Hermite.Jensen
public import RealRooted.SimpleRoots
import RealRooted.Hermite.FiniteTransfer
import RealRooted.Derivative.Interlacing

/-!
# The Hermite Jensen Appell family

For a fixed coefficient sequence, differentiation lowers the degree index
without shifting the coefficient sequence. This gives consecutive-degree
interlacing, and simple roots exclude shared roots between adjacent rows.
-/

public section

open Polynomial

namespace RealRooted

/-- Hermite Jensen polynomials form an Appell family with derivative factor `2d`. -/
theorem derivative_hermiteJensenPolynomial (d : ℕ) (gamma : ℕ → ℝ) :
    (hermiteJensenPolynomial (d + 1) gamma).derivative =
      C (2 * (d + 1 : ℝ)) * hermiteJensenPolynomial d gamma := by
  classical
  rw [hermiteJensenPolynomial, map_sum, Finset.sum_range_succ]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, Nat.sub_self,
    hermitePhysicists_zero, derivative_one, mul_zero, add_zero]
  rw [hermiteJensenPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : d + 1 - k = d - k + 1 := by lia
  rw [hsub, derivative_hermitePhysicists]
  have hchoose : ((d + 1).choose k : ℝ) * (d - k + 1 : ℕ) =
      (d + 1 : ℝ) * (d.choose k : ℝ) := by
    rw [← hsub]
    exact_mod_cast (Nat.choose_mul_succ_eq d k).symm.trans (Nat.mul_comm _ _)
  simp only [← mul_assoc, ← C_mul]
  congr 2
  push_cast at hchoose
  linear_combination 2 * gamma k * hchoose

/-- Splitting of the upper Hermite row gives zero-aware interlacing with the preceding row. -/
theorem hermiteJensenPolynomial_interl {d : ℕ} {gamma : ℕ → ℝ}
    (hp : (hermiteJensenPolynomial (d + 1) gamma).Splits) :
    Interl (hermiteJensenPolynomial d gamma) (hermiteJensenPolynomial (d + 1) gamma) := by
  have hi : Interl (hermiteJensenPolynomial (d + 1) gamma).derivative
      (hermiteJensenPolynomial (d + 1) gamma) := by
    by_cases hd : (hermiteJensenPolynomial (d + 1) gamma).natDegree = 0
    · rw [derivative_eq_zero.mpr hd]
      exact interl_zero_left _
    · exact (derivative_interlaces_of_natDegree_ne_zero hp hd).toStrictInterl.toInterl
  have hscaled := hi.C_mul_left_of_nonneg (a := (2 * (d + 1 : ℝ))⁻¹) (by positivity)
  simpa only [derivative_hermiteJensenPolynomial, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (by positivity : (2 * (d + 1 : ℝ)) ≠ 0), C_1, one_mul] using hscaled

/-- Nonzero zeroth coefficient gives nonzero, consecutive-degree interlacing. -/
theorem hermiteJensenPolynomial_strictInterl {d : ℕ} {gamma : ℕ → ℝ}
    (hp : (hermiteJensenPolynomial (d + 1) gamma).Splits) (hgamma : gamma 0 ≠ 0) :
    StrictInterl (hermiteJensenPolynomial d gamma)
      (hermiteJensenPolynomial (d + 1) gamma) := by
  have hdegree : (hermiteJensenPolynomial (d + 1) gamma).natDegree ≠ 0 := by
    rw [natDegree_hermiteJensenPolynomial hgamma]
    lia
  have hi := (derivative_interlaces_of_natDegree_ne_zero hp hdegree).toStrictInterl
  have hscaled := hi.C_mul_left (a := (2 * (d + 1 : ℝ))⁻¹) (by positivity)
  simpa only [derivative_hermiteJensenPolynomial, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (by positivity : (2 * (d + 1 : ℝ)) ≠ 0), C_1, one_mul] using hscaled

/-- A simple upper Hermite row shares no real root with its predecessor. -/
theorem hermiteJensenPolynomial_no_common_root {d : ℕ} {gamma : ℕ → ℝ}
    (hp : HasSimpleRoots (hermiteJensenPolynomial (d + 1) gamma)) (r : ℝ) :
    ¬ ((hermiteJensenPolynomial d gamma).IsRoot r ∧
      (hermiteJensenPolynomial (d + 1) gamma).IsRoot r) := by
  intro hr
  apply hp.eval_derivative_ne_zero hr.2
  rw [derivative_hermiteJensenPolynomial, eval_mul]
  rw [show (hermiteJensenPolynomial d gamma).eval r = 0 from hr.1, mul_zero]

end RealRooted
