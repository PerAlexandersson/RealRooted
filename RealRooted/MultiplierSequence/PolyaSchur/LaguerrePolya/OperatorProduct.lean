module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import RealRooted.Hermite.Poulain
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial factors of Taylor differential operators

Multiplication of an entire symbol by a real polynomial corresponds to
composition with its finite constant-coefficient differential operator.
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- Taylor differential operators are additive in entire symbols. -/
theorem taylorDifferentialOperator_add {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (p : ℝ[X]) :
    taylorDifferentialOperator (fun z => f z + g z) p =
      taylorDifferentialOperator f p + taylorDifferentialOperator g p := by
  have hd (k : ℕ) : iteratedDeriv k (fun z => f z + g z) 0 =
      iteratedDeriv k f 0 + iteratedDeriv k g 0 :=
    iteratedDeriv_fun_add hf.contDiff.contDiffAt hg.contDiff.contDiffAt
  simp only [taylorDifferentialOperator, hd, add_div, Complex.add_re, map_add,
    add_mul, Finset.sum_add_distrib]

/-- A real scalar on the symbol becomes the same scalar on the polynomial output. -/
theorem taylorDifferentialOperator_real_mul (a : ℝ) (f : ℂ → ℂ) (p : ℝ[X]) :
    taylorDifferentialOperator (fun z => (a : ℂ) * f z) p =
      C a * taylorDifferentialOperator f p := by
  simp only [taylorDifferentialOperator, iteratedDeriv_const_mul_field,
    mul_div_assoc, re_ofReal_mul, map_mul, Finset.mul_sum, mul_assoc]

/-- Multiplication of the symbol by its variable shifts its Taylor coefficients. -/
private theorem iteratedDeriv_mul_id_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (k : ℕ) :
    iteratedDeriv (k + 1) (fun z => z * f z) 0 = (k + 1 : ℂ) * iteratedDeriv k f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiff.contDiffAt]
  simp [iteratedDeriv_fun_id_zero, mul_ite, ite_mul]

/-- Multiplication of an entire symbol by its variable differentiates the output. -/
theorem taylorDifferentialOperator_id_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (p : ℝ[X]) :
    taylorDifferentialOperator (fun z => z * f z) p =
      (taylorDifferentialOperator f p).derivative := by
  classical
  have hcoef (k : ℕ) :
      iteratedDeriv (k + 1) (fun z => z * f z) 0 / (k + 1).factorial =
        iteratedDeriv k f 0 / k.factorial := by
    rw [iteratedDeriv_mul_id_zero hf, Nat.factorial_succ]
    push_cast
    field_simp
  rw [taylorDifferentialOperator, Finset.sum_range_succ', taylorDifferentialOperator,
    map_sum, Finset.sum_range_succ]
  simp only [iteratedDeriv_zero, zero_mul, zero_div, zero_re, map_zero,
    zero_mul, add_zero, hcoef, derivative_C_mul, ← Function.iterate_succ_apply']
  rw [iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)]
  simp

/-- Polynomial factors of an entire symbol act by composition of differential operators. -/
theorem taylorDifferentialOperator_polynomial_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (q p : ℝ[X]) :
    taylorDifferentialOperator (fun z => (q.map ofRealHom).eval z * f z) p =
      applyAsDifferentialOperator q (taylorDifferentialOperator f p) := by
  induction q using Polynomial.induction_on with
  | C a =>
      simpa [applyAsDifferentialOperator_C] using taylorDifferentialOperator_real_mul a f p
  | add q r ihq ihr =>
      have heq : (fun z => ((q + r).map ofRealHom).eval z * f z) =
          fun z => (q.map ofRealHom).eval z * f z + (r.map ofRealHom).eval z * f z := by
        funext z
        simp [Polynomial.map_add, eval_add, add_mul]
      rw [heq, taylorDifferentialOperator_add (by fun_prop) (by fun_prop), ihq, ihr,
        applyAsDifferentialOperator_add]
  | monomial n a ih =>
      rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring,
        applyAsDifferentialOperator_X_mul]
      have heq : (fun z => ((X * (C a * X ^ n)).map ofRealHom).eval z * f z) =
          fun z => z * (((C a * X ^ n).map ofRealHom).eval z * f z) := by
        funext z
        simp [Polynomial.map_mul, eval_mul, mul_assoc]
      rw [heq, taylorDifferentialOperator_id_mul (by fun_prop), ih]

/-- A Taylor differential operator cannot increase the input degree. -/
theorem natDegree_taylorDifferentialOperator_le (f : ℂ → ℂ) (p : ℝ[X]) :
    (taylorDifferentialOperator f p).natDegree ≤ p.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_iterate_derivative p k).trans (Nat.sub_le _ _))

/-- Only the constant Taylor coefficient contributes to the top input degree. -/
theorem coeff_taylorDifferentialOperator_natDegree (f : ℂ → ℂ) (p : ℝ[X]) :
    (taylorDifferentialOperator f p).coeff p.natDegree = (f 0).re * p.leadingCoeff := by
  rw [taylorDifferentialOperator, finsetSum_coeff, Finset.sum_eq_single 0]
  · simp [coeff_natDegree]
  · intro k _ hk
    rw [coeff_C_mul, coeff_iterate_derivative,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk))]
    simp
  · simp

/-- A nonzero real constant Taylor coefficient prevents annihilation of any nonzero input. -/
theorem taylorDifferentialOperator_ne_zero {f : ℂ → ℂ} {p : ℝ[X]}
    (hf : (f 0).re ≠ 0) (hp : p ≠ 0) : taylorDifferentialOperator f p ≠ 0 := by
  intro hz
  have h := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hz
  rw [coeff_taylorDifferentialOperator_natDegree, coeff_zero] at h
  exact mul_ne_zero hf (leadingCoeff_ne_zero.mpr hp) h

/-- A nonzero real constant Taylor coefficient preserves the exact input degree. -/
theorem natDegree_taylorDifferentialOperator {f : ℂ → ℂ} {p : ℝ[X]}
    (hf : (f 0).re ≠ 0) (hp : p ≠ 0) :
    (taylorDifferentialOperator f p).natDegree = p.natDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_taylorDifferentialOperator_le f p)
    (by rw [coeff_taylorDifferentialOperator_natDegree];
        exact mul_ne_zero hf (leadingCoeff_ne_zero.mpr hp))

end RealRooted
