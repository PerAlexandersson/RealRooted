module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import RealRooted.Hermite.Homogeneous
public import RealRooted.SimpleRoots
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.Hermite.GeneratingFunction
import RealRooted.BasisTransform.Hermite
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorLinear
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# Strict Gaussian differential operators on polynomials

The symbol `exp(a z + s z²)` acts through the homogeneous Hermite basis
`Hₙ(X+a,s)`. For `s < 0`, its affine raising operator has a strictly negative
derivative term, so every nonzero real-rooted polynomial input acquires simple
real roots. This is a finite-input theorem; no infinite heat series is used.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Differentiating the translated homogeneous Hermite basis lowers its index. -/
theorem derivative_hermiteHomogeneous_affine (a s : ℝ) (n : ℕ) :
    (hermiteHomogeneous (X + C a) (C s) (n + 1)).derivative =
      C (n + 1 : ℝ) * hermiteHomogeneous (X + C a) (C s) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [hermiteHomogeneous_add_two]; ring
  | more n ih ih' =>
      rw [hermiteHomogeneous_add_two]
      simp only [derivative_add, derivative_mul, derivative_X, derivative_C, add_zero,
        one_mul, derivative_ofNat, derivative_natCast, zero_mul, mul_zero,
        zero_add, ih, ih']
      rw [hermiteHomogeneous_add_two]
      push_cast
      simp only [map_add, map_natCast, map_ofNat, map_one]
      ring

/-- Coefficients of translated homogeneous Hermite polynomials are binomial
multiples of their values at the translation parameter. -/
theorem coeff_hermiteHomogeneous_affine (a s : ℝ) (n k : ℕ) :
    (hermiteHomogeneous (X + C a) (C s) n).coeff k =
      (n.choose k : ℝ) * hermiteHomogeneous a s (n - k) := by
  induction n generalizing k with
  | zero => cases k <;> simp [coeff_one]
  | succ n ih =>
      cases k with
      | zero =>
          rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
            coeff_zero_eq_eval_zero]
          have hm := map_hermiteHomogeneous (evalRingHom (0 : ℝ))
            (X + C a) (C s) (n + 1)
          change (hermiteHomogeneous (X + C a) (C s) (n + 1)).eval 0 =
            hermiteHomogeneous ((X + C a).eval 0) ((C s).eval 0) (n + 1) at hm
          simpa only [eval_add, eval_X, eval_C, zero_add] using hm
      | succ k =>
          have hd := congrArg (fun p : ℝ[X] => p.coeff k)
            (derivative_hermiteHomogeneous_affine a s n)
          simp only [coeff_derivative, coeff_C_mul, ih] at hd
          have hc : (n + 1 : ℝ) * (n.choose k : ℝ) =
              ((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℝ) := by
            exact_mod_cast Nat.add_one_mul_choose_eq n k
          have hk : (k + 1 : ℝ) ≠ 0 := by positivity
          simp only [Nat.succ_sub_succ_eq_sub]
          apply mul_right_cancel₀ hk
          linear_combination hd + hermiteHomogeneous a s (n - k) * hc

/-- The translated homogeneous Hermite basis satisfies the Gaussian raising relation. -/
theorem hermiteHomogeneous_affine_raising (a s : ℝ) (n : ℕ) :
    hermiteHomogeneous (X + C a) (C s) (n + 1) =
      (X + C a) * hermiteHomogeneous (X + C a) (C s) n +
        C (2 * s) * (hermiteHomogeneous (X + C a) (C s) n).derivative := by
  cases n with
  | zero => simp
  | succ n =>
      rw [derivative_hermiteHomogeneous_affine, hermiteHomogeneous_add_two]
      push_cast
      simp only [map_add, map_mul, map_natCast, map_ofNat, map_one]
      ring

/-- A quadratic exponential sends a power of the variable to the corresponding
translated homogeneous Hermite polynomial. -/
theorem taylor_exp_quadratic_X_pow (a s : ℝ) (n : ℕ) :
    taylorDifferentialOperator (fun z => exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) (X ^ n) =
      hermiteHomogeneous (X + C a) (C s) n := by
  rw [taylorDifferentialOperator_X_pow]
  have hdata (k : ℕ) :
      (iteratedDeriv k (fun z => exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) 0).re =
        hermiteHomogeneous a s k := by
    rw [iteratedDeriv_exp_quadratic_zero]
    have hm : ((hermiteHomogeneous a s k : ℝ) : ℂ) =
        hermiteHomogeneous (a : ℂ) (s : ℂ) k :=
      map_hermiteHomogeneous ofRealHom a s k
    rw [← hm]
    rfl
  ext k
  rw [coeff_reflect, coeff_hermiteHomogeneous_affine]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, coeff_jensenPolynomial, ite_eq_left (Nat.sub_le _ _), hdata,
      Nat.choose_symm hk]
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hk), coeff_jensenPolynomial,
      ite_eq_right hk, Nat.choose_eq_zero_of_lt (lt_of_not_ge hk), Nat.cast_zero, zero_mul]

/-- The finite Taylor operator of a quadratic exponential is its Hermite basis transform. -/
theorem taylor_exp_quadratic_eq_basisTransform (a s : ℝ) (p : ℝ[X]) :
    taylorDifferentialOperator (fun z => exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) p =
      basisTransform (fun n => hermiteHomogeneous (X + C a) (C s) n) p := by
  rw [taylorDifferentialOperator_eq_basisTransform]
  simp only [taylor_exp_quadratic_X_pow]

/-- A linear exponential symbol acts by real translation of the input. -/
theorem taylor_exp_linear_eq_comp (a : ℝ) (p : ℝ[X]) :
    taylorDifferentialOperator (fun z => exp ((a : ℂ) * z)) p = p.comp (X + C a) := by
  have heq := taylor_exp_quadratic_eq_basisTransform a 0 p
  simp only [ofReal_zero, zero_mul, add_zero, map_zero,
    hermiteHomogeneous_zero_right] at heq
  rw [heq]
  clear heq
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [basisTransform_add, add_comp, hp, hq]
  | monomial n c => simp [basisTransform_monomial, monomial_comp]

/-- A strictly negative Gaussian parameter makes every nonzero real-rooted
polynomial input simple-real-rooted. -/
theorem simple_taylor_exp_quadratic (a : ℝ) {s : ℝ} (hs : s < 0)
    {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) :
    IsSimpleRealRooted
      (taylorDifferentialOperator (fun z => exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) p) := by
  rw [taylor_exp_quadratic_eq_basisTransform]
  apply isSimpleRealRooted_basisTransform_of_raising (a := 1) (b := a) (c := -2 * s)
    (by simp) (by norm_num) (by nlinarith) _ hp hp0
  intro n
  simpa using hermiteHomogeneous_affine_raising a s n

/-- Nonpositive Gaussian parameters preserve splitting, including zero
inputs and the translation boundary at parameter zero. -/
theorem splits_taylor_exp_quadratic (a : ℝ) {s : ℝ} (hs : s ≤ 0)
    {p : ℝ[X]} (hp : p.Splits) :
    (taylorDifferentialOperator (fun z => exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) p).Splits := by
  rcases hs.lt_or_eq with hs | rfl
  · by_cases hp0 : p = 0
    · simp [hp0, taylorDifferentialOperator]
    · exact (simple_taylor_exp_quadratic a hs hp0 hp).2.1
  · simpa only [ofReal_zero, zero_mul, add_zero, taylor_exp_linear_eq_comp]
      using hp.comp_X_add_C a

end RealRooted
