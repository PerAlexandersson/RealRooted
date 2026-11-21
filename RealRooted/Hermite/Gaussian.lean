module

public import RealRooted.Hermite.Homogeneous
import Mathlib.Tactic

/-!
# Gaussian coefficient evaluation

The finite functional sends `Xʲ` to `Hⱼ(0,s)`. Its integration-by-parts identity
is purely algebraic. We use it to prove the pairing identity in the unpublished
Grace-apolarity proof of RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- The monic homogeneous Hermite polynomial, with `s` fixed. -/
noncomputable def hermiteHomogeneousPoly (s : ℂ) (n : ℕ) : ℂ[X] :=
  hermiteHomogeneous X (C s) n

/-- Differentiating the homogeneous Hermite family lowers its index. -/
theorem derivative_hermiteHomogeneousPoly (s : ℂ) (n : ℕ) :
    (hermiteHomogeneousPoly s (n + 1)).derivative =
      ((n + 1 : ℕ) : ℂ[X]) * hermiteHomogeneousPoly s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteHomogeneousPoly]
  | one => simp [hermiteHomogeneousPoly, hermiteHomogeneous_add_two]; ring
  | more n ih ih' =>
    change (X * hermiteHomogeneousPoly s (n + 2) +
      2 * ((n + 2 : ℕ) : ℂ[X]) * C s * hermiteHomogeneousPoly s (n + 1)).derivative = _
    simp only [derivative_add, derivative_mul, derivative_X, one_mul, ih',
      derivative_ofNat, derivative_natCast, derivative_C, zero_mul, mul_zero,
      add_zero, zero_add, ih]
    change _ = ((n + 3 : ℕ) : ℂ[X]) *
      (X * hermiteHomogeneousPoly s (n + 1) +
        2 * ((n + 1 : ℕ) : ℂ[X]) * C s * hermiteHomogeneousPoly s n)
    have hr : hermiteHomogeneousPoly s (n + 2) =
        X * hermiteHomogeneousPoly s (n + 1) +
          2 * ((n + 1 : ℕ) : ℂ[X]) * C s * hermiteHomogeneousPoly s n := rfl
    rw [hr]
    push_cast
    ring

/-- Homogeneous Hermite coefficients are binomial multiples of their constant terms. -/
theorem coeff_hermiteHomogeneousPoly (s : ℂ) (n k : ℕ) :
    (hermiteHomogeneousPoly s n).coeff k =
      (n.choose k : ℂ) * hermiteHomogeneous 0 s (n - k) := by
  induction n generalizing k with
  | zero => cases k <;> simp [hermiteHomogeneousPoly, coeff_one]
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        coeff_zero_eq_eval_zero]
      exact eval_hermiteHomogeneous (0 : ℂ) s (n + 1)
    | succ k =>
      have hd := congrArg (fun p : ℂ[X] => p.coeff k)
        (derivative_hermiteHomogeneousPoly s n)
      simp only [coeff_derivative, coeff_natCast_mul, ih] at hd
      push_cast at hd
      have hc : (n + 1 : ℂ) * (n.choose k : ℂ) =
          ((n + 1).choose (k + 1) : ℂ) * (k + 1 : ℂ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n k
      have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp only [Nat.succ_sub_succ_eq_sub]
      apply mul_right_cancel₀ hk
      linear_combination hd + hermiteHomogeneous 0 s (n - k) * hc

/-- The homogeneous Hermite polynomial is monic of its indicated degree. -/
theorem hermiteHomogeneousPoly_monic (s : ℂ) (n : ℕ) :
    (hermiteHomogeneousPoly s n).Monic ∧ (hermiteHomogeneousPoly s n).natDegree = n := by
  have hc := coeff_hermiteHomogeneousPoly s n
  have htop : (hermiteHomogeneousPoly s n).coeff n = 1 := by simp [hc]
  have hd : (hermiteHomogeneousPoly s n).natDegree ≤ n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [hc, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul]
  have he := natDegree_eq_of_le_of_coeff_ne_zero hd (by rw [htop]; exact one_ne_zero)
  exact ⟨by rw [Monic, leadingCoeff, he, htop], he⟩

/-- The finite Gaussian coefficient functional, defined without convergence assumptions. -/
noncomputable def gaussianEval (s : ℂ) (p : ℂ[X]) : ℂ :=
  p.sum fun j a => a * hermiteHomogeneous 0 s j

/-- A monomial is evaluated by its Gaussian moment. -/
@[simp] theorem gaussianEval_monomial (s a : ℂ) (j : ℕ) :
    gaussianEval s (monomial j a) = a * hermiteHomogeneous 0 s j := by
  simp [gaussianEval, sum_monomial_index]

/-- Gaussian evaluation of zero is zero. -/
@[simp] theorem gaussianEval_zero (s : ℂ) : gaussianEval s 0 = 0 := by
  simp [gaussianEval]

/-- Gaussian evaluation of one is one. -/
@[simp] theorem gaussianEval_one (s : ℂ) : gaussianEval s 1 = 1 := by
  change (C (1 : ℂ)).sum (fun j a => a * hermiteHomogeneous 0 s j) = 1
  rw [sum_C_index (by simp)]
  simp

/-- Gaussian evaluation is additive. -/
@[simp] theorem gaussianEval_add (s : ℂ) (p q : ℂ[X]) :
    gaussianEval s (p + q) = gaussianEval s p + gaussianEval s q := by
  exact sum_add_index p q _ (by simp) (by intros; ring)

/-- A constant factor pulls out of Gaussian evaluation. -/
@[simp] theorem gaussianEval_C_mul (s a : ℂ) (p : ℂ[X]) :
    gaussianEval s (C a * p) = a * gaussianEval s p := by
  change (C a * p).sum _ = _
  rw [← smul_eq_C_mul, sum_smul_index _ _ _ (by simp)]
  simp only [gaussianEval, sum_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Gaussian evaluation of a constant is that constant. -/
@[simp] theorem gaussianEval_C (s a : ℂ) : gaussianEval s (C a) = a := by
  simp [gaussianEval, sum_C_index]

/-- Gaussian evaluation of a power is its Gaussian moment. -/
@[simp] theorem gaussianEval_X_pow (s : ℂ) (n : ℕ) :
    gaussianEval s (X ^ n) = hermiteHomogeneous 0 s n := by
  rw [X_pow_eq_monomial, gaussianEval_monomial, one_mul]

/-- Gaussian evaluation of the variable is zero. -/
@[simp] theorem gaussianEval_X (s : ℂ) : gaussianEval s X = 0 := by
  simpa only [pow_one, hermiteHomogeneous_one] using gaussianEval_X_pow s 1

/-- A constant factor on the right pulls out of Gaussian evaluation. -/
@[simp] theorem gaussianEval_mul_C (s a : ℂ) (p : ℂ[X]) :
    gaussianEval s (p * C a) = a * gaussianEval s p := by
  rw [mul_comm, gaussianEval_C_mul]

/-- A natural constant on the right pulls out of Gaussian evaluation. -/
@[simp] theorem gaussianEval_mul_natCast (s : ℂ) (m : ℕ) (p : ℂ[X]) :
    gaussianEval s (p * (m : ℂ[X])) = (m : ℂ) * gaussianEval s p := by
  simpa only [C_eq_natCast] using gaussianEval_mul_C s (m : ℂ) p

/-- A natural constant evaluates to itself. -/
@[simp] theorem gaussianEval_natCast (s : ℂ) (m : ℕ) :
    gaussianEval s (m : ℂ[X]) = (m : ℂ) := by
  simpa only [C_eq_natCast] using gaussianEval_C s (m : ℂ)

/-- A numeral factor on the right pulls out of Gaussian evaluation. -/
@[simp] theorem gaussianEval_mul_ofNat (s : ℂ) (m : ℕ) [m.AtLeastTwo] (p : ℂ[X]) :
    gaussianEval s (p * ofNat(m)) = (ofNat(m) : ℂ) * gaussianEval s p :=
  gaussianEval_mul_natCast s m p

/-- A numeral evaluates to itself under Gaussian evaluation. -/
@[simp] theorem gaussianEval_ofNat (s : ℂ) (m : ℕ) [m.AtLeastTwo] :
    gaussianEval s ofNat(m) = (ofNat(m) : ℂ) := gaussianEval_natCast s m

/-- Algebraic Gaussian integration by parts. -/
theorem gaussianEval_X_mul (s : ℂ) (p : ℂ[X]) :
    gaussianEval s (X * p) = 2 * s * gaussianEval s p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q ih ih' => simp [mul_add, derivative_add, ih, ih', mul_add]
  | monomial j a =>
    rw [X_mul_monomial, gaussianEval_monomial]
    cases j with
    | zero => simp only [Nat.zero_add, hermiteHomogeneous_one, monomial_zero_left,
        derivative_C, gaussianEval_zero, mul_zero]
    | succ j =>
      rw [derivative_monomial_succ, gaussianEval_monomial, hermiteHomogeneous_add_two]
      simp only [zero_mul, zero_add]
      push_cast
      ring

/-- Odd Gaussian moments vanish, expressed in the sign form used by apolarity. -/
theorem neg_one_pow_mul_hermiteHomogeneous_zero (s : ℂ) (n : ℕ) :
    (-1 : ℂ) ^ n * hermiteHomogeneous 0 s n = hermiteHomogeneous 0 s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    simp only [hermiteHomogeneous_add_two, zero_mul, zero_add]
    rw [pow_add, show (-1 : ℂ) ^ 2 = 1 by norm_num, mul_one]
    linear_combination (2 * (n + 1 : ℕ) * s) * ih

/-- Scaling the quadratic parameter scales the Gaussian moment by the matching power. -/
theorem hermiteHomogeneous_zero_mul_sq (a s : ℂ) (n : ℕ) :
    hermiteHomogeneous 0 (a ^ 2 * s) n = a ^ n * hermiteHomogeneous 0 s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    simp only [hermiteHomogeneous_add_two, zero_mul, zero_add, ih]
    rw [pow_add]
    ring

/-- Gaussian evaluation commutes with dilation after the quadratic parameter is scaled. -/
theorem gaussianEval_comp_C_mul_X (a s : ℂ) (p : ℂ[X]) :
    gaussianEval s (p.comp (C a * X)) = gaussianEval (a ^ 2 * s) p := by
  induction p using Polynomial.induction_on' with
  | add p q ih ih' => simp [add_comp, ih, ih']
  | monomial n b =>
    have he : (monomial n b).comp (C a * X) = monomial n (b * a ^ n) := by
      simp only [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
        mul_pow, map_mul, map_pow]
      ring
    rw [he, gaussianEval_monomial, gaussianEval_monomial,
      hermiteHomogeneous_zero_mul_sq]
    ring

end RealRooted
