module

public import RealRooted.MultiplierSequence.Infinite
public import RealRooted.SimpleRoots
import RealRooted.MultiplierSequence.JensenSeparation
import RealRooted.MultiplierSequence.JensenDerivative
import RealRooted.MultiplierSequence.ProperPosition
import RealRooted.LinearPowerFamily

/-!
# Consecutive Jensen interlacing for positive multiplier sequences

Strictly positive multiplier coefficients give adjacent Jensen rows with
exact degrees and directed interlacing. This is a sufficient sign hypothesis
for the interlacing consequence of same-sign root separation. Signs of the
zeros of an arbitrary LP symbol alone are not sufficient when Gaussian
factors are allowed.
-/

public section

open Polynomial

namespace RealRooted

/-- Positive multiplier sequences give directed interlacing of consecutive
Jensen degrees with no coefficient shift. -/
theorem strictInterl_jensenPolynomial_succ_of_pos {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (hpos : ∀ k, 0 < gamma k) (d : ℕ) :
    StrictInterl (jensenPolynomial d gamma) (jensenPolynomial (d + 1) gamma) := by
  have hpower : StrictInterl ((X + 1 : ℝ[X]) ^ d) ((X + 1) ^ (d + 1)) := by
    simpa only [C_1] using strictInterl_X_add_C_pow_succ 1 d
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
    jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  exact hgamma.strictInterl_diagonalOperator_of_pos hpos hpower

/-- Positive multiplier coefficients make consecutive Jensen degrees differ
by one, so the directed relation is ordinary root-list interlacing. -/
theorem interlaces_jensenPolynomial_succ_of_pos {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (hpos : ∀ k, 0 < gamma k) (d : ℕ) :
    Interlaces (jensenPolynomial d gamma) (jensenPolynomial (d + 1) gamma) := by
  apply (strictInterl_jensenPolynomial_succ_of_pos hgamma hpos d).toInterlaces
  rw [natDegree_jensenPolynomial (hpos d).ne', natDegree_jensenPolynomial (hpos (d + 1)).ne']

/-- A simple Jensen row with nonzero initial coefficient has no real root
in common with the preceding unshifted row. -/
theorem jensenPolynomial_succ_no_common_root {gamma : ℕ → ℝ} (hzero : gamma 0 ≠ 0)
    (d : ℕ) (hsimple : HasSimpleRoots (jensenPolynomial (d + 1) gamma)) (r : ℝ) :
    ¬ ((jensenPolynomial d gamma).IsRoot r ∧ (jensenPolynomial (d + 1) gamma).IsRoot r) := by
  intro hr
  have hr0 : r ≠ 0 := by
    intro hz
    subst r
    apply hzero
    simpa only [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_jensenPolynomial,
      Nat.zero_le, ite_true, Nat.choose_zero_right, Nat.cast_one, one_mul] using hr.2
  have heuler := congrArg (fun p : ℝ[X] => p.eval r) (jensenPolynomial_euler d gamma)
  simp only [eval_mul, eval_C, eval_add, eval_X, hr.1.eq_zero, hr.2.eq_zero,
    mul_zero, zero_add] at heuler
  exact hsimple.eval_derivative_ne_zero hr.2
    ((mul_eq_zero.mp heuler.symm).resolve_left hr0)

end RealRooted
