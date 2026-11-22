module

public import RealRooted.MultiplierSequence
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Same-sign separation of consecutive Jensen polynomials

The Euler identity relates adjacent degree parameters with no shift in the
coefficient sequence. Rolle's theorem applied to `Jₙ(x)/xⁿ` shows that any
two same-sign real zeros of `Jₙ` enclose a zero of `Jₙ₋₁`. This needs no
Laguerre–Pólya or real-rootedness assumption.
-/

public section

open Polynomial Set

namespace RealRooted

/-- The binomial coefficient already vanishes outside the Jensen degree bound. -/
private theorem coeff_jensen_eq_choose (d k : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial d gamma).coeff k = (d.choose k : ℝ) * gamma k := by
  by_cases hk : k ≤ d
  · simp [coeff_jensenPolynomial, hk]
  · simp [coeff_jensenPolynomial, hk, Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]

/-- Adjacent unshifted Jensen polynomials satisfy the Euler derivative identity. -/
theorem jensenPolynomial_euler (d : ℕ) (gamma : ℕ → ℝ) :
    C (d + 1 : ℝ) * jensenPolynomial (d + 1) gamma =
      C (d + 1 : ℝ) * jensenPolynomial d gamma +
        X * (jensenPolynomial (d + 1) gamma).derivative := by
  ext k
  simp only [coeff_C_mul, coeff_add, coeff_X_mul_derivative, coeff_jensen_eq_choose]
  by_cases hk : k ≤ d + 1
  · have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_succ_eq d k)
    push_cast [Nat.cast_sub hk] at hc
    linear_combination -gamma k * hc
  · rw [Nat.choose_eq_zero_of_lt (by lia : d + 1 < k),
      Nat.choose_eq_zero_of_lt (by lia : d < k)]
    simp

/-- The closed interval between two numbers of the same sign avoids zero. -/
private theorem ne_zero_on_same_sign_interval {s t x : ℝ}
    (hsign : 0 < s * t) (hx : x ∈ Icc s t) : x ≠ 0 := by
  rcases mul_pos_iff.mp hsign with hpos | hneg
  · linarith [hx.1, hpos.1]
  · linarith [hx.2, hneg.2]

/-- Any two same-sign roots of a Jensen polynomial enclose a root of the
preceding unshifted Jensen polynomial. They need not be consecutive or simple. -/
theorem jensenPolynomial_same_sign_separation (d : ℕ) (gamma : ℕ → ℝ)
    {s t : ℝ} (hst : s < t) (hsign : 0 < s * t)
    (hs : (jensenPolynomial (d + 1) gamma).IsRoot s)
    (ht : (jensenPolynomial (d + 1) gamma).IsRoot t) :
    ∃ x ∈ Ioo s t, (jensenPolynomial d gamma).IsRoot x := by
  let p := jensenPolynomial (d + 1) gamma
  have hne (x : ℝ) (hx : x ∈ Icc s t) : x ≠ 0 :=
    ne_zero_on_same_sign_interval hsign hx
  have hc : ContinuousOn (fun x => p.eval x / x ^ (d + 1)) (Icc s t) :=
    p.continuous.continuousOn.div (continuous_id.pow _).continuousOn
      (fun x hx => pow_ne_zero _ (hne x hx))
  have he : p.eval s / s ^ (d + 1) = p.eval t / t ^ (d + 1) := by
    rw [hs.eq_zero, ht.eq_zero, zero_div, zero_div]
  obtain ⟨x, hx, hd⟩ := exists_hasDerivAt_eq_zero hst hc he
    (fun x hx => (p.hasDerivAt x).div ((hasDerivAt_id x).pow (d + 1))
      (pow_ne_zero _ (hne x ⟨hx.1.le, hx.2.le⟩)))
  have hx0 : x ≠ 0 := hne x ⟨hx.1.le, hx.2.le⟩
  have hnum : p.derivative.eval x * x ^ (d + 1) -
      p.eval x * ((d + 1 : ℝ) * x ^ d) = 0 := by
    simpa [pow_ne_zero _ hx0] using hd
  have hmul : x ^ d * (x * p.derivative.eval x - (d + 1 : ℝ) * p.eval x) = 0 := by
    rw [pow_succ] at hnum
    linear_combination hnum
  have hcore := (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hx0)
  have heuler := congrArg (fun q : ℝ[X] => q.eval x) (jensenPolynomial_euler d gamma)
  simp only [eval_mul, eval_C, eval_add, eval_X] at heuler
  have hprev : (d + 1 : ℝ) * (jensenPolynomial d gamma).eval x = 0 := by
    change (d + 1 : ℝ) * p.eval x =
      (d + 1 : ℝ) * (jensenPolynomial d gamma).eval x + x * p.derivative.eval x at heuler
    linear_combination -heuler - hcore
  exact ⟨x, hx, (mul_eq_zero.mp hprev).resolve_left (by positivity)⟩

end RealRooted
