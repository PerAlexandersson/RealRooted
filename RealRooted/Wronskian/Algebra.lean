import RealRooted.EulerOperator
import RealRooted.Mathlib.RingTheory.Polynomial.Wronskian

/-!
# Wronskian algebra and Laguerre inequalities

Reusable Wronskian-algebra and positivity lemmas.

  Several real-rootedness target families (A141689, A272471, A157153-56,
  A268434) reduce their remaining obligations to showing that a Wronskian
  `wronskian p q = p * q' - p' * q` is pointwise nonnegative on `ℝ`, and each
  currently does its own bespoke SOS/positivity transport.  This module
  collects the *general* identities and bounds those arguments share, built
  on top of mathlib's `Polynomial.wronskian` and its bilinearity API:

  * `wronskian_X_mul_right` : `W(p, X*p) = p^2` — the manifestly-SOS fact,
    with the general product form `wronskian_X_mul_right_eq` :
    `W(p, X*q) = X * W(p, q) + p*q`.
  * `wronskian_derivative_right` : `W(p, p') = p*p'' - p'^2`, the negated
    Laguerre form; for a splitting `p` it is pointwise `≤ 0`
    (`wronskian_derivative_right_eval_nonpos`, via `laguerre_form_nonneg`).
  * `iterated_laguerre_form_nonneg` : Laguerre's inequality for every
    iterated derivative of a splitting polynomial.
  * Wronskians of consecutive derivatives, including their pointwise
    nonpositivity for splitting polynomials.
  * `wronskian_thetaPlusOne_right` : closed form for `W(p, θ⁺p)` where
    `θ⁺p = p + X*p'` is the shifted Euler operator, plus the compositional
    form `W(p, θ⁺p) = p*p' + X * W(p, p')`.
  * ℝ-scalar bilinearity conveniences (`wronskian_C_mul_right`,
    `wronskian_linear_combination_right`, …) so that decomposing an
    operator-image Wronskian into simpler Wronskians is a one-liner.
  * Root-localized evaluations (`wronskian_eval_left_root`,
    `wronskian_eval_right_root`) packaging the value of a Wronskian at a
    root of either argument.
  * The A268434-style double-Euler shell `W(p, θ⁺(θ⁺p) + X*p)` decomposed
    through the building blocks above.

The algebraic identities in this file are candidates for generalization into
`RealRooted.Mathlib.RingTheory.Polynomial.Wronskian`; the order statements use
the real-rootedness API and belong in this library.
-/

open Polynomial

namespace RealRooted

private theorem iterate_derivative_eq_zero_or_splits_of_splits
    {p : ℝ[X]} (hp : p.Splits) (k : ℕ) :
    (derivative^[k]) p = 0 ∨ ((derivative^[k]) p).Splits := by
  induction k with
  | zero => exact Or.inr hp
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using eq_zero_or_splits_derivative ih

/-! ### The star SOS identity: `W(p, X*p) = p^2` -/

/-- General product form: multiplying the right argument by `X` scales the
Wronskian by `X` and adds the product term, `W(p, X*q) = X * W(p, q) + p*q`. -/
theorem wronskian_X_mul_right_eq (p q : ℝ[X]) :
    wronskian p (X * q) = X * wronskian p q + p * q :=
  Polynomial.wronskian_X_mul_right_eq p q

/-- **The star lemma.**  `W(p, X*p) = p^2`: the Wronskian of `p` against
`X*p` is a perfect square, hence manifestly pointwise nonnegative. -/
theorem wronskian_X_mul_right (p : ℝ[X]) : wronskian p (X * p) = p ^ 2 :=
  Polynomial.wronskian_X_mul_right p

theorem wronskian_X_mul_right_eval (p : ℝ[X]) (t : ℝ) :
    (wronskian p (X * p)).eval t = p.eval t ^ 2 := by
  rw [wronskian_X_mul_right, eval_pow]

/-- Pointwise nonnegativity of `W(p, X*p)` — no hypothesis on `p` needed. -/
theorem wronskian_X_mul_right_eval_nonneg (p : ℝ[X]) (t : ℝ) :
    0 ≤ (wronskian p (X * p)).eval t := by
  rw [wronskian_X_mul_right_eval]
  positivity

/-! ### The derivative Wronskian and Laguerre's inequality -/

/-- `W(p, p') = p * p'' - p'^2`, the negated Laguerre form of `p`. -/
theorem wronskian_derivative_right (p : ℝ[X]) :
    wronskian p (derivative p) =
      p * derivative (derivative p) - derivative p ^ 2 :=
  Polynomial.wronskian_derivative_right p

theorem wronskian_derivative_right_eval (p : ℝ[X]) (t : ℝ) :
    (wronskian p (derivative p)).eval t =
      p.eval t * (derivative (derivative p)).eval t -
        (derivative p).eval t ^ 2 := by
  rw [wronskian_derivative_right]
  simp

/-- Auxiliary form of **Laguerre's inequality** for an explicit product of
real linear factors: if `p = C c * ∏_{r ∈ s} (X - C r)` then
`0 ≤ p'(t)^2 - p(t) * p''(t)` for every real `t`.  Adjoining one factor
`X - C a` transforms the Laguerre form into
`q(t)^2 + (t - a)^2 * (q'(t)^2 - q(t) * q''(t))`, so the claim follows by
induction on the multiset of roots with no analytic input. -/
private lemma laguerre_form_nonneg_prod (c : ℝ) (s : Multiset ℝ) (t : ℝ) :
    0 ≤ (C c * (s.map fun r => X - C r).prod : ℝ[X]).derivative.eval t ^ 2 -
      (C c * (s.map fun r => X - C r).prod : ℝ[X]).eval t *
        (C c * (s.map fun r => X - C r).prod
          : ℝ[X]).derivative.derivative.eval t := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have hrw : (C c * ((a ::ₘ s).map fun r => X - C r).prod : ℝ[X]) =
          (X - C a) * (C c * (s.map fun r => X - C r).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]
        ring
      set q : ℝ[X] := C c * (s.map fun r => X - C r).prod with hq
      rw [hrw]
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
        derivative_add, sub_zero, one_mul, eval_add, eval_mul, eval_sub,
        eval_X, eval_C]
      nlinarith [mul_nonneg (sq_nonneg (t - a)) ih, sq_nonneg (q.eval t)]

/-- **Laguerre's inequality.**  If a real polynomial has all real roots,
then `p'(t)^2 - p(t) * p''(t) ≥ 0` for every real `t`. -/
theorem laguerre_form_nonneg {p : ℝ[X]} (hp : p.Splits) (t : ℝ) :
    0 ≤ (derivative p).eval t ^ 2 -
      p.eval t * (derivative (derivative p)).eval t := by
  conv_lhs => rw [show (0 : ℝ) = 0 from rfl]
  rw [hp.eq_prod_roots]
  exact laguerre_form_nonneg_prod p.leadingCoeff p.roots t

/-- For a splitting `p`, the derivative Wronskian `W(p, p')` is pointwise
nonpositive on all of `ℝ` (Laguerre's inequality in Wronskian form). -/
theorem wronskian_derivative_right_eval_nonpos {p : ℝ[X]} (hp : p.Splits)
    (t : ℝ) : (wronskian p (derivative p)).eval t ≤ 0 := by
  rw [wronskian_derivative_right_eval]
  linarith [laguerre_form_nonneg hp t]

/-! ### The Newton-Laguerre hierarchy -/

/-- Laguerre's inequality for the `k`-th derivative of a splitting
polynomial. The derivative is either zero or itself splits. -/
theorem iterated_laguerre_form_nonneg {p : ℝ[X]} (hp : p.Splits) (k : ℕ)
    (t : ℝ) :
    0 ≤ (derivative ((derivative^[k]) p)).eval t ^ 2 -
      ((derivative^[k]) p).eval t *
        (derivative (derivative ((derivative^[k]) p))).eval t := by
  rcases iterate_derivative_eq_zero_or_splits_of_splits hp k with h | h
  · simp [h]
  · exact laguerre_form_nonneg h t

/-! ### The shifted Euler operator `θ⁺ = 1 + X·d/dX` -/

/-- Compositional form: `W(p, θ⁺p) = p*p' + X * W(p, p')`. -/
theorem wronskian_thetaPlusOne_right_eq (p : ℝ[X]) :
    wronskian p (thetaPlusOne p) =
      p * derivative p + X * wronskian p (derivative p) := by
  rw [thetaPlusOne, theta, wronskian_add_right, wronskian_self_eq_zero,
    add_zero, wronskian_X_mul_right_eq]
  ring

/-- Closed form: `W(p, θ⁺p) = p*p' + X * (p*p'' - p'^2)`. -/
theorem wronskian_thetaPlusOne_right (p : ℝ[X]) :
    wronskian p (thetaPlusOne p) =
      p * derivative p +
        X * (p * derivative (derivative p) - derivative p ^ 2) := by
  rw [wronskian_thetaPlusOne_right_eq, wronskian_derivative_right]

theorem wronskian_thetaPlusOne_right_eval (p : ℝ[X]) (t : ℝ) :
    (wronskian p (thetaPlusOne p)).eval t =
      p.eval t * (derivative p).eval t +
        t * (p.eval t * (derivative (derivative p)).eval t -
          (derivative p).eval t ^ 2) := by
  rw [wronskian_thetaPlusOne_right]
  simp

/-- The plain Euler operator `θp = X*p'`: `W(p, θp) = X * W(p, p') + p*p'`. -/
theorem wronskian_theta_right (p : ℝ[X]) :
    wronskian p (theta p) =
      X * wronskian p (derivative p) + p * derivative p := by
  rw [theta, wronskian_X_mul_right_eq]

/-! ### ℝ-scalar bilinearity conveniences -/

theorem wronskian_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    wronskian p (C a * q) = C a * wronskian p q :=
  Polynomial.wronskian_C_mul_right a p q

theorem wronskian_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    wronskian (C a * p) q = C a * wronskian p q :=
  Polynomial.wronskian_C_mul_left a p q

theorem wronskian_smul_right (a : ℝ) (p q : ℝ[X]) :
    wronskian p (a • q) = a • wronskian p q :=
  Polynomial.wronskian_smul_right a p q

theorem wronskian_smul_left (a : ℝ) (p q : ℝ[X]) :
    wronskian (a • p) q = a • wronskian p q :=
  Polynomial.wronskian_smul_left a p q

/-- Decompose the Wronskian of `p` against an ℝ-linear combination:
`W(p, a*q + b*r) = a * W(p, q) + b * W(p, r)`. -/
theorem wronskian_linear_combination_right (p q r : ℝ[X]) (a b : ℝ) :
    wronskian p (C a * q + C b * r) =
      C a * wronskian p q + C b * wronskian p r :=
  Polynomial.wronskian_C_mul_add_C_mul_right p q r a b

theorem wronskian_sub_right (p q r : ℝ[X]) :
    wronskian p (q - r) = wronskian p q - wronskian p r :=
  Polynomial.wronskian_sub_right p q r

theorem wronskian_sub_left (p q r : ℝ[X]) :
    wronskian (p - q) r = wronskian p r - wronskian q r :=
  Polynomial.wronskian_sub_left p q r

/-! ### Root-localized evaluations -/

/-- Value of the Wronskian at a root of the left argument:
`p(r) = 0 → W(p, q)(r) = -p'(r) * q(r)`. -/
theorem wronskian_eval_left_root {p : ℝ[X]} {r : ℝ} (hr : p.IsRoot r)
    (q : ℝ[X]) :
    (wronskian p q).eval r = -((derivative p).eval r * q.eval r) :=
  Polynomial.wronskian_eval_left_root hr q

/-- Value of the Wronskian at a root of the right argument:
`q(s) = 0 → W(p, q)(s) = p(s) * q'(s)`. -/
theorem wronskian_eval_right_root (p : ℝ[X]) {q : ℝ[X]} {s : ℝ}
    (hs : q.IsRoot s) :
    (wronskian p q).eval s = p.eval s * (derivative q).eval s :=
  Polynomial.wronskian_eval_right_root p hs

/-! ### The double-Euler shell (A268434 shape) -/

/-- Explicit expansion of the double shift: `θ⁺(θ⁺p) = X²p'' + 3Xp' + p`. -/
theorem thetaPlusOne_thetaPlusOne (p : ℝ[X]) :
    thetaPlusOne (thetaPlusOne p) =
      X ^ 2 * derivative (derivative p) + 3 * (X * derivative p) + p := by
  simp only [thetaPlusOne, theta, derivative_add, derivative_mul,
    derivative_X, one_mul]
  ring

/-- Closed form for the double-Euler Wronskian:
`W(p, θ⁺(θ⁺p)) = X²(p*p''' - p'*p'') + X(5p*p'' - 3p'^2) + 3p*p'`. -/
theorem wronskian_thetaPlusOne_sq_right (p : ℝ[X]) :
    wronskian p (thetaPlusOne (thetaPlusOne p)) =
      X ^ 2 * (p * derivative (derivative (derivative p)) -
          derivative p * derivative (derivative p)) +
        X * (5 * (p * derivative (derivative p)) - 3 * derivative p ^ 2) +
        3 * (p * derivative p) := by
  simp only [thetaPlusOne, theta, wronskian, derivative_add, derivative_mul,
    derivative_X, one_mul]
  ring

/-- **Library composition demo (A268434 shell).**  The Wronskian of `p`
against the double-Euler-plus-pencil image `θ⁺(θ⁺p) + X*p` splits, by
bilinearity and the star lemma, into the double-Euler Wronskian plus the
manifestly nonnegative square `p^2`. -/
theorem wronskian_doubleEuler_shell (p : ℝ[X]) :
    wronskian p (thetaPlusOne (thetaPlusOne p) + X * p) =
      wronskian p (thetaPlusOne (thetaPlusOne p)) + p ^ 2 := by
  rw [wronskian_add_right, wronskian_X_mul_right]

/-! ### Turán-type second Laguerre inequality -/

/-- **Second Laguerre (Turán-type) inequality.**  If `p` has all real roots,
so does `p'` (or it vanishes), hence Laguerre's inequality applies one level
up: `p''(t)^2 - p'(t) * p'''(t) ≥ 0` for every real `t`. -/
theorem laguerre_form_derivative_nonneg {p : ℝ[X]} (hp : p.Splits) (t : ℝ) :
    0 ≤ (derivative (derivative p)).eval t ^ 2 -
      (derivative p).eval t *
        (derivative (derivative (derivative p))).eval t := by
  rcases eq_zero_or_splits_derivative (Or.inr hp) with h0 | hs
  · simp [h0]
  · exact laguerre_form_nonneg hs t

/-! ### Wronskians of consecutive derivatives -/

/-- Leibniz rule for the derivative of a Wronskian. -/
theorem derivative_wronskian (a b : ℝ[X]) :
    derivative (wronskian a b) =
      wronskian a (derivative b) + wronskian (derivative a) b :=
  Polynomial.derivative_wronskian a b

/-- Differentiating `W(p, p')` gives `W(p, p'')`. -/
theorem derivative_wronskian_derivative_right (p : ℝ[X]) :
    derivative (wronskian p (derivative p)) =
      wronskian p (derivative (derivative p)) :=
  Polynomial.derivative_wronskian_derivative_right p

/-- The Wronskian `W(p', p'')` is the negated derivative Laguerre form. -/
theorem wronskian_derivative_derivative (p : ℝ[X]) :
    wronskian (derivative p) (derivative (derivative p)) =
      derivative p * derivative (derivative (derivative p)) -
        derivative (derivative p) ^ 2 :=
  Polynomial.wronskian_derivative_derivative p

theorem wronskian_derivative_derivative_eval (p : ℝ[X]) (t : ℝ) :
    (wronskian (derivative p) (derivative (derivative p))).eval t =
      (derivative p).eval t *
          (derivative (derivative (derivative p))).eval t -
        (derivative (derivative p)).eval t ^ 2 := by
  rw [wronskian_derivative_derivative]
  simp

/-- For a splitting polynomial, `W(p', p'')` is pointwise nonpositive. -/
theorem wronskian_derivative_derivative_eval_nonpos {p : ℝ[X]}
    (hp : p.Splits) (t : ℝ) :
    (wronskian (derivative p) (derivative (derivative p))).eval t ≤ 0 := by
  rw [wronskian_derivative_derivative_eval]
  linarith [laguerre_form_derivative_nonneg hp t]

/-- The second-derivative Wronskian in expanded form. -/
theorem wronskian_self_second_derivative (p : ℝ[X]) :
    wronskian p (derivative (derivative p)) =
      p * derivative (derivative (derivative p)) -
        derivative p * derivative (derivative p) :=
  Polynomial.wronskian_self_second_derivative p

theorem wronskian_self_second_derivative_eval (p : ℝ[X]) (t : ℝ) :
    (wronskian p (derivative (derivative p))).eval t =
      p.eval t * (derivative (derivative (derivative p))).eval t -
        (derivative p).eval t * (derivative (derivative p)).eval t := by
  rw [wronskian_self_second_derivative]
  simp

/-- The Wronskian of consecutive iterated derivatives. -/
theorem wronskian_iterate_derivative_succ (p : ℝ[X]) (k : ℕ) :
    wronskian ((derivative^[k]) p) ((derivative^[k + 1]) p) =
      (derivative^[k]) p * (derivative^[k + 2]) p -
        (derivative^[k + 1]) p ^ 2 :=
  Polynomial.wronskian_iterate_derivative_succ p k

/-- Every consecutive-derivative Wronskian of a splitting polynomial is
pointwise nonpositive. -/
theorem wronskian_iterate_derivative_succ_eval_nonpos {p : ℝ[X]}
    (hp : p.Splits) (k : ℕ) (t : ℝ) :
    (wronskian ((derivative^[k]) p) ((derivative^[k + 1]) p)).eval t ≤ 0 := by
  rw [wronskian_iterate_derivative_succ]
  have h := iterated_laguerre_form_nonneg hp k t
  simp only [Function.iterate_succ_apply', eval_sub, eval_mul, eval_pow] at h ⊢
  linarith

/-! ### The double-Euler-vs-`X`-pencil residual (A268434 crux shape) -/

/-- **The residual identity.**  For any `p`, the Wronskian of the double
Euler image `θ⁺(θ⁺p)` against `X*p` collapses to
`p² + X²(3p'² − 4pp'') + X³(p'p'' − pp''')`.  The first summand is a square
and, for splitting `p`, `3p'² − 4pp'' = 3(p'² − pp'') − pp''` combines a
Laguerre form with `-pp''`; the cubic coefficient is `-W(p, p'')`. -/
theorem wronskian_thetaPlusOne_sq_X_mul (p : ℝ[X]) :
    wronskian (thetaPlusOne (thetaPlusOne p)) (X * p) =
      p ^ 2 +
        X ^ 2 * (3 * derivative p ^ 2 -
          4 * (p * derivative (derivative p))) +
        X ^ 3 * (derivative p * derivative (derivative p) -
          p * derivative (derivative (derivative p))) := by
  simp only [thetaPlusOne, theta, wronskian, derivative_add, derivative_mul,
    derivative_X, one_mul]
  ring

/-- Coefficient form of a Wronskian.  The coefficient of `X^l` in
`W(p,q)` is the skew convolution
`∑_{i+j=l+1} (j-i) p_i q_j`.

This avoids separate shifted convolutions for the two differentiated terms
and is useful when the coefficients of one input have a closed form. -/
theorem coeff_wronskian (p q : ℝ[X]) (l : ℕ) :
    (wronskian p q).coeff l =
      ∑ ij ∈ Finset.antidiagonal (l + 1),
        (((ij.2 : ℝ) - (ij.1 : ℝ)) * p.coeff ij.1 * q.coeff ij.2) := by
  have hpoly : X * wronskian p q = p * theta q - theta p * q := by
    simp only [wronskian, theta]
    ring
  have hcoeff := congrArg (fun r : ℝ[X] ↦ r.coeff (l + 1)) hpoly
  rw [coeff_X_mul, coeff_sub, coeff_mul, coeff_mul] at hcoeff
  simp only [coeff_theta] at hcoeff
  calc
    (wronskian p q).coeff l =
        (∑ ij ∈ Finset.antidiagonal (l + 1),
            p.coeff ij.1 * ((ij.2 : ℝ) * q.coeff ij.2)) -
          ∑ ij ∈ Finset.antidiagonal (l + 1),
            ((ij.1 : ℝ) * p.coeff ij.1) * q.coeff ij.2 := hcoeff
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ij _
      ring

theorem wronskian_thetaPlusOne_sq_X_mul_eval (p : ℝ[X]) (t : ℝ) :
    (wronskian (thetaPlusOne (thetaPlusOne p)) (X * p)).eval t =
      p.eval t ^ 2 +
        t ^ 2 * (3 * (derivative p).eval t ^ 2 -
          4 * (p.eval t * (derivative (derivative p)).eval t)) +
        t ^ 3 * ((derivative p).eval t *
            (derivative (derivative p)).eval t -
          p.eval t *
            (derivative (derivative (derivative p))).eval t) := by
  rw [wronskian_thetaPlusOne_sq_X_mul]
  simp

/-- At `t = 0` the residual is the square of the constant term. -/
theorem wronskian_thetaPlusOne_sq_X_mul_eval_zero (p : ℝ[X]) :
    (wronskian (thetaPlusOne (thetaPlusOne p)) (X * p)).eval 0 =
      p.eval 0 ^ 2 := by
  rw [wronskian_thetaPlusOne_sq_X_mul_eval]
  ring

/-- **Root localization of the residual.**  At a root `r` of `p` the residual
factors as `r² p'(r) (3 p'(r) + r p''(r))`; positivity of the residual on
all of `ℝ` therefore forces the root bracket `3 + r p''(r)/p'(r) > 0` at
every simple root of `p`. -/
theorem wronskian_thetaPlusOne_sq_X_mul_eval_root {p : ℝ[X]} {r : ℝ}
    (hr : p.IsRoot r) :
    (wronskian (thetaPlusOne (thetaPlusOne p)) (X * p)).eval r =
      r ^ 2 * (derivative p).eval r *
        (3 * (derivative p).eval r +
          r * (derivative (derivative p)).eval r) := by
  rw [wronskian_thetaPlusOne_sq_X_mul_eval, hr.eq_zero]
  ring

/-- Laguerre-based partial signing of the residual: the `X⁰` and (three of
the four) `X²`-contributions are controlled, leaving exactly
`residual ≥ p² - t²·p(t)p''(t) + t³·(p'p'' - pp''')(t)` for splitting `p`.
Recorded as the exact decomposition through the Laguerre form. -/
theorem wronskian_thetaPlusOne_sq_X_mul_eval_ge {p : ℝ[X]} (hp : p.Splits)
    (t : ℝ) :
    p.eval t ^ 2 -
        t ^ 2 * (p.eval t * (derivative (derivative p)).eval t) +
        t ^ 3 * ((derivative p).eval t *
            (derivative (derivative p)).eval t -
          p.eval t *
            (derivative (derivative (derivative p))).eval t) ≤
      (wronskian (thetaPlusOne (thetaPlusOne p)) (X * p)).eval t := by
  rw [wronskian_thetaPlusOne_sq_X_mul_eval]
  nlinarith [mul_nonneg (sq_nonneg t) (laguerre_form_nonneg hp t)]

end RealRooted
