/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.Wronskian.Algebra

/-!
# Degree-weighted and polar Laguerre inequalities

This file strengthens Laguerre's inequality by its degree-weighted
Cauchy--Schwarz form and by a root-location-sensitive Euler form.  The latter
simultaneously controls the Wronskians against `thetaPlusOne` and `polarTheta`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The polynomial Laguerre form `p' ^ 2 - p * p''`. -/
def laguerreForm (p : ℝ[X]) : ℝ[X] :=
  derivative p ^ 2 - p * derivative (derivative p)

@[simp] theorem eval_laguerreForm (p : ℝ[X]) (t : ℝ) :
    (laguerreForm p).eval t =
      (derivative p).eval t ^ 2 -
        p.eval t * (derivative (derivative p)).eval t := by
  simp [laguerreForm]

/-- The Euler-weighted Laguerre form `p * p' - X * (p' ^ 2 - p * p'')`. -/
def thetaLaguerreForm (p : ℝ[X]) : ℝ[X] :=
  p * derivative p - X * laguerreForm p

@[simp] theorem eval_thetaLaguerreForm (p : ℝ[X]) (t : ℝ) :
    (thetaLaguerreForm p).eval t =
      p.eval t * (derivative p).eval t -
        t * ((derivative p).eval t ^ 2 -
          p.eval t * (derivative (derivative p)).eval t) := by
  simp [thetaLaguerreForm]

/-- A single root-product induction supplying both strengthened Laguerre
bounds used below. -/
private theorem product_laguerre_bounds (c : ℝ) (s : Multiset ℝ) (t : ℝ) :
    (C c * (s.map fun r => X - C r).prod : ℝ[X]).derivative.eval t ^ 2 ≤
        (s.card : ℝ) *
          ((C c * (s.map fun r => X - C r).prod : ℝ[X]).derivative.eval t ^ 2 -
            (C c * (s.map fun r => X - C r).prod : ℝ[X]).eval t *
              (C c * (s.map fun r => X - C r).prod
                : ℝ[X]).derivative.derivative.eval t) ∧
      ((∀ r ∈ s, r ≤ 0) →
        0 ≤ (C c * (s.map fun r => X - C r).prod : ℝ[X]).eval t *
            (C c * (s.map fun r => X - C r).prod : ℝ[X]).derivative.eval t -
          t * ((C c * (s.map fun r => X - C r).prod
                : ℝ[X]).derivative.eval t ^ 2 -
            (C c * (s.map fun r => X - C r).prod : ℝ[X]).eval t *
              (C c * (s.map fun r => X - C r).prod
                : ℝ[X]).derivative.derivative.eval t)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have hrw : (C c * ((a ::ₘ s).map fun r => X - C r).prod : ℝ[X]) =
          (X - C a) * (C c * (s.map fun r => X - C r).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]
        ring
      set q : ℝ[X] := C c * (s.map fun r => X - C r).prod with hq
      constructor
      · rw [hrw]
        simp only [Multiset.card_cons, derivative_mul, derivative_sub,
          derivative_X, derivative_C, sub_zero, one_mul, derivative_add,
          eval_add, eval_mul, eval_sub, eval_X, eval_C]
        push_cast
        rcases eq_or_ne s 0 with rfl | hsne
        · simp only [Multiset.card_zero, Multiset.map_zero, Multiset.prod_zero,
            mul_one] at *
          simp only [hq]
          simp
        · have hcard : (0 : ℝ) < (s.card : ℝ) := by
            exact_mod_cast Multiset.card_pos.mpr hsne
          nlinarith [ih.1,
            sq_nonneg ((s.card : ℝ) * q.eval t -
              (t - a) * q.derivative.eval t),
            mul_nonneg
              (mul_nonneg (by positivity : (0 : ℝ) ≤ (s.card : ℝ) + 1)
                (sq_nonneg (t - a)))
              (by
                nlinarith [ih.1] :
                  0 ≤ (s.card : ℝ) *
                      (q.derivative.eval t ^ 2 -
                        q.eval t * q.derivative.derivative.eval t) -
                    q.derivative.eval t ^ 2)]
      · intro hs
        have ha : a ≤ 0 := hs a (by simp)
        have htail : ∀ r ∈ s, r ≤ 0 := fun r hr => hs r (by simp [hr])
        have ih' := ih.2 htail
        rw [hrw]
        simp only [derivative_mul, derivative_sub, derivative_X,
          derivative_C, derivative_add, sub_zero, one_mul, eval_add,
          eval_mul, eval_sub, eval_X, eval_C]
        nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sq_nonneg (q.eval t)),
          mul_nonneg (sq_nonneg (t - a)) ih']

/-- Laguerre's inequality expressed through `laguerreForm`. -/
theorem laguerreForm_eval_nonneg {p : ℝ[X]} (hp : p.Splits) (t : ℝ) :
    0 ≤ (laguerreForm p).eval t := by
  simpa using laguerre_form_nonneg hp t

/-- **Degree-weighted Laguerre inequality.** For a split polynomial,
`p'(t) ^ 2 ≤ deg(p) * (p'(t) ^ 2 - p(t) * p''(t))`. -/
theorem derivative_sq_le_natDegree_mul_laguerreForm {p : ℝ[X]}
    (hp : p.Splits) (t : ℝ) :
    (derivative p).eval t ^ 2 ≤
      (p.natDegree : ℝ) * (laguerreForm p).eval t := by
  have h := (product_laguerre_bounds p.leadingCoeff p.roots t).1
  rw [← hp.eq_prod_roots] at h
  have hcard : ((p.roots.card : ℕ) : ℝ) = (p.natDegree : ℝ) := by
    exact_mod_cast (Splits.natDegree_eq_card_roots hp).symm
  simpa [hcard] using h

/-- **Polar Laguerre inequality.** If `p` splits and has degree at most `M`,
then `(M - 1) * p'(t) ^ 2 - M * p(t) * p''(t)` is nonnegative. -/
theorem polar_laguerreForm_nonneg {p : ℝ[X]} (hp : p.Splits) {M : ℕ}
    (hdeg : p.natDegree ≤ M) (t : ℝ) :
    0 ≤ ((M : ℝ) - 1) * (derivative p).eval t ^ 2 -
      (M : ℝ) * (p.eval t * (derivative (derivative p)).eval t) := by
  have hdegree := derivative_sq_le_natDegree_mul_laguerreForm hp t
  have hlaguerre := laguerreForm_eval_nonneg hp t
  have hM : (p.natDegree : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hdeg
  simp only [eval_laguerreForm] at hdegree hlaguerre
  nlinarith

/-- `W(p', polarTheta M p)` is the polar Laguerre form. -/
theorem wronskian_derivative_polarTheta (M : ℕ) (p : ℝ[X]) :
    wronskian (derivative p) (polarTheta M p) =
      C ((M : ℝ) - 1) * derivative p ^ 2 -
        C (M : ℝ) * (p * derivative (derivative p)) := by
  simp [wronskian, polarTheta, theta]
  ring

/-- Pointwise Wronskian form of the polar Laguerre inequality. -/
theorem wronskian_derivative_polarTheta_eval_nonneg {p : ℝ[X]}
    (hp : p.Splits) {M : ℕ} (hdeg : p.natDegree ≤ M) (t : ℝ) :
    0 ≤ (wronskian (derivative p) (polarTheta M p)).eval t := by
  rw [wronskian_derivative_polarTheta]
  simpa using polar_laguerreForm_nonneg hp hdeg t

/-- **Theta-Laguerre inequality.** A split polynomial whose roots are all
nonpositive has nonnegative `thetaLaguerreForm` on the whole real line. -/
theorem theta_laguerreForm_nonneg_of_roots_nonpos {p : ℝ[X]}
    (hp : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0) (t : ℝ) :
    0 ≤ (thetaLaguerreForm p).eval t := by
  have h := (product_laguerre_bounds p.leadingCoeff p.roots t).2 hroots
  rw [← hp.eq_prod_roots] at h
  simpa using h

/-- Nonnegative coefficients package the root-location hypothesis in the
theta-Laguerre inequality. -/
theorem theta_laguerreForm_nonneg_of_nonnegCoeffs {p : ℝ[X]}
    (hp : p.Splits) (hnn : HasNonnegCoeffs p) (t : ℝ) :
    0 ≤ (thetaLaguerreForm p).eval t :=
  theta_laguerreForm_nonneg_of_roots_nonpos hp
    (roots_nonpos_of_hasNonnegCoeffs hnn) t

/-- Zero-aware PF package of the theta-Laguerre inequality. -/
theorem theta_laguerreForm_nonneg_of_isPF {p : ℝ[X]}
    (hp : IsPFPolynomial p) (t : ℝ) :
    0 ≤ (thetaLaguerreForm p).eval t := by
  rcases hp.eq_zero_or_splits with rfl | hsplits
  · simp [thetaLaguerreForm, laguerreForm]
  · exact theta_laguerreForm_nonneg_of_roots_nonpos hsplits hp.roots_nonpos t

/-- The Wronskian against `thetaPlusOne` is the theta-Laguerre form. -/
theorem wronskian_thetaPlusOne_right_eq_thetaLaguerreForm (p : ℝ[X]) :
    wronskian p (thetaPlusOne p) = thetaLaguerreForm p := by
  rw [wronskian_thetaPlusOne_right]
  simp [thetaLaguerreForm, laguerreForm]
  ring

/-- The Wronskian with `polarTheta` on the left is independent of the polar
degree and is the same theta-Laguerre form. -/
theorem wronskian_polarTheta_left_eq_thetaLaguerreForm (M : ℕ) (p : ℝ[X]) :
    wronskian (polarTheta M p) p = thetaLaguerreForm p := by
  simp [wronskian, polarTheta, theta, thetaLaguerreForm, laguerreForm]
  ring

/-- The theta-Laguerre Wronskian is pointwise nonnegative for PF polynomials,
including the zero polynomial. -/
theorem wronskian_thetaPlusOne_right_eval_nonneg_of_isPF {p : ℝ[X]}
    (hp : IsPFPolynomial p) (t : ℝ) :
    0 ≤ (wronskian p (thetaPlusOne p)).eval t := by
  rw [wronskian_thetaPlusOne_right_eq_thetaLaguerreForm]
  exact theta_laguerreForm_nonneg_of_isPF hp t

/-- Equivalent polar-Wronskian packaging of the theta-Laguerre inequality. -/
theorem wronskian_polarTheta_left_eval_nonneg_of_isPF (M : ℕ) {p : ℝ[X]}
    (hp : IsPFPolynomial p) (t : ℝ) :
    0 ≤ (wronskian (polarTheta M p) p).eval t := by
  rw [wronskian_polarTheta_left_eq_thetaLaguerreForm]
  exact theta_laguerreForm_nonneg_of_isPF hp t

end RealRooted
