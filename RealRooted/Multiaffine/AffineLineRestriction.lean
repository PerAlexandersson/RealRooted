import RealRooted.AffineLineRestriction
import RealRooted.Multiaffine.Rayleigh

/-!
# Rayleigh identities for affine-line restrictions

This file connects finite directional derivatives and univariate affine-line
restrictions to multiaffine Rayleigh differences.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The derivative of an affine-line restriction is the restriction of the
directional derivative. -/
theorem derivative_realAffineLineRestriction
    {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    (realAffineLineRestriction a b P).derivative =
      realAffineLineRestriction a b (directionalPDeriv b P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [realAffineLineRestriction, directionalPDeriv]
  | add P Q hP hQ =>
      unfold realAffineLineRestriction at hP hQ ⊢
      unfold directionalPDeriv at hP hQ ⊢
      rw [map_add, Polynomial.derivative_add, hP, hQ, map_sum]
      simp only [map_add, map_mul, map_sum, mul_add,
        Finset.sum_add_distrib]
  | mul_X P j hP =>
      unfold realAffineLineRestriction at hP ⊢
      unfold directionalPDeriv at hP ⊢
      rw [map_mul, Polynomial.derivative_mul, hP, map_sum]
      simp only [map_mul, map_add, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X, Pi.single_apply, mul_add,
        Finset.sum_add_distrib]
      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', Polynomial.derivative_add,
        Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_X, zero_mul, zero_add]
      congr 1
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      · rw [Finset.sum_eq_single j]
        · simp only [map_one, mul_one, if_pos]
          rw [mul_comm]
        · intro i hi hij
          simp [Ne.symm hij]
        · simp

/-- The Laguerre form of a finite directional derivative is the weighted sum
of all Rayleigh differences. -/
theorem directionalPDeriv_sq_sub_directionalPDeriv
    {R σ : Type*} [CommRing R] [Fintype σ]
    (b : σ → R) (P : MvPolynomial σ R) :
    directionalPDeriv b P ^ 2 -
        P * directionalPDeriv b (directionalPDeriv b P) =
      ∑ i, ∑ j,
        MvPolynomial.C (b i * b j) *
          MvPolynomial.rayleighDifference P i j := by
  classical
  simp only [directionalPDeriv, MvPolynomial.rayleighDifference,
    map_sum, MvPolynomial.pderiv_C_mul, pow_two, Finset.sum_mul,
    Finset.mul_sum, map_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The univariate Laguerre form of an affine-line restriction is the
restriction of the weighted Rayleigh sum. -/
theorem derivative_sq_sub_realAffineLineRestriction
    {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    (realAffineLineRestriction a b P).derivative ^ 2 -
        realAffineLineRestriction a b P *
          (realAffineLineRestriction a b P).derivative.derivative =
      realAffineLineRestriction a b
        (∑ i, ∑ j,
          MvPolynomial.C (b i * b j) *
            MvPolynomial.rayleighDifference P i j) := by
  rw [derivative_realAffineLineRestriction,
    derivative_realAffineLineRestriction]
  unfold realAffineLineRestriction
  rw [← map_pow, ← map_mul, ← map_sub,
    directionalPDeriv_sq_sub_directionalPDeriv]

/-- Pointwise form of the weighted Rayleigh identity for an affine-line
restriction. -/
theorem eval_derivative_sq_sub_realAffineLineRestriction
    {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (P : MvPolynomial σ ℝ) (t : ℝ) :
    (realAffineLineRestriction a b P).derivative.eval t ^ 2 -
        (realAffineLineRestriction a b P).eval t *
          (realAffineLineRestriction a b P).derivative.derivative.eval t =
      ∑ i, ∑ j, (b i * b j) *
        MvPolynomial.eval (fun k => a k + b k * t)
          (MvPolynomial.rayleighDifference P i j) := by
  have h := congrArg (Polynomial.eval t)
    (derivative_sq_sub_realAffineLineRestriction a b P)
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, eval_realAffineLineRestriction,
    map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C] using h

/-- Every nonnegative-direction affine restriction of a Rayleigh polynomial
satisfies Laguerre's differential inequality. -/
theorem MvPolynomial.IsRayleigh.laguerre_realAffineLineRestriction
    {σ : Type*} [Finite σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsRayleigh) (a b : σ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (t : ℝ) :
    0 ≤ (realAffineLineRestriction a b P).derivative.eval t ^ 2 -
      (realAffineLineRestriction a b P).eval t *
        (realAffineLineRestriction a b P).derivative.derivative.eval t := by
  classical
  letI := Fintype.ofFinite σ
  rw [eval_derivative_sq_sub_realAffineLineRestriction]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hb i) (hb j))
    (hP i j fun k => a k + b k * t)

end

end RealRooted
