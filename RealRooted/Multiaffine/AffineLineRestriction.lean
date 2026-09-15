import RealRooted.AffineLineRestriction
import RealRooted.Mathlib.RingTheory.Polynomial.Wronskian
import RealRooted.Multiaffine.Rayleigh

/-!
# Rayleigh identities for affine-line restrictions

This file connects finite directional derivatives and univariate affine-line
restrictions to multiaffine Rayleigh differences.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- A multiaffine polynomial is its zero-specialization in one coordinate
plus that coordinate times its partial derivative. -/
theorem MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : P.IsMultiaffine) (i : σ) :
    P = MvPolynomial.specializeZero i P +
      MvPolynomial.X i * MvPolynomial.pderiv i P := by
  classical
  apply MvPolynomial.funext
  intro z
  rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_specializeZero]
  have h := hP.eval_update_eq_eval_pderiv_mul_add i z (z i)
  simp only [Function.update_eq_self] at h
  rw [h]
  ring

/-- Restricting a zero-specialization to an affine line is the same as first
zeroing that coordinate in the line. -/
theorem realAffineLineRestriction_specializeZero
    {σ : Type*} [DecidableEq σ]
    (a b : σ → ℝ) (P : MvPolynomial σ ℝ) (i : σ) :
    realAffineLineRestriction a b (MvPolynomial.specializeZero i P) =
      realAffineLineRestriction (Function.update a i 0)
        (Function.update b i 0) P := by
  classical
  apply Polynomial.funext
  intro t
  simp only [eval_realAffineLineRestriction,
    MvPolynomial.eval_specializeZero]
  have hassignment : Function.update (fun j => a j + b j * t) i 0 =
      fun j => Function.update a i 0 j + Function.update b i 0 j * t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hassignment]

/-- The partial derivative of a multiaffine polynomial has the same affine
restriction after zeroing the differentiated coordinate in the line. -/
theorem MvPolynomial.IsMultiaffine.realAffineLineRestriction_pderiv_update_zero
    {σ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsMultiaffine) (a b : σ → ℝ) (i : σ) :
    realAffineLineRestriction a b (MvPolynomial.pderiv i P) =
      realAffineLineRestriction (Function.update a i 0)
        (Function.update b i 0) (MvPolynomial.pderiv i P) := by
  classical
  apply Polynomial.funext
  intro t
  simp only [eval_realAffineLineRestriction]
  let z : σ → ℝ := fun j => a j + b j * t
  have hupdate := hP.eval_update_pderiv_eq i z 0
  rw [← hupdate]
  have hassignment : Function.update z i 0 =
      fun j => Function.update a i 0 j + Function.update b i 0 j * t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [z]
    · simp [z, hji]
  rw [hassignment]

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

/-- The Wronskian between a partial derivative and the original polynomial,
after affine-line restriction, is a weighted row sum of Rayleigh differences. -/
theorem wronskian_realAffineLineRestriction_pderiv
    {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (P : MvPolynomial σ ℝ) (i : σ) :
    Polynomial.wronskian
        (realAffineLineRestriction a b (MvPolynomial.pderiv i P))
        (realAffineLineRestriction a b P) =
      realAffineLineRestriction a b
        (∑ j, MvPolynomial.C (b j) *
          MvPolynomial.rayleighDifference P i j) := by
  rw [Polynomial.wronskian, derivative_realAffineLineRestriction,
    derivative_realAffineLineRestriction]
  unfold realAffineLineRestriction
  rw [← map_mul, ← map_mul, ← map_sub]
  congr 1
  rw [mul_comm (directionalPDeriv b (MvPolynomial.pderiv i P)) P,
    MvPolynomial.pderiv_mul_directionalPDeriv_sub]

/-- Rayleigh nonnegativity orients every affine-line Wronskian between a
coordinate derivative and the original polynomial. -/
theorem MvPolynomial.IsRayleigh.wronskian_eval_realAffineLineRestriction_pderiv_nonneg
    {σ : Type*} [Finite σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsRayleigh) (a b : σ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (i : σ) (t : ℝ) :
    0 ≤ (Polynomial.wronskian
      (realAffineLineRestriction a b (MvPolynomial.pderiv i P))
      (realAffineLineRestriction a b P)).eval t := by
  classical
  letI := Fintype.ofFinite σ
  rw [wronskian_realAffineLineRestriction_pderiv,
    eval_realAffineLineRestriction, map_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  exact mul_nonneg (hb j) (hP i j fun k => a k + b k * t)

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
