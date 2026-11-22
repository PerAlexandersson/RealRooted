module

public import RealRooted.Hermite.Homogeneous
public import RealRooted.MultiplierSequence
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Hermite.GeneratingFunction
import RealRooted.Mathlib.Algebra.Polynomial.Chow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Hermite versions of Jensen polynomials

The physicists' Hermite polynomials have generating function `exp (2 X z - z²)`.
Their binomial convolution with the Taylor data of `f` is a reversed Jensen
polynomial of `f(z) exp(-z²)`, evaluated at `2 X`.
-/

@[expose] public section

open Polynomial Complex

namespace RealRooted

/-- The physicists' Hermite normalization, `H₀ = 1` and `H₁ = 2 X`. -/
noncomputable def hermitePhysicists (d : ℕ) : ℝ[X] :=
  hermiteHomogeneous (2 * X) (-1) d

/-- A Hermite polynomial with binomially weighted Taylor coefficients. -/
noncomputable def hermiteJensenPolynomial (d : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C ((d.choose k : ℝ) * gamma k) * hermitePhysicists (d - k)

@[simp] theorem hermitePhysicists_zero : hermitePhysicists 0 = 1 := rfl

@[simp] theorem hermitePhysicists_one : hermitePhysicists 1 = 2 * X := rfl

/-- The classical three-term recurrence in the physicists' normalization. -/
theorem hermitePhysicists_add_two (d : ℕ) :
    hermitePhysicists (d + 2) = 2 * X * hermitePhysicists (d + 1) -
      C (2 * (d + 1 : ℝ)) * hermitePhysicists d := by
  simp only [hermitePhysicists, hermiteHomogeneous_add_two, map_mul, map_ofNat,
    map_add, map_natCast, map_one]
  push_cast
  ring

private theorem eval₂_hermitePhysicists (d : ℕ) (x : ℂ) :
    (hermitePhysicists d).eval₂ ofRealHom x = hermiteHomogeneous (2 * x) (-1) d := by
  change (eval₂RingHom ofRealHom x) (hermiteHomogeneous (2 * X) (-1) d) = _
  rw [map_hermiteHomogeneous, map_mul, map_ofNat]
  simp

private theorem eval₂_reflect_jensenPolynomial (d : ℕ) (gamma : ℕ → ℝ) (x : ℂ) :
    (reflect d (jensenPolynomial d gamma)).eval₂ ofRealHom x =
      ∑ k ∈ Finset.range (d + 1), (d.choose k : ℂ) * (gamma k : ℂ) * x ^ (d - k) := by
  simp only [jensenPolynomial, ← C_mul_X_pow_eq_monomial, reflect_finset_sum_C_mul,
    reflect_monomial, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    ofRealHom_eq_coe, ofReal_mul, ofReal_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [revAt_le (by simpa using hk)]

private theorem eval₂_reflect_jensenPolynomial_eq_iteratedDeriv
    {f : ℂ → ℂ} {gamma : ℕ → ℝ} (hf : Differentiable ℂ f)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ)) (d : ℕ) (x : ℂ) :
    (reflect d (jensenPolynomial d gamma)).eval₂ ofRealHom x =
      iteratedDeriv d (fun z => f z * exp (x * z)) 0 := by
  rw [eval₂_reflect_jensenPolynomial, iteratedDeriv_fun_mul
    (hf.contDiff.contDiffAt) (by fun_prop)]
  simp only [hgamma, iteratedDeriv_cexp_const_mul, mul_zero, exp_zero, mul_one]

/-- The Hermite convolution is a reversed Jensen polynomial of the product
with a Gaussian. This identity fixes both the coefficient and Hermite normalizations. -/
theorem hermiteJensenPolynomial_eq_reflect_jensenPolynomial
    {f : ℂ → ℂ} {gamma beta : ℕ → ℝ} (hf : Differentiable ℂ f)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ))
    (hbeta : ∀ k, iteratedDeriv k (fun z => f z * exp (-z ^ 2)) 0 = (beta k : ℂ))
    (d : ℕ) :
    hermiteJensenPolynomial d gamma =
      (reflect d (jensenPolynomial d beta)).comp (C 2 * X) := by
  apply Polynomial.funext
  intro x
  apply ofReal_injective
  have heval (p : ℝ[X]) : ((p.eval x : ℝ) : ℂ) = p.eval₂ ofRealHom (x : ℂ) := by
    exact (eval₂_at_apply ofRealHom x).symm
  rw [heval, heval, eval₂_comp]
  simp only [eval₂_mul, eval₂_C, eval₂_X, ofRealHom_eq_coe, ofReal_ofNat]
  rw [eval₂_reflect_jensenPolynomial_eq_iteratedDeriv
    (hf.mul (by fun_prop)) hbeta]
  simp only [Pi.mul_def]
  have heq : (fun z => (f z * exp (-z ^ 2)) * exp (2 * (x : ℂ) * z)) =
      fun z => f z * exp (2 * (x : ℂ) * z + (-1) * z ^ 2) := by
    funext z
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  rw [heq, iteratedDeriv_fun_mul (hf.contDiff.contDiffAt) (by fun_prop)]
  simp only [hermiteJensenPolynomial, eval₂_finsetSum, eval₂_mul, eval₂_C,
    ofRealHom_eq_coe, ofReal_mul, ofReal_natCast, eval₂_hermitePhysicists,
    hgamma, iteratedDeriv_exp_quadratic_zero]

end RealRooted
