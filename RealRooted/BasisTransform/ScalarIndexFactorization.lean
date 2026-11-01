module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import RealRooted.NarayanaTransformation.Basis

/-!
# Scalar-index recurrence factorization

For a linear endomorphism `L` and a seed `g`, this module packages the linear
map sending `X ^ n` to `L ^ n g`.  It identifies the recurrence obtained by
successively applying `L + n h I` with the image of the generalized rising
factorial of step `h` under this orbit map.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The linear map from polynomials to the orbit of `g` under `L`, determined
by `X ^ n ↦ L ^ n g`. -/
def polynomialOrbitMap (L : Module.End ℝ V) (g : V) : ℝ[X] →ₗ[ℝ] V :=
  Polynomial.lsum fun n ↦
    LinearMap.toSpanSingleton ℝ V ((L ^ n) g)

/-- The orbit map sends a scalar monomial to the corresponding scalar
multiple of the orbit. -/
@[simp] theorem polynomialOrbitMap_monomial
    (L : Module.End ℝ V) (g : V) (n : ℕ) (a : ℝ) :
    polynomialOrbitMap L g (Polynomial.monomial n a) =
      a • (L ^ n) g := by
  simp [polynomialOrbitMap, Polynomial.lsum_apply]

/-- The orbit map has its prescribed value on every monomial basis vector. -/
@[simp] theorem polynomialOrbitMap_X_pow
    (L : Module.End ℝ V) (g : V) (n : ℕ) :
    polynomialOrbitMap L g (X ^ n) = (L ^ n) g := by
  rw [Polynomial.X_pow_eq_monomial, polynomialOrbitMap_monomial]
  simp

/-- The orbit map is evaluation of the input polynomial at the endomorphism, applied to `g`. -/
theorem polynomialOrbitMap_apply (L : Module.End ℝ V) (g : V) (p : ℝ[X]) :
    polynomialOrbitMap L g p = aeval L p g := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [LinearMap.map_add, hp, hq, map_add, LinearMap.add_apply]
  | monomial n b =>
      simp [polynomialOrbitMap_monomial, aeval_monomial, Module.algebraMap_end_apply]

/-- Multiplication by an affine factor before the orbit map applies the
corresponding affine expression in the endomorphism afterwards. -/
theorem polynomialOrbitMap_mul_X_add_C
    (L : Module.End ℝ V) (g : V) (p : ℝ[X]) (a : ℝ) :
    polynomialOrbitMap L g (p * (X + C a)) =
      (L + a • (1 : Module.End ℝ V)) (polynomialOrbitMap L g p) := by
  rw [polynomialOrbitMap_apply, polynomialOrbitMap_apply, mul_comm, map_mul,
    Module.End.mul_apply]
  simp [Algebra.algebraMap_eq_smul_one]

/-- For polynomial-valued orbits, `polynomialOrbitMap` is the existing basis
transform whose `n`th basis element is `L ^ n g`. -/
theorem polynomialOrbitMap_eq_basisTransformₗ
    (L : Module.End ℝ ℝ[X]) (g : ℝ[X]) :
    polynomialOrbitMap L g =
      Polynomial.basisTransformₗ (fun n ↦ (L ^ n) g) := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, polynomialOrbitMap_monomial,
    Polynomial.basisTransformₗ_apply,
    Polynomial.basisTransform_monomial, Polynomial.smul_eq_C_mul]

/-- A row initialized by `g` and updated by `L + n h I` is the orbit-map
image of the generalized rising factorial of step `h`. -/
theorem scalarIndexRow_eq_polynomialOrbitMap
    (L : Module.End ℝ V) (g : V) (h : ℝ) (P : ℕ → V)
    (hzero : P 0 = g)
    (hsucc : ∀ n, P (n + 1) =
      (L + ((n : ℝ) * h) • (1 : Module.End ℝ V)) (P n)) (n : ℕ) :
    P n = polynomialOrbitMap L g (risingFactorialPolynomial h n) := by
  induction n with
  | zero =>
      rw [hzero]
      simpa [risingFactorialPolynomial] using
        (polynomialOrbitMap_X_pow L g 0).symm
  | succ n ih =>
      rw [hsucc, ih, risingFactorialPolynomial_succ_mul]
      exact (polynomialOrbitMap_mul_X_add_C
        L g (risingFactorialPolynomial h n) ((n : ℝ) * h)).symm

end RealRooted
