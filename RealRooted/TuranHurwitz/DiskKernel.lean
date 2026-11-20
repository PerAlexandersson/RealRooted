module

public import RealRooted.TuranHurwitz.TanhKernel
public import Mathlib.Analysis.Complex.Basic
import RealRooted.TuranHurwitz.BinomialComposition
import RealRooted.TuranHurwitz.CoefficientDerivation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The complex product kernel in the coefficient lemma

We keep the parameters `eta` fixed while differentiating the polynomial variable.
The kernel recurrence is an identity in `ℂ[z]⟦t⟧`.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Extension of scalars from real to complex polynomials as a real algebra map. -/
@[expose] noncomputable def complexPolynomialMap : ℝ[X] →ₐ[ℝ] ℂ[X] :=
  Polynomial.mapAlgHom (Algebra.ofId ℝ ℂ)

/-- The square of tanh with complex polynomial coefficients. -/
@[expose] noncomputable def complexTanhSquare : PowerSeries ℂ[X] :=
  tanhSquarePolynomialSeries.map complexPolynomialMap.toRingHom

/-- The complex tanh square has zero constant coefficient. -/
@[simp] theorem constantCoeff_complexTanhSquare :
    PowerSeries.constantCoeff complexTanhSquare = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, complexTanhSquare,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
  simp

local notation "Z" => (PowerSeries.C (X : ℂ[X]))
local notation "U" => complexTanhSquare

/-- The variable-dependent denominator power in the product kernel. -/
@[expose] noncomputable def tanhDenominator (a : ℝ) : PowerSeries ℂ[X] :=
  (PowerSeries.binomialSeries ℝ (-a)).subst (-Z * U)

/-- The numerator, with one fixed complex disk parameter added at each step. -/
@[expose] noncomputable def diskNumerator (d : ℝ) (eta : ℕ → ℂ) : ℕ → PowerSeries ℂ[X]
  | 0 => (PowerSeries.binomialSeries ℝ d).subst (-U)
  | ell + 1 => diskNumerator d eta ell * (1 - PowerSeries.C (C (eta ell)) * U)

/-- The full formal product kernel in Shi's coefficient lemma. -/
@[expose] noncomputable def diskKernel (d : ℝ) (eta : ℕ → ℂ) (ell : ℕ) :
    PowerSeries ℂ[X] :=
  diskNumerator d eta ell * tanhDenominator (d + ell)

/-- The recursive numerator equals the product in the paper's defining formula. -/
theorem diskNumerator_eq_prod (d : ℝ) (eta : ℕ → ℂ) (ell : ℕ) :
    diskNumerator d eta ell =
      (PowerSeries.binomialSeries ℝ d).subst (-U) *
        ∏ j ∈ Finset.range ell, (1 - PowerSeries.C (C (eta j)) * U) := by
  induction ell with
  | zero => simp [diskNumerator]
  | succ ell ih => rw [diskNumerator, ih, Finset.prod_range_succ, mul_assoc]

/-- The zero-parameter kernel is the scalar extension of the real base kernel. -/
theorem diskKernel_zero (d : ℝ) (eta : ℕ → ℂ) :
    diskKernel d eta 0 = (tanhKernel d).map complexPolynomialMap.toRingHom := by
  have hX : complexPolynomialMap.toRingHom (X : ℝ[X]) = (X : ℂ[X]) := by
    exact Polynomial.map_X _
  rw [tanhKernel, map_mul]
  rw [map_subst_algebraHom _ _ _
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp))]
  rw [map_subst_algebraHom _ _ _
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp))]
  simp only [diskKernel, diskNumerator, tanhDenominator, Nat.cast_zero, add_zero,
    map_neg, map_mul, PowerSeries.map_C, hX, complexTanhSquare]

/-- The coefficientwise polynomial derivative, regarded as a real derivation. -/
@[expose] noncomputable def complexParameterDerivation : Derivation ℝ ℂ[X] ℂ[X] :=
  (Polynomial.derivative' (R := ℂ)).restrictScalars ℝ

/-- Formal differentiation in the complex polynomial parameter. -/
@[expose] noncomputable def complexParameterDerivative (f : PowerSeries ℂ[X]) :
    PowerSeries ℂ[X] := PowerSeries.mapDerivation complexParameterDerivation f

/-- A coefficient of the parameter derivative is the derivative of the coefficient. -/
theorem coeff_complexParameterDerivative (f : PowerSeries ℂ[X]) (k : ℕ) :
    PowerSeries.coeff k (complexParameterDerivative f) = (PowerSeries.coeff k f).derivative := by
  rw [complexParameterDerivative, PowerSeries.coeff_mapDerivation]
  rfl

private theorem complexParameterDerivative_U : complexParameterDerivative U = 0 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_complexParameterDerivative]
  simp only [complexTanhSquare, tanhSquarePolynomialSeries, PowerSeries.coeff_map]
  change ((C (PowerSeries.coeff n (tanhSeries ^ 2))).map
    (algebraMap ℝ ℂ)).derivative = 0
  rw [Polynomial.map_C]
  exact derivative_C

private theorem complexParameterDerivative_argument :
    complexParameterDerivative (-Z * U) = -U := by
  have hneg := (coefficientDerivation complexParameterDerivation).map_neg (Z * U)
  change complexParameterDerivative (-(Z * U)) =
    -complexParameterDerivative (Z * U) at hneg
  rw [show -Z * U = -(Z * U) by ring, hneg]
  simp only [complexParameterDerivative, PowerSeries.mapDerivation_mul,
    PowerSeries.mapDerivation_C, complexParameterDerivation, Derivation.restrictScalars_apply,
    Polynomial.derivative'_apply, derivative_X, map_one]
  change -(1 * U + Z * complexParameterDerivative U) = -U
  rw [complexParameterDerivative_U]
  ring

/-- Differentiation of the variable-dependent denominator power raises its exponent. -/
theorem complexParameterDerivative_tanhDenominator (a : ℝ) :
    complexParameterDerivative (tanhDenominator a) =
      PowerSeries.C (C (a : ℂ)) * U * tanhDenominator (a + 1) := by
  have hzero : PowerSeries.constantCoeff (-Z * U) = 0 := by simp
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hzero
  rw [tanhDenominator, complexParameterDerivative, mapDerivation_subst _ _ _ hzero,
    derivative_binomialSeries, PowerSeries.subst_mul hsubst, subst_C_algebra _ _ hsubst]
  rw [show -a - 1 = -(a + 1) by ring]
  change PowerSeries.C (C ((-a : ℝ) : ℂ)) * tanhDenominator (a + 1) *
    complexParameterDerivative (-Z * U) = _
  rw [complexParameterDerivative_argument]
  simp only [map_neg, Complex.ofReal_neg]
  ring

/-- The denominator powers satisfy the formal base-shift identity. -/
theorem tanhDenominator_shift (a : ℝ) :
    (1 - Z * U) * tanhDenominator (a + 1) = tanhDenominator a := by
  have h := binomial_subst_shift (-a) (-Z * U) (by simp)
  simpa only [tanhDenominator, show -a - 1 = -(a + 1) by ring,
    neg_mul, sub_eq_add_neg] using h

private theorem complexParameterDerivative_diskNumerator (d : ℝ) (eta : ℕ → ℂ)
    (ell : ℕ) : complexParameterDerivative (diskNumerator d eta ell) = 0 := by
  induction ell with
  | zero =>
      rw [diskNumerator, complexParameterDerivative,
        mapDerivation_subst _ _ _ (by simp)]
      change _ * complexParameterDerivative (-U) = 0
      have hneg := (coefficientDerivation complexParameterDerivation).map_neg U
      change complexParameterDerivative (-U) = -complexParameterDerivative U at hneg
      rw [hneg, complexParameterDerivative_U, neg_zero, mul_zero]
  | succ ell ih =>
      have hmul := PowerSeries.mapDerivation_mul complexParameterDerivation
        (diskNumerator d eta ell) (1 - PowerSeries.C (C (eta ell)) * U)
      change complexParameterDerivative (diskNumerator d eta (ell + 1)) = 0
      rw [diskNumerator]
      change PowerSeries.mapDerivation complexParameterDerivation _ = _
      rw [hmul]
      change complexParameterDerivative (diskNumerator d eta ell) * _ +
        diskNumerator d eta ell * complexParameterDerivative
          (1 - PowerSeries.C (C (eta ell)) * U) = 0
      rw [ih]
      have hsub := (coefficientDerivation complexParameterDerivation).map_sub
        1 (PowerSeries.C (C (eta ell)) * U)
      change complexParameterDerivative (1 - PowerSeries.C (C (eta ell)) * U) =
        complexParameterDerivative 1 -
          complexParameterDerivative (PowerSeries.C (C (eta ell)) * U) at hsub
      rw [hsub]
      simp only [complexParameterDerivative, PowerSeries.mapDerivation_one,
        PowerSeries.mapDerivation_mul, PowerSeries.mapDerivation_C,
        complexParameterDerivation, Derivation.restrictScalars_apply,
        Polynomial.derivative'_apply, derivative_C, map_zero]
      change 0 * _ + diskNumerator d eta ell * (0 - (0 * U + _ *
        complexParameterDerivative U)) = 0
      rw [complexParameterDerivative_U]
      ring

/-- The numerator factors are constant with respect to the polynomial parameter. -/
theorem complexParameterDerivative_diskKernel (d : ℝ) (eta : ℕ → ℂ) (ell : ℕ) :
    complexParameterDerivative (diskKernel d eta ell) =
      PowerSeries.C (C ((d + ell : ℝ) : ℂ)) * U *
        diskNumerator d eta ell * tanhDenominator (d + ell + 1) := by
  rw [diskKernel, complexParameterDerivative, PowerSeries.mapDerivation_mul]
  change complexParameterDerivative (diskNumerator d eta ell) * _ +
    diskNumerator d eta ell * complexParameterDerivative (tanhDenominator (d + ell)) = _
  rw [complexParameterDerivative_diskNumerator, complexParameterDerivative_tanhDenominator]
  ring

/-- The formal product kernel satisfies the positive-weight differential step. -/
theorem diskKernel_succ_mul (d : ℝ) (eta : ℕ → ℂ) (ell : ℕ) :
    PowerSeries.C (C ((d + ell : ℝ) : ℂ)) * diskKernel d eta (ell + 1) =
      PowerSeries.C (C ((d + ell : ℝ) : ℂ)) * diskKernel d eta ell +
        (Z - PowerSeries.C (C (eta ell))) *
          complexParameterDerivative (diskKernel d eta ell) := by
  rw [complexParameterDerivative_diskKernel, diskKernel, diskNumerator,
    show d + ((ell + 1 : ℕ) : ℝ) = d + ell + 1 by push_cast; ring]
  have hshift := tanhDenominator_shift (d + ell)
  rw [diskKernel]
  linear_combination (PowerSeries.C (C ((d + ell : ℝ) : ℂ)) *
    diskNumerator d eta ell) * hshift

end RealRooted.TuranHurwitz
