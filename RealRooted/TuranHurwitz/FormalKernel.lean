module

public import RealRooted.TuranHurwitz.FormalHyperbolic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import RealRooted.Mathlib.RingTheory.PowerSeries.MapDerivation
public import Mathlib.Algebra.Polynomial.Derivation
import RealRooted.TuranHurwitz.FormalBinomial
import RealRooted.TuranHurwitz.CoefficientDerivation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The formal hyperbolic kernel

We work in `ℝ[z]⟦t⟧`. The variable in the polynomial coefficients is `z`,
whereas the power-series variable is `t`. Both partial derivatives are formal.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

local notation "Z" => (PowerSeries.C (X : ℝ[X]))

/-- The square of formal sinh, lifted to constant polynomial coefficients. -/
@[expose] noncomputable def sinhSquarePolynomialSeries : PowerSeries ℝ[X] :=
  (sinhSeries ^ 2).map Polynomial.C

/-- The zero-constant series `-z sinh(t)²` used in binomial substitution. -/
@[expose] noncomputable def kernelArgument : PowerSeries ℝ[X] :=
  -Z * sinhSquarePolynomialSeries

/-- The formal kernel `(1-z sinh(t)²)^(-d)` for an arbitrary real exponent. -/
@[expose] noncomputable def hyperbolicKernel (d : ℝ) : PowerSeries ℝ[X] :=
  (PowerSeries.binomialSeries ℝ (-d)).subst kernelArgument

/-- Formal differentiation with respect to the polynomial parameter `z`. -/
@[expose] noncomputable def parameterDerivative (f : PowerSeries ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ)) f

/-- The kernel substitution has zero constant coefficient. -/
@[simp] theorem constantCoeff_kernelArgument : PowerSeries.constantCoeff kernelArgument = 0 := by
  have hs : PowerSeries.constantCoeff sinhSquarePolynomialSeries = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, sinhSquarePolynomialSeries,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  simp only [kernelArgument, map_mul, hs, mul_zero]

/-- The binomial substitution is formally admissible. -/
theorem hasSubst_kernelArgument : PowerSeries.HasSubst kernelArgument :=
  PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_kernelArgument

/-- The formal kernel has constant coefficient one. -/
@[simp] theorem constantCoeff_hyperbolicKernel (d : ℝ) :
    PowerSeries.constantCoeff (hyperbolicKernel d) = 1 := by
  rw [hyperbolicKernel, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero
    constantCoeff_kernelArgument]
  simp

private theorem parameterDerivative_sinhSquare :
    parameterDerivative sinhSquarePolynomialSeries = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [parameterDerivative, PowerSeries.coeff_mapDerivation,
    sinhSquarePolynomialSeries, PowerSeries.coeff_map, Polynomial.derivative'_apply,
    derivative_C, map_zero]

private theorem parameterDerivative_argument :
    parameterDerivative kernelArgument = -sinhSquarePolynomialSeries := by
  have hneg (f : PowerSeries ℝ[X]) : parameterDerivative (-f) = -parameterDerivative f := by
    exact (coefficientDerivation (Polynomial.derivative' (R := ℝ))).map_neg f
  rw [kernelArgument, show -Z * sinhSquarePolynomialSeries =
    -(Z * sinhSquarePolynomialSeries) by ring, hneg]
  simp only [parameterDerivative, PowerSeries.mapDerivation_mul, PowerSeries.mapDerivation_C,
    Polynomial.derivative'_apply, Polynomial.derivative_X, map_one]
  change -(1 * sinhSquarePolynomialSeries + Z * parameterDerivative sinhSquarePolynomialSeries) = _
  rw [parameterDerivative_sinhSquare]
  ring

/-- Differentiating the formal kernel in its parameter raises the exponent by one. -/
theorem parameterDerivative_hyperbolicKernel (d : ℝ) :
    parameterDerivative (hyperbolicKernel d) =
      PowerSeries.C (C d) * sinhSquarePolynomialSeries * hyperbolicKernel (d + 1) := by
  rw [hyperbolicKernel, parameterDerivative,
    mapDerivation_subst _ _ _ constantCoeff_kernelArgument, derivative_binomialSeries]
  rw [PowerSeries.subst_mul hasSubst_kernelArgument,
    subst_C_algebra _ _ hasSubst_kernelArgument]
  have hexp : -d - 1 = -(d + 1) := by ring
  rw [hexp]
  change PowerSeries.C (C (-d)) * hyperbolicKernel (d + 1) *
    parameterDerivative kernelArgument = _
  rw [parameterDerivative_argument]
  simp only [map_neg]
  ring

/-- Multiplication by the kernel base lowers the negative exponent by one. -/
theorem hyperbolicKernel_shift (d : ℝ) :
    (1 - Z * sinhSquarePolynomialSeries) * hyperbolicKernel (d + 1) =
      hyperbolicKernel d := by
  have h := congrArg (fun f : PowerSeries ℝ => f.subst kernelArgument)
    (one_add_X_mul_binomialSeries_pred (-d))
  have hone : (1 : PowerSeries ℝ).subst kernelArgument = (1 : PowerSeries ℝ[X]) := by
    simpa using subst_C_algebra (1 : ℝ) kernelArgument hasSubst_kernelArgument
  rw [PowerSeries.subst_mul hasSubst_kernelArgument,
    PowerSeries.subst_add hasSubst_kernelArgument, PowerSeries.subst_X hasSubst_kernelArgument,
    hone, show -d - 1 = -(d + 1) by ring] at h
  change (1 + kernelArgument) * hyperbolicKernel (d + 1) = hyperbolicKernel d at h
  simpa only [kernelArgument, neg_mul, sub_eq_add_neg] using h

private theorem parameterDerivative_scalar (r : ℝ) :
    parameterDerivative (PowerSeries.C (C r)) = 0 := by
  simp [parameterDerivative]

/-- The second formal parameter derivative of the kernel. -/
theorem parameterDerivative_parameterDerivative_hyperbolicKernel (d : ℝ) :
    parameterDerivative (parameterDerivative (hyperbolicKernel d)) =
      PowerSeries.C (C (d * (d + 1))) * sinhSquarePolynomialSeries ^ 2 *
        hyperbolicKernel (d + 2) := by
  have hmul (f g : PowerSeries ℝ[X]) : parameterDerivative (f * g) =
      parameterDerivative f * g + f * parameterDerivative g :=
    PowerSeries.mapDerivation_mul _ f g
  rw [parameterDerivative_hyperbolicKernel, hmul, hmul, parameterDerivative_scalar,
    parameterDerivative_sinhSquare, parameterDerivative_hyperbolicKernel]
  rw [show d + 1 + 1 = d + 2 by ring]
  simp only [map_mul, zero_mul, mul_zero, zero_add, add_zero]
  ring

private theorem derivative_kernelArgument : PowerSeries.derivative kernelArgument =
    -Z * PowerSeries.derivative sinhSquarePolynomialSeries := by
  simp only [kernelArgument, PowerSeries.derivative.leibniz, map_neg,
    PowerSeries.derivative_C, neg_zero, smul_eq_mul, mul_zero, add_zero]

/-- The first formal derivative in `t` of the kernel. -/
theorem derivative_hyperbolicKernel (d : ℝ) :
    PowerSeries.derivative (hyperbolicKernel d) =
      PowerSeries.C (C d) * Z * PowerSeries.derivative sinhSquarePolynomialSeries *
        hyperbolicKernel (d + 1) := by
  rw [hyperbolicKernel, derivative_subst_algebra _ _ hasSubst_kernelArgument,
    derivative_binomialSeries, PowerSeries.subst_mul hasSubst_kernelArgument,
    subst_C_algebra _ _ hasSubst_kernelArgument]
  rw [show -d - 1 = -(d + 1) by ring]
  change PowerSeries.C (C (-d)) * hyperbolicKernel (d + 1) *
    PowerSeries.derivative kernelArgument = _
  rw [derivative_kernelArgument]
  simp only [map_neg]
  ring

private theorem derivative_sinhSquarePolynomialSeries_sq :
    PowerSeries.derivative sinhSquarePolynomialSeries ^ 2 =
      4 * sinhSquarePolynomialSeries * (1 + sinhSquarePolynomialSeries) := by
  have h := congrArg (PowerSeries.map Polynomial.C) derivative_sinhSeries_sq_sq
  rw [sinhSquarePolynomialSeries, derivative_map]
  simpa only [map_pow, map_mul, map_add,
    map_one, map_ofNat] using h

private theorem derivative_derivative_sinhSquarePolynomialSeries :
    PowerSeries.derivative (PowerSeries.derivative sinhSquarePolynomialSeries) =
      2 + 4 * sinhSquarePolynomialSeries := by
  rw [sinhSquarePolynomialSeries, derivative_map, derivative_map,
    derivative_derivative_sinhSeries_sq]
  simp only [map_add, map_mul, map_ofNat]

/-- The second formal derivative in `t` of the kernel, before eliminating `sinh²`. -/
theorem derivative_derivative_hyperbolicKernel (d : ℝ) :
    PowerSeries.derivative (PowerSeries.derivative (hyperbolicKernel d)) =
      PowerSeries.C (C d) * Z *
        PowerSeries.derivative (PowerSeries.derivative sinhSquarePolynomialSeries) *
          hyperbolicKernel (d + 1) +
      PowerSeries.C (C (d * (d + 1))) * Z ^ 2 *
        PowerSeries.derivative sinhSquarePolynomialSeries ^ 2 * hyperbolicKernel (d + 2) := by
  let : Algebra ℝ[X] (PowerSeries ℝ[X]) := MvPowerSeries.instAlgebra
  rw [derivative_hyperbolicKernel, PowerSeries.derivative.leibniz,
    PowerSeries.derivative.leibniz, PowerSeries.derivative.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_C, derivative_hyperbolicKernel]
  rw [show d + 1 + 1 = d + 2 by ring]
  simp only [smul_eq_mul, map_mul, mul_zero, add_zero]
  ring

/-- EPDE holds in `ℝ[z]⟦t⟧`, with both derivatives interpreted formally. -/
theorem hyperbolicKernel_pde (d : ℝ) :
    PowerSeries.derivative (PowerSeries.derivative (hyperbolicKernel d)) =
      4 * Z ^ 2 * (1 + Z) *
        parameterDerivative (parameterDerivative (hyperbolicKernel d)) +
      Z * (4 + PowerSeries.C (C (4 * d + 6)) * Z) *
        parameterDerivative (hyperbolicKernel d) +
      PowerSeries.C (C (2 * d)) * Z * hyperbolicKernel d := by
  rw [derivative_derivative_hyperbolicKernel,
    derivative_derivative_sinhSquarePolynomialSeries,
    derivative_sinhSquarePolynomialSeries_sq,
    parameterDerivative_parameterDerivative_hyperbolicKernel,
    parameterDerivative_hyperbolicKernel]
  simp only [map_mul, map_add, map_one, map_ofNat]
  have h₀ := hyperbolicKernel_shift d
  have h₁ := hyperbolicKernel_shift (d + 1)
  rw [show d + 1 + 1 = d + 2 by ring] at h₁
  linear_combination (2 * PowerSeries.C (C d) * Z) * h₀ +
    (4 * PowerSeries.C (C d) * (PowerSeries.C (C d) + 1) * Z ^ 2 *
      sinhSquarePolynomialSeries) * h₁

end RealRooted.TuranHurwitz
