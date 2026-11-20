module

public import RealRooted.TuranHurwitz.FormalKernel
public import RealRooted.TuranHurwitz.BinomialComposition
import RealRooted.TuranHurwitz.CoefficientDerivation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Formal change of variables from the sinh kernel to the tanh kernel

The base identity uses multiplicativity of normalized binomial powers.
All equalities hold coefficientwise, with no analytic convergence hypotheses.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

local notation "Z" => (PowerSeries.C (X : ℝ[X]))

/-- The square of formal tanh, lifted to polynomial coefficients. -/
@[expose] noncomputable def tanhSquarePolynomialSeries : PowerSeries ℝ[X] :=
  (tanhSeries ^ 2).map Polynomial.C

/-- The lifted square of tanh has zero constant coefficient. -/
@[simp] theorem constantCoeff_tanhSquarePolynomialSeries :
    PowerSeries.constantCoeff tanhSquarePolynomialSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, tanhSquarePolynomialSeries,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- The lifted square of sinh has zero constant coefficient. -/
@[simp] theorem constantCoeff_sinhSquarePolynomialSeries :
    PowerSeries.constantCoeff sinhSquarePolynomialSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, sinhSquarePolynomialSeries,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- The algebraic relation between the squares of tanh and sinh. -/
theorem tanhSeries_sq_mul_one_add_sinhSeries_sq :
    tanhSeries ^ 2 * (1 + sinhSeries ^ 2) = sinhSeries ^ 2 := by
  have hc : 1 + sinhSeries ^ 2 = coshSeries ^ 2 := by
    linear_combination -coshSeries_sq_sub_sinhSeries_sq
  have hi := PowerSeries.mul_inv_cancel coshSeries (by simp)
  rw [hc, tanhSeries]
  calc
    _ = sinhSeries ^ 2 * (coshSeries * coshSeries⁻¹) ^ 2 := by ring
    _ = _ := by rw [hi]; ring

/-- The tanh-to-sinh relation remains valid after lifting coefficients. -/
theorem tanhSquare_mul_one_add_sinhSquare :
    tanhSquarePolynomialSeries * (1 + sinhSquarePolynomialSeries) =
      sinhSquarePolynomialSeries := by
  have h := congrArg (PowerSeries.map Polynomial.C)
    tanhSeries_sq_mul_one_add_sinhSeries_sq
  simpa only [tanhSquarePolynomialSeries, sinhSquarePolynomialSeries,
    map_mul, map_add, map_one] using h

/-- The formal base kernel appearing in the coefficient lemma at `ell = 0`. -/
@[expose] noncomputable def tanhKernel (d : ℝ) : PowerSeries ℝ[X] :=
  (PowerSeries.binomialSeries ℝ d).subst (-tanhSquarePolynomialSeries) *
    (PowerSeries.binomialSeries ℝ (-d)).subst (-Z * tanhSquarePolynomialSeries)

/-- Changing the binomial base identifies the tanh kernel with a shifted sinh kernel. -/
theorem tanhKernel_eq_shifted_sinhKernel (d : ℝ) :
    tanhKernel d = (PowerSeries.binomialSeries ℝ (-d)).subst
      (-(Z - 1) * sinhSquarePolynomialSeries) := by
  let T := tanhSquarePolynomialSeries
  let W := sinhSquarePolynomialSeries
  have hT : PowerSeries.constantCoeff (-T) = 0 := by simp [T]
  have hW : PowerSeries.constantCoeff (-(Z - 1) * W) = 0 := by simp [W]
  have hbase : -T + (-(Z - 1) * W) + (-T) * (-(Z - 1) * W) = -Z * T := by
    have h := tanhSquare_mul_one_add_sinhSquare
    change T * (1 + W) = W at h
    linear_combination (Z - 1) * h
  have hm := binomial_subst_mul (-d) (-T) (-(Z - 1) * W) hT hW
  rw [hbase] at hm
  have hc := binomial_subst_mul_neg d (-T) hT
  change (PowerSeries.binomialSeries ℝ d).subst (-T) *
    (PowerSeries.binomialSeries ℝ (-d)).subst (-Z * T) = _
  rw [← hm, ← mul_assoc, hc, one_mul]

/-- Coefficientwise composition by `X - 1` realizes the sinh-to-tanh change of variables. -/
theorem tanhKernel_eq_map_hyperbolicKernel (d : ℝ) :
    tanhKernel d = (hyperbolicKernel d).map
      (Polynomial.aeval (X - 1 : ℝ[X])).toRingHom := by
  rw [tanhKernel_eq_shifted_sinhKernel, hyperbolicKernel,
    show PowerSeries.map (Polynomial.aeval (X - 1 : ℝ[X])).toRingHom
      ((PowerSeries.binomialSeries ℝ (-d)).subst kernelArgument) =
      (PowerSeries.binomialSeries ℝ (-d)).subst
        (kernelArgument.map (Polynomial.aeval (X - 1 : ℝ[X])).toRingHom) from
      map_subst_algebraHom _ _ _ hasSubst_kernelArgument]
  congr 1
  rw [kernelArgument, map_mul, map_neg, PowerSeries.map_C]
  have hW : sinhSquarePolynomialSeries.map
      (Polynomial.aeval (X - 1 : ℝ[X])).toRingHom = sinhSquarePolynomialSeries := by
    apply PowerSeries.ext
    intro n
    simp only [sinhSquarePolynomialSeries, PowerSeries.coeff_map]
    change Polynomial.aeval (X - 1 : ℝ[X]) (C _) = C _
    simp only [Polynomial.aeval_C, algebraMap_eq]
  rw [hW]
  simp

/-- Each even base coefficient is the corresponding sinh coefficient composed with `X - 1`. -/
theorem coeff_even_tanhKernel (d : ℝ) (n : ℕ) :
    PowerSeries.coeff (2 * n) (tanhKernel d) =
      (PowerSeries.coeff (2 * n) (hyperbolicKernel d)).comp (X - 1) := by
  rw [tanhKernel_eq_map_hyperbolicKernel, PowerSeries.coeff_map]
  rfl

end RealRooted.TuranHurwitz
