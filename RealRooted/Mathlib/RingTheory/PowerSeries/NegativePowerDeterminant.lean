/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialDerivative
import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel.Determinant
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence

/-! Determinants of coefficients of canonical formal negative powers. -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- The coefficient of a normalized formal negative power is a weighted
Hessenberg determinant, with a factorial normalization. -/
theorem det_weightedDerivativeKernel_subst_binomialSeries_neg
    (κ : R) (H : PowerSeries R) (hH : constantCoeff H = 1) (n : ℕ) :
    ((Matrix.weightedDerivativeKernel κ (fun k => (-1 : R) ^ k * coeff k H)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) R).det =
      (n.factorial : R) * coeff n (subst (H - 1) (binomialSeries R (-κ))) := by
  apply Matrix.det_weightedDerivativeKernel_signed_of_recurrence
  · simpa only [coeff_zero_eq_constantCoeff_apply] using hH
  · simpa only [coeff_zero_eq_constantCoeff_apply] using
      constantCoeff_subst_binomialSeries_neg κ H hH
  · exact fun k => coeff_recurrence_of_negPower_ode κ H _
      (by simpa only [coeff_zero_eq_constantCoeff_apply] using hH)
      (subst_binomialSeries_neg_ode κ H hH) k

end PowerSeries
