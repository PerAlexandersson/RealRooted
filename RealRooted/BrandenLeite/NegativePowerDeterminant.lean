module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
public import RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialDerivative
import RealRooted.BrandenLeite.WeightedDerivativeKernel.Determinant
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence

/-! Determinants of coefficients of canonical formal negative powers. -/

public section

open PowerSeries

namespace RealRooted.BrandenLeite

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- The coefficient of a normalized formal negative power is a weighted
Hessenberg determinant, with a factorial normalization. -/
theorem det_weightedDerivativeKernel_subst_binomialSeries_neg
    (κ : R) (H : PowerSeries R) (hH : constantCoeff H = 1) (n : ℕ) :
    ((weightedDerivativeKernel κ (fun k => (-1 : R) ^ k * coeff k H)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) R).det =
      (n.factorial : R) * coeff n (subst (H - 1) (binomialSeries R (-κ))) := by
  apply det_weightedDerivativeKernel_signed_of_recurrence
  · simpa only [coeff_zero_eq_constantCoeff_apply] using hH
  · simpa only [coeff_zero_eq_constantCoeff_apply] using
      constantCoeff_subst_binomialSeries_neg κ H hH
  · exact fun k => coeff_recurrence_of_negPower_ode κ H _
      (by simpa only [coeff_zero_eq_constantCoeff_apply] using hH)
      (subst_binomialSeries_neg_ode κ H hH) k

end RealRooted.BrandenLeite
