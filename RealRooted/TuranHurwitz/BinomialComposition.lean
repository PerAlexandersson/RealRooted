module

public import RealRooted.TuranHurwitz.FormalBinomial
import RealRooted.TuranHurwitz.CoefficientDerivation
import RealRooted.TuranHurwitz.FormalODE
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Products of normalized formal binomial powers

The multiplicativity law follows from a common formal differential equation.
It supplies the change-of-base identities needed to pass between sinh and tanh kernels.
-/

public section

namespace RealRooted.TuranHurwitz

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- Exponents add when two normalized binomial powers have the same formal base. -/
theorem binomial_subst_add (r s : ℝ) (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.binomialSeries ℝ r).subst g *
        (PowerSeries.binomialSeries ℝ s).subst g =
      (PowerSeries.binomialSeries ℝ (r + s)).subst g := by
  rw [PowerSeries.binomialSeries_add,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hg)]

/-- Opposite exponents cancel in a formal base with constant coefficient one. -/
theorem binomial_subst_mul_neg (r : ℝ) (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.binomialSeries ℝ r).subst g *
        (PowerSeries.binomialSeries ℝ (-r)).subst g = 1 := by
  rw [binomial_subst_add r (-r) g hg, add_neg_cancel, PowerSeries.binomialSeries_zero]
  simpa using subst_C_algebra (1 : ℝ) g
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg)

/-- A substituted real binomial series has constant coefficient one. -/
theorem constantCoeff_binomial_subst (r : ℝ) (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff ((PowerSeries.binomialSeries ℝ r).subst g) = 1 := by
  rw [PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero hg]
  simp

/-- Multiplication by the base raises a formal real binomial exponent by one. -/
theorem binomial_subst_shift (r : ℝ) (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    (1 + g) * (PowerSeries.binomialSeries ℝ (r - 1)).subst g =
      (PowerSeries.binomialSeries ℝ r).subst g := by
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have h := congrArg (fun f : PowerSeries ℝ => f.subst g)
    (one_add_X_mul_binomialSeries_pred r)
  have hone : (1 : PowerSeries ℝ).subst g = (1 : PowerSeries A) := by
    simpa using subst_C_algebra (1 : ℝ) g hsubst
  rw [PowerSeries.subst_mul hsubst, PowerSeries.subst_add hsubst,
    PowerSeries.subst_X hsubst, hone] at h
  exact h

/-- The logarithmic differential equation for a substituted real binomial series. -/
theorem binomial_subst_euler (r : ℝ) (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    (1 + g) * PowerSeries.derivative ((PowerSeries.binomialSeries ℝ r).subst g) =
      PowerSeries.C (algebraMap ℝ A r) *
        (PowerSeries.binomialSeries ℝ r).subst g * PowerSeries.derivative g := by
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  rw [derivative_subst_algebra _ _ hsubst, derivative_binomialSeries,
    PowerSeries.subst_mul hsubst, subst_C_algebra _ _ hsubst]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  calc
    _ = PowerSeries.C (algebraMap ℝ A r) *
        ((1 + g) * (PowerSeries.binomialSeries ℝ (r - 1)).subst g) *
          PowerSeries.derivative g := by ring
    _ = _ := by rw [binomial_subst_shift r g hg]

/-- Normalized real binomial powers are multiplicative in their formal unit bases. -/
theorem binomial_subst_mul [HasUniqueDiv A] (r : ℝ) (g h : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) (hh : PowerSeries.constantCoeff h = 0) :
    (PowerSeries.binomialSeries ℝ r).subst g * (PowerSeries.binomialSeries ℝ r).subst h =
      (PowerSeries.binomialSeries ℝ r).subst (g + h + g * h) := by
  let U := (1 + g) * (1 + h)
  let V := PowerSeries.C (algebraMap ℝ A r) * PowerSeries.derivative U
  let F := (PowerSeries.binomialSeries ℝ r).subst g * (PowerSeries.binomialSeries ℝ r).subst h
  let G := (PowerSeries.binomialSeries ℝ r).subst (g + h + g * h)
  have hk : PowerSeries.constantCoeff (g + h + g * h) = 0 := by simp [hg, hh]
  have hU : IsUnit U := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [U, hg, hh])
  have hG : IsUnit G := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [show PowerSeries.constantCoeff G = 1 from constantCoeff_binomial_subst r _ hk]
    exact isUnit_one)
  have hFdiff : U * PowerSeries.derivative F = V * F := by
    have h₁ := binomial_subst_euler r g hg
    have h₂ := binomial_subst_euler r h hh
    dsimp [U, V, F]
    simp only [PowerSeries.derivative.leibniz, map_add, PowerSeries.derivative_one,
      zero_add, smul_eq_mul]
    linear_combination ((1 + h) * (PowerSeries.binomialSeries ℝ r).subst h) * h₁ +
      ((1 + g) * (PowerSeries.binomialSeries ℝ r).subst g) * h₂
  have hGdiff : U * PowerSeries.derivative G = V * G := by
    have hkdiff := binomial_subst_euler r (g + h + g * h) hk
    have hbase : U = 1 + (g + h + g * h) := by dsimp [U]; ring
    dsimp [V, G]
    rw [hbase, map_add, PowerSeries.derivative_one, zero_add]
    linear_combination hkdiff
  apply eq_of_mul_derivative_eq hU hG hFdiff hGdiff
  simp only [F, G, map_mul, constantCoeff_binomial_subst r g hg,
    constantCoeff_binomial_subst r h hh, constantCoeff_binomial_subst r _ hk, one_mul]

end RealRooted.TuranHurwitz
