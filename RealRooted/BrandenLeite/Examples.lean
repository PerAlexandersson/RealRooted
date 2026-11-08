module

import RealRooted.BrandenLeite.PositivePowerFactors
import RealRooted.BrandenLeite.LogarithmicFactors
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import RealRooted.BrandenLeite.AffineNegativePower
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
import Mathlib.Tactic

/-! # Regression examples for the Brändén–Leite factor theorems

Concrete instances of `affineNegativePowerCoeff_factor_properties` and
`affineLogCoeff_factor_properties`: a nonintegral exponent with a nonmonomial numerator,
degree loss at valuation three, repeated factors, the logarithmic limit, and the exceptional
linear/linear family, which is a scalar multiple of a repeated linear factor.
-/

public section

open Polynomial

namespace RealRooted.BrandenLeite

/-- Nonintegral exponent and genuinely nonmonomial numerator, matching the
example in the source note. -/
example (n : ℕ) :
    let q := fun m => affineNegativePowerCoeff (1 / 2 : ℝ)
      (((1 - X) * (1 - C 2 * X) : Polynomial ℝ) : PowerSeries ℝ)
      ((X * (1 + C 3 * X) : Polynomial ℝ) : PowerSeries ℝ) m
    (q n).Splits ∧ (q n).natDegree = n ∧ Interl (q n) (q (n + 1)) := by
  have hp := affineNegativePowerCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp)
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 2)
    (by intro i _; fin_cases i <;> norm_num)
    (Finset.univ : Finset (Fin 1)) (fun _ => (3 : ℝ))
    (by intro i _; norm_num) (c := 1) (κ := 1 / 2)
    (by norm_num) (by norm_num) 1 (by norm_num) n
  simpa [Fin.prod_univ_two, Fin.prod_univ_one] using
    And.intro hp.2.1 (And.intro hp.2.2.2.1 hp.2.2.2.2.2)

/-- Valuation three exercises degree loss and the equal-degree interlacing
steps of the regularization limit. -/
example (n : ℕ) :
    let q := fun m => affineNegativePowerCoeff (1 / 2 : ℝ)
      (((1 - X) * (1 - C 2 * X) : Polynomial ℝ) : PowerSeries ℝ)
      ((C 2 * X ^ 3 * (1 + C 3 * X) : Polynomial ℝ) : PowerSeries ℝ) m
    (q n).natDegree = n / 3 ∧ Interl (q n) (q (n + 1)) := by
  have hp := affineNegativePowerCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp)
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 2)
    (by intro i _; fin_cases i <;> norm_num)
    (Finset.univ : Finset (Fin 1)) (fun _ => (3 : ℝ))
    (by intro i _; norm_num) (c := 2) (κ := 1 / 2)
    (by norm_num) (by norm_num) 3 (by norm_num) n
  simpa [Fin.prod_univ_two, Fin.prod_univ_one] using
    And.intro hp.2.2.2.1 hp.2.2.2.2.2

/-- Repeated denominator and numerator factors remain allowed. -/
example (n : ℕ) :
    let q := fun m => affineNegativePowerCoeff (1 / 2 : ℝ)
      (((1 - X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ)
      ((X ^ 2 * (1 + X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ) m
    (q n).Splits ∧ (q n).natDegree = n / 2 ∧ Interl (q n) (q (n + 1)) := by
  have hp := affineNegativePowerCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp) (fun _ => (1 : ℝ))
    (by intro i _; norm_num)
    (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
    (by intro i _; norm_num) (c := 1) (κ := 1 / 2)
    (by norm_num) (by norm_num) 2 (by norm_num) n
  simpa [Fin.prod_univ_two, pow_two] using
    And.intro hp.2.1 (And.intro hp.2.2.2.1 hp.2.2.2.2.2)

/-- The logarithmic limit retains the same higher-valuation degree and
orientation, starting at positive row index. -/
example (n : ℕ) :
    let ℓ := fun m => affineLogCoeff
      (((1 - X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ)
      ((X ^ 2 * (1 + X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ) m
    (ℓ (n + 1)).Splits ∧ (ℓ (n + 1)).natDegree = (n + 1) / 2 ∧
      Interl (ℓ (n + 1)) (ℓ (n + 2)) := by
  have hp := affineLogCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp) (fun _ => (1 : ℝ))
    (by intro i _; norm_num)
    (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
    (by intro i _; norm_num) (c := 1) (by norm_num) 2 (by norm_num)
    (n + 1) (Nat.succ_ne_zero n)
  simpa [Fin.prod_univ_two, pow_two, Nat.add_assoc] using
    And.intro hp.2.1 (And.intro hp.2.2.2.1 hp.2.2.2.2.2)

/-- The linear/linear exceptional case is exactly a positive scalar times
a repeated linear factor. It provides an exact regression for the exceptional family. -/
theorem affineNegativePowerCoeff_one_sub_X (κ : ℝ) (n : ℕ) :
    affineNegativePowerCoeff κ (1 - PowerSeries.X) PowerSeries.X n =
      C (Ring.multichoose κ n) * (1 + X) ^ n := by
  unfold affineNegativePowerCoeff
  have harg : PowerSeries.map Polynomial.C (1 - PowerSeries.X : PowerSeries ℝ) -
      PowerSeries.C Polynomial.X * PowerSeries.map Polynomial.C PowerSeries.X - 1 =
      PowerSeries.C (-(1 + Polynomial.X) : Polynomial ℝ) *
        (PowerSeries.X : PowerSeries (Polynomial ℝ)) := by
    simp only [map_sub, map_one, PowerSeries.map_X, map_neg, map_add]
    ring
  have hsmul := PowerSeries.smul_eq_C_mul (R := Polynomial ℝ)
    (PowerSeries.X : PowerSeries (Polynomial ℝ)) (-(1 + Polynomial.X))
  have hrescale :=
    (PowerSeries.rescale_eq_subst (R := Polynomial ℝ) (-(1 + Polynomial.X))
      (PowerSeries.binomialSeries (Polynomial ℝ) (-C κ))).trans
      (congrArg
        (fun g : PowerSeries (Polynomial ℝ) =>
          PowerSeries.subst g (PowerSeries.binomialSeries (Polynomial ℝ) (-C κ))) hsmul)
  rw [harg]
  calc
    _ = PowerSeries.coeff n (PowerSeries.rescale (-(1 + Polynomial.X))
        (PowerSeries.binomialSeries (Polynomial ℝ) (-C κ))) :=
      congrArg (PowerSeries.coeff n) hrescale.symm
    _ = (-(1 + X)) ^ n * Ring.choose (-C κ) n := by
      rw [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff]
      simp only [smul_eq_mul, mul_one]
    _ = (1 + X) ^ n * ((-1 : Polynomial ℝ) ^ n * Ring.choose (-C κ) n) := by
      rw [neg_pow]
      ring
    _ = C (Ring.multichoose κ n) * (1 + X) ^ n := by
      rw [Ring.neg_one_pow_mul_choose_neg,
        ← Ring.map_multichoose Polynomial.C κ n]
      ring

/-- A nonintegral exponent does not remove the repeated-root exception. -/
example (n : ℕ) :
    affineNegativePowerCoeff (1 / 2 : ℝ)
      (1 - PowerSeries.X) PowerSeries.X (n + 2) =
        C (Ring.multichoose (1 / 2 : ℝ) (n + 2)) * (1 + X) ^ (n + 2) :=
  affineNegativePowerCoeff_one_sub_X (1 / 2) (n + 2)

/-- In the exceptional family, `-1` is simultaneously a root of every
row of degree at least two and of its derivative. -/
example (n : ℕ) :
    let p := affineNegativePowerCoeff (1 / 2 : ℝ)
      (1 - PowerSeries.X) PowerSeries.X (n + 2)
    p.eval (-1) = 0 ∧ p.derivative.eval (-1) = 0 := by
  dsimp
  rw [affineNegativePowerCoeff_one_sub_X]
  constructor <;> simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

end RealRooted.BrandenLeite
