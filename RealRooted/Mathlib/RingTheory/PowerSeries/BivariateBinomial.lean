/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Tactic

/-! The universal bivariate Taylor coefficients of a generalized binomial
series: the coefficient of `x ^ k * y ^ m` in `(1 + x + y) ^ r`. -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- The coefficient of bidegree `(k,m)` in `(1+x+y)^r` separates into
`choose r k` times the coefficient of degree `m` in `(1+x)^(r-k)`. -/
theorem coeff_subst_add_binomialSeries (r : R) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (subst ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) +
        MvPowerSeries.X (1 : Fin 2)) (binomialSeries R r)) =
      Ring.choose r (e 0) * Ring.choose (r - (e 0 : R)) (e 1) := by
  rw [coeff_subst_X_zero_add_X_one]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  have h := Ring.choose_smul_choose r (n := e 0 + e 1) (k := e 0)
    (Nat.le_add_right _ _)
  simpa only [nsmul_eq_mul, Nat.add_sub_cancel_left] using h

/-- Extracting one variable from the universal binomial series gives a
shifted binomial series in the other variable. This is the formal Taylor
formula needed before substituting `Q-1` and `-tB`. -/
theorem coeff_finSuccEquiv_subst_add_binomialSeries (r : R) (k : ℕ) :
    coeff k (MvPowerSeries.finSuccEquiv R 1
      (subst ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) +
        MvPowerSeries.X (1 : Fin 2)) (binomialSeries R r))) =
      Ring.choose r k •
        subst (MvPowerSeries.X (0 : Fin 1)) (binomialSeries R (r - (k : R))) := by
  apply MvPowerSeries.ext
  intro e
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, coeff_subst_add_binomialSeries,
    MvPowerSeries.coeff_smul, coeff_subst_single]
  have he : e = Finsupp.single (0 : Fin 1) (e 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  simp only [Finsupp.cons_zero, show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    Finsupp.cons_succ, ite_eq_left he, binomialSeries_coeff, smul_eq_mul, mul_one]

end PowerSeries
