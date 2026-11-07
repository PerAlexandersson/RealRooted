/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-! Normalized linear factors under reflection and formal-series coercion. -/

public section

namespace Polynomial

/-- Changing the sign of the variable changes each normalized negative
linear factor into a positive linear factor. -/
theorem prod_one_sub_C_mul_X_comp_neg_X {R ι : Type*} [CommRing R]
    (s : Finset ι) (α : ι → R) :
    (∏ i ∈ s, (1 - C (α i) * X : R[X])).comp (-X) =
      ∏ i ∈ s, (1 + C (α i) * X : R[X]) := by
  rw [Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp, mul_neg, sub_neg_eq_add]

/-- Coercing a product of normalized linear polynomial factors to formal
power series preserves the displayed product. -/
theorem coe_prod_one_sub_C_mul_X {R ι : Type*} [CommRing R]
    (s : Finset ι) (α : ι → R) :
    ((∏ i ∈ s, (1 - C (α i) * X) : R[X]) : PowerSeries R) =
      ∏ i ∈ s, (1 - PowerSeries.C (α i) * PowerSeries.X : PowerSeries R) := by
  rw [← coeToPowerSeries.ringHom_apply, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- Products of normalized positive linear factors split over the reals. -/
theorem splits_prod_one_add_C_mul_X {R ι : Type*} [Field R]
    (s : Finset ι) (α : ι → R) :
    (∏ i ∈ s, (1 + C (α i) * X : R[X])).Splits := by
  apply Polynomial.Splits.prod
  intro i _
  apply Polynomial.Splits.of_natDegree_le_one
  exact Polynomial.natDegree_add_le_of_degree_le (by simp)
    ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)

/-- Coercing a product of normalized positive linear polynomial factors
to formal power series preserves its factor presentation. -/
theorem coe_prod_one_add_C_mul_X {R ι : Type*} [CommRing R]
    (s : Finset ι) (β : ι → R) :
    ((∏ i ∈ s, (1 + C (β i) * X) : Polynomial R) : PowerSeries R) =
      ∏ i ∈ s, (1 + PowerSeries.C (β i) * PowerSeries.X : PowerSeries R) := by
  rw [← coeToPowerSeries.ringHom_apply, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- The usual PF numerator factorization is preserved under the
polynomial-to-formal-series coercion. -/
theorem coe_C_mul_X_pow_prod_one_add_C_mul_X {R ι : Type*} [CommRing R]
    (c : R) (r : ℕ) (s : Finset ι) (β : ι → R) :
    ((C c * X ^ r * ∏ i ∈ s, (1 + C (β i) * X) : Polynomial R) : PowerSeries R) =
      PowerSeries.C c * PowerSeries.X ^ r *
        ∏ i ∈ s, (1 + PowerSeries.C (β i) * PowerSeries.X : PowerSeries R) := by
  rw [coe_mul, coe_mul, coe_C, coe_pow, coe_X, coe_prod_one_add_C_mul_X]

end Polynomial
