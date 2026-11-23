/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Complex.LinearProductDivisor
import Mathlib.Tactic.Ring

/-!
# Positive slopes and native zero multiplicities

The root of a positive linear factor is its negative reciprocal. The
fiber of this root map is equivalent to the vanishing-factor fiber, so
its finite cardinality is exactly the native divisor multiplicity.
-/

public section

namespace Complex

/-- The zero represented by one strictly positive linear-product slope. -/
@[expose] noncomputable def positiveSlopeRoot {ι : Type*} (a : ι → ℝ)
    (i : {i // 0 < a i}) : ℂ := -((a i : ℂ)⁻¹)

/-- The spectral rate of a positive linear factor is the reciprocal slope. -/
@[simp] theorem norm_positiveSlopeRoot {ι : Type*} {a : ι → ℝ}
    (i : {i // 0 < a i}) : ‖positiveSlopeRoot a i‖ = (a i)⁻¹ := by
  simp only [positiveSlopeRoot, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos i.property]

private theorem one_add_mul_eq_zero_iff_eq_neg_inv {a z : ℂ} (ha : a ≠ 0) :
    1 + a * z = 0 ↔ z = -a⁻¹ := by
  constructor
  · intro hz
    have hmul : a * z = -1 := eq_neg_of_add_eq_zero_right hz
    calc z = a⁻¹ * (a * z) := (inv_mul_cancel_left₀ ha z).symm
      _ = -a⁻¹ := by rw [hmul, mul_neg_one]
  · rintro rfl
    simp only [mul_neg, mul_inv_cancel₀ ha, add_neg_cancel]

/-- Fibers of the positive-slope root map are exactly the factors that
vanish at the given point. This preserves every repeated slope. -/
noncomputable def positiveSlopeRootFiberEquiv {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (z : ℂ) :
    {i : {i // 0 < a i} // positiveSlopeRoot a i = z} ≃
      {i // 1 + (a i : ℂ) * z = 0} where
  toFun i := ⟨i.val.val, by
    have hne : (a i.val : ℂ) ≠ 0 := by exact_mod_cast i.val.property.ne'
    exact (one_add_mul_eq_zero_iff_eq_neg_inv hne).mpr i.property.symm⟩
  invFun i := by
    have hne : a i ≠ 0 := by
      intro hz
      have h : (1 : ℂ) = 0 := by
        simpa only [hz, ofReal_zero, zero_mul, add_zero] using i.property
      exact one_ne_zero h
    have hpos : 0 < a i := lt_of_le_of_ne (ha i) hne.symm
    have hneC : (a i : ℂ) ≠ 0 := by exact_mod_cast hne
    exact ⟨⟨i.val, hpos⟩, ((one_add_mul_eq_zero_iff_eq_neg_inv hneC).mp i.property).symm⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/-- A summable nonnegative slope family has finite root-map fibers. -/
theorem finite_positiveSlopeRoot_fiber {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (z : ℂ) :
    {i : {i // 0 < a i} | positiveSlopeRoot a i = z}.Finite := by
  apply ((finite_linearProduct_zero_fiber hs z).preimage
    (Subtype.val_injective.injOn)).subset
  intro i hi
  exact (positiveSlopeRootFiberEquiv ha z ⟨i, hi⟩).property

/-- Native divisor multiplicity is the finite cardinality of the
positive-slope root fiber, after any nonzero constant normalization. -/
theorem divisor_const_mul_linearProduct_eq_natCard_root_fiber
    {ι : Type*} {a : ι → ℝ} {c : ℂ} (hc : c ≠ 0)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (z : ℂ) :
    MeromorphicOn.divisor (fun w : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * w)) Set.univ z =
      (Nat.card {i : {i // 0 < a i} // positiveSlopeRoot a i = z} : ℤ) := by
  rw [divisor_const_mul_tprod_one_add_ofReal_mul_apply hc hs z]
  exact_mod_cast Nat.card_congr (positiveSlopeRootFiberEquiv ha z).symm

end Complex
