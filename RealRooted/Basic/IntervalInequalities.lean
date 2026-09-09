import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import RealRooted.Mathlib.Data.Nat.Cast.Basic
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.Mathlib.Data.List.Interleave

open Polynomial

noncomputable section

namespace RealRooted


lemma quadratic_nonneg_on_unit_interval_of_coeffs_nonneg
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ A + B * β + C * β ^ 2 := by
  positivity

lemma quadratic_nonneg_on_unit_interval_of_endpoint_nonneg_of_c_nonneg
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hEnd : 0 ≤ A + B + C)
    (hC : 0 ≤ C) (hBneg : B < 0 → C = 0) :
    0 ≤ A + B * β + C * β ^ 2 := by
  by_cases hB : 0 ≤ B
  · exact quadratic_nonneg_on_unit_interval_of_coeffs_nonneg hβ0 hA hB hC
  · have hEnd' : 0 ≤ A + B := by simp_all
    have : 0 ≤ (1 - β) * A + β * (A + B) :=
      add_nonneg (mul_nonneg (sub_nonneg_of_le hβ1) hA) (mul_nonneg hβ0 hEnd')
    have : A + B * β + C * β ^ 2 = (1 - β) * A + β * (A + B) := by
      rw [hBneg (lt_of_not_ge hB)]
      ring_nf
    lia

lemma quadratic_nonneg_on_unit_interval_of_endpoint_nonneg_of_vertex_or_discriminant
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hEnd : 0 ≤ A + B + C)
    (hC : 0 ≤ C)
    (hBneg : B < 0 → 2 * C ≤ -B ∨ B ^ 2 ≤ 4 * C * A) :
    0 ≤ A + B * β + C * β ^ 2 := by
  by_cases hB : 0 ≤ B
  · exact quadratic_nonneg_on_unit_interval_of_coeffs_nonneg hβ0 hA hB hC
  · cases hBneg (lt_of_not_ge hB)
    · have hβm1 : β - 1 ≤ 0 := tsub_nonpos.mpr hβ1
      have hβp1 : β + 1 ≤ 2 := by linarith
      have : C * (β + 1) ≤ C * 2 := mul_le_mul_of_nonneg_left hβp1 hC
      have hfactor : B + C * (β + 1) ≤ 0 := by linarith
      have : 0 ≤ (β - 1) * (B + C * (β + 1)) := mul_nonneg_of_nonpos_of_nonpos hβm1 hfactor
      grind
    · have : 0 < C := lt_of_le_of_ne hC (by intro rfl; simp_all)
      have : 0 ≤ (2 * C * β + B) ^ 2 := sq_nonneg _
      have : 0 ≤ 4 * C * (A + B * β + C * β ^ 2) := by grind
      simp_all
end RealRooted
