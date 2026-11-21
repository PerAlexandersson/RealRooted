module

public import RealRooted.TuranHurwitz.BoundaryValues
public import RealRooted.TuranHurwitz.InteriorStability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The main theorem outside the exponential boundary

The only admissible tuples excluded below have `a₁ > 0` and `b₁ = tau = 0`.
The zero scale inside the open parameter set is handled by its exact pole value.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The only zero of the normalization scale is the real pole. -/
theorem eq_pole_of_normalizationScale_eq_zero {c : Parameters} (ha : c.a₁ ≠ 0) (z : ℂ)
    (hz : normalizationScale c z = 0) :
    c.tau ≠ 0 ∧ z = (((1 / c.tau - c.lam : ℝ)) : ℂ) := by
  have haC : (c.a₁ : ℂ) / 2 ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr ha) (by norm_num)
  have hzero : 1 - (c.tau : ℂ) * (z + (c.lam : ℂ)) = 0 :=
    (mul_eq_zero.mp hz).resolve_left haC
  have ht : c.tau ≠ 0 := by
    intro heq
    simp [heq] at hzero
  refine ⟨ht, ?_⟩
  have htC : (c.tau : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  push_cast
  apply (mul_left_injective₀ htC)
  field_simp
  linear_combination -hzero

/-- Nonvanishing on the entire half-plane for the nondegenerate parameter range. -/
theorem aeval_family_turan_ne_zero_nondegenerate {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hden : 0 < c.b₁ + c.tau * c.a₁) (m n : ℕ) (z : ℂ)
    (hz : -c.lam < z.re) : Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  by_cases hscale : normalizationScale c z = 0
  · obtain ⟨ht, rfl⟩ := eq_pole_of_normalizationScale_eq_zero ha.ne' z hscale
    exact aeval_family_turan_pole_ne_zero hc ha
      (lt_of_le_of_ne hc.tau_nonneg (Ne.symm ht)) m n
  · exact aeval_family_turan_ne_zero_of_scale_ne_zero hc ha hden m n z hz hscale

/-- Theorem 1.1(i) away from `a₁ > 0, b₁ = tau = 0`, with polynomial nonzeroness explicit. -/
theorem family_turan_stable_of_nondegenerate {c : Parameters} (hc : c.Admissible)
    (hcase : c.a₁ = 0 ∨ 0 < c.b₁ + c.tau * c.a₁) (m n : ℕ) :
    turan m n (family c) ≠ 0 ∧
      ∀ z : ℂ, -c.lam < z.re → Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  have hnonvanishing : ∀ z : ℂ, -c.lam < z.re →
      Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
    intro z hz
    rcases hcase with ha | hden
    · exact aeval_family_turan_ne_zero_of_a₁_eq_zero hc ha m n z hz
    · by_cases ha : c.a₁ = 0
      · exact aeval_family_turan_ne_zero_of_a₁_eq_zero hc ha m n z hz
      · exact aeval_family_turan_ne_zero_nondegenerate hc
          (lt_of_le_of_ne hc.a₁_nonneg (Ne.symm ha)) hden m n z hz
  refine ⟨?_, hnonvanishing⟩
  intro heq
  have h := hnonvanishing (1 - (c.lam : ℂ)) (by simp)
  simp [heq] at h

/-- Admissible parameters outside the completed range have exactly the exponential boundary form. -/
theorem exponential_boundary_of_not_nondegenerate {c : Parameters} (hc : c.Admissible)
    (hcase : ¬(c.a₁ = 0 ∨ 0 < c.b₁ + c.tau * c.a₁)) :
    0 < c.a₁ ∧ c.b₁ = 0 ∧ c.tau = 0 ∧ 0 < c.b₂ := by
  have ha : 0 < c.a₁ := lt_of_le_of_ne hc.a₁_nonneg
    (Ne.symm (fun hzero => hcase (Or.inl hzero)))
  have hsum : c.b₁ + c.tau * c.a₁ = 0 := by
    have hnonpos : c.b₁ + c.tau * c.a₁ ≤ 0 :=
      le_of_not_gt (fun hpos => hcase (Or.inr hpos))
    exact le_antisymm hnonpos (add_nonneg hc.b₁_nonneg (mul_nonneg hc.tau_nonneg ha.le))
  have hb : c.b₁ = 0 := by nlinarith [hc.b₁_nonneg, hc.tau_nonneg]
  have ht : c.tau = 0 := by nlinarith [hc.tau_nonneg]
  exact ⟨ha, hb, ht, by simpa only [hb, ht, zero_mul, zero_add, add_zero]
    using hc.numerator_pos⟩

end RealRooted.TuranHurwitz
