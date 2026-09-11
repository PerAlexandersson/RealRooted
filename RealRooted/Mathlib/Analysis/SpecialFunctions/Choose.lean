import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Rescaled binomial-coefficient limit

This Mathlib-shaped lemma is the fixed-degree asymptotic used by rescaled
Jensen polynomials.
-/

open Asymptotics Filter Nat Topology

noncomputable section

/-- For fixed `k`, `choose n k / n^k` tends to `1 / k!`. -/
theorem tendsto_choose_mul_inv_pow_atTop (k : ℕ) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    field_simp
  have hequiv : (fun n : ℕ => (n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k) ~[atTop]
      (fun n : ℕ => ((n : ℝ) * (n : ℝ)⁻¹) ^ k / k.factorial) := by
    calc
      _ ~[atTop] (fun n : ℕ => ((n : ℝ) ^ k / k.factorial) * ((n : ℝ)⁻¹) ^ k) :=
        (isEquivalent_choose k).mul
          (IsEquivalent.refl : (fun n : ℕ => ((n : ℝ)⁻¹) ^ k) ~[atTop]
            (fun n : ℕ => ((n : ℝ)⁻¹) ^ k))
      _ ~[atTop] _ := EventuallyEq.isEquivalent (.of_eq (by ext n; field))
  refine (IsEquivalent.tendsto_nhds_iff hequiv).mpr ?_
  simpa [div_eq_mul_inv] using (hmul.pow k).mul_const ((k.factorial : ℝ)⁻¹)

/-- The rescaled fixed-degree binomial coefficient is bounded by `1 / k!`. -/
theorem norm_choose_mul_inv_pow_le (n k : ℕ) :
    ‖(n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k‖ ≤ 1 / (k.factorial : ℝ) := by
  by_cases hn : n = 0
  · subst n
    cases k <;> norm_num
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [norm_mul, Real.norm_of_nonneg (by positivity), norm_pow,
      norm_inv, Real.norm_of_nonneg (by positivity)]
    have hchoose := Nat.choose_le_pow_div (α := ℝ) k n
    calc
      (n.choose k : ℝ) * (n : ℝ)⁻¹ ^ k = (n.choose k : ℝ) / (n : ℝ) ^ k := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ ((n : ℝ) ^ k / k.factorial) / (n : ℝ) ^ k :=
        (div_le_div_iff_of_pos_right (pow_pos (by positivity) _)).mpr hchoose
      _ = 1 / k.factorial := by field_simp
