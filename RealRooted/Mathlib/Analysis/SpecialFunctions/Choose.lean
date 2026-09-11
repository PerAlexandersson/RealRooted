import Mathlib.Analysis.SpecialFunctions.Choose

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
