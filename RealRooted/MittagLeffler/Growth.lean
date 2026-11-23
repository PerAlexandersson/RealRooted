module

public import RealRooted.MittagLeffler.Basic
public import TauCeti.Analysis.Complex.GrowthOrder

/-!
# Growth of integer-parameter Mittag--Leffler functions

At radius at least one, the defining series is bounded by a subsequence of
the exponential series at the `r`-th root of that radius. Consequently its
order is at most `1/r`. This argument allows every natural residue, even
where positive Type-I membership is not asserted.
-/

public section

open Complex Filter Asymptotics Bornology

namespace RealRooted

/-- Outside the unit disk an integer-stride Mittag--Leffler series is bounded
by the exponential at the corresponding root of the radius. -/
theorem norm_mittagLefflerNat_le_exp {r s : ℕ} (hr : 0 < r)
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖mittagLefflerNat r s z‖ ≤ Real.exp (‖z‖ ^ (r : ℝ)⁻¹) := by
  let t : ℝ := ‖z‖ ^ (r : ℝ)⁻¹
  have ht : 1 ≤ t := Real.one_le_rpow hz (by positivity)
  have htpow : t ^ r = ‖z‖ := Real.rpow_inv_natCast_pow (norm_nonneg z) hr.ne'
  have hS : HasSum (fun k : ℕ ↦ t ^ k / (k.factorial : ℝ)) (Real.exp t) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t
  have hinj : Function.Injective (fun k : ℕ ↦ s + r * k) := by
    intro j k hjk
    exact mul_right_injective₀ hr.ne' (Nat.add_left_cancel hjk)
  have hsub := hS.summable.comp_injective hinj
  have hbound (k : ℕ) : ‖z ^ k / ((s + r * k).factorial : ℂ)‖ ≤
      t ^ (s + r * k) / ((s + r * k).factorial : ℝ) := by
    rw [norm_div, norm_pow, norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [pow_add, pow_mul, htpow]
    exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg z) k) (one_le_pow₀ ht)
  have hnorm : Summable (fun k : ℕ ↦ ‖z ^ k / ((s + r * k).factorial : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound hsub
  rw [mittagLefflerNat_eq_tsum]
  calc
    _ ≤ ∑' k : ℕ, ‖z ^ k / ((s + r * k).factorial : ℂ)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, t ^ (s + r * k) / ((s + r * k).factorial : ℝ) :=
      hnorm.tsum_le_tsum hbound hsub
    _ ≤ ∑' k : ℕ, t ^ k / (k.factorial : ℝ) := by
      simpa only [Function.comp_def] using
        tsum_comp_le_tsum_of_inj hS.summable (fun k ↦ by positivity) hinj
    _ = _ := hS.tsum_eq

/-- Integer stride `r > 0` gives a Mittag--Leffler growth order at most `1/r`. -/
theorem orderLE_mittagLefflerNat {r s : ℕ} (hr : 0 < r) :
    TauCeti.OrderLE (mittagLefflerNat r s) (r : ℝ)⁻¹ := by
  rw [TauCeti.orderLE_def]
  intro A hA
  apply IsBigO.of_bound 1
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
  simp only [Real.norm_eq_abs, Real.abs_exp, one_mul]
  exact (norm_mittagLefflerNat_le_exp hr hz).trans
    (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hz hA.le))

end RealRooted
