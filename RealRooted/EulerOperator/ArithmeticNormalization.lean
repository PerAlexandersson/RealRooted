module

public import RealRooted.EulerOperator.ArithmeticProduct
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Normalized arithmetic polar multipliers

The scale `r^r M^(r-1)` removes the falling-factorial attenuation in the
finite arithmetic polar approximants. The resulting coefficients converge
to the factorial ratio needed for exponential generating sections.
-/

public section

open Filter Topology

namespace RealRooted

/-- The scaling used in arithmetic sections has the required power identity. -/
private theorem arithmetic_scale_pow {r : ℕ} (hr : r ≠ 0) (M k : ℕ) :
    ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k * (M : ℝ) ^ k =
      ((r * M : ℕ) : ℝ) ^ (r * k) := by
  have he : (r - 1) * k + k = r * k := by
    calc
      _ = (r - 1 + 1) * k := by ring
      _ = _ := by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hr)]
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add, he, Nat.cast_mul, mul_pow]

/-- The two reflections in the arithmetic approximation cancel the signs
of its finite multiplier. -/
private theorem arithmetic_sign_cancel {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    (-1 : ℝ) ^ (r * k + k) * (-1) ^ (r * k - k) = 1 := by
  have hk : k ≤ r * k := Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hr)
  rw [← pow_add, show r * k + k + (r * k - k) = r * k + r * k by lia,
    pow_add, ← mul_pow]
  norm_num

/-- After reflection and scaling, the arithmetic multiplier is a ratio of
normalized descending factorials. -/
theorem arithmeticPolarMultiplier_normalized {r M k : ℕ}
    (hr : r ≠ 0) (hM : M ≠ 0) (hk : k ≤ M) :
    (-1 : ℝ) ^ (r * k + k) *
        (arithmeticPolarMultiplier r (r * M) (r * k) /
          arithmeticPolarMultiplier r (r * M) 0) *
        ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k =
      ((r * k).factorial : ℝ) / k.factorial *
        (((M.descFactorial k : ℝ) / (M : ℝ) ^ k) /
          (((r * M).descFactorial (r * k) : ℝ) / ((r * M : ℕ) : ℝ) ^ (r * k))) := by
  rw [arithmeticPolarMultiplier_ratio hr hk]
  have hsign := arithmetic_sign_cancel hr k
  have hscale := arithmetic_scale_pow hr M k
  have hrM : ((r * M : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hr hM)
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hdesc : ((r * M).descFactorial (r * k) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (Nat.mul_le_mul_left r hk)).ne'
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ = ((r * k).factorial : ℝ) / k.factorial *
        M.descFactorial k / (r * M).descFactorial (r * k) *
        ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k := by
      calc
        _ = ((-1 : ℝ) ^ (r * k + k) * (-1) ^ (r * k - k)) *
            (((r * k).factorial : ℝ) / k.factorial *
              M.descFactorial k / (r * M).descFactorial (r * k) *
              ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k) := by ring
        _ = _ := by rw [hsign, one_mul]
    _ = _ := by
      field_simp
      rw [← hscale]
      ring

/-- For a fixed stride and coefficient index, the normalized arithmetic
multiplier tends to the exponential-section factorial ratio. -/
theorem tendsto_arithmeticPolarMultiplier_normalized {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    Tendsto (fun M : ℕ => (-1 : ℝ) ^ (r * k + k) *
        (arithmeticPolarMultiplier r (r * M) (r * k) /
          arithmeticPolarMultiplier r (r * M) 0) *
        ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k)
      atTop (𝓝 (((r * k).factorial : ℝ) / k.factorial)) := by
  have hm : Tendsto (fun M : ℕ => r * M) atTop atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop n).mono fun M hM =>
      hM.trans (Nat.le_mul_of_pos_left M (Nat.pos_of_ne_zero hr))
  have hratio := (Nat.tendsto_descFactorial_div_pow_atTop k).div
    ((Nat.tendsto_descFactorial_div_pow_atTop (r * k)).comp hm) (by norm_num)
  have hlim := hratio.const_mul (((r * k).factorial : ℝ) / k.factorial)
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop k, eventually_ge_atTop 1] with M hk hM
  exact (arithmeticPolarMultiplier_normalized hr (by lia) hk).symm

end RealRooted
