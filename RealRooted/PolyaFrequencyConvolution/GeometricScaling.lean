import RealRooted.PolyaFrequencyConvolution

/-!
# Geometric scaling of Pólya-frequency sequences

This file proves that multiplying the `n`th entry of a Pólya-frequency
sequence by a nonnegative geometric weight preserves total nonnegativity of
its Toeplitz matrix.
-/

open Matrix

namespace RealRooted

/-- Multiply the `n`th entry of a sequence by `c ^ n`. -/
def geometricScale (c : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  c ^ n * a n

@[simp]
theorem geometricScale_apply (c : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    geometricScale c a n = c ^ n * a n :=
  rfl

@[simp]
theorem geometricScale_one (a : ℕ → ℝ) :
    geometricScale 1 a = a := by
  funext n
  simp

/-- Nonnegative geometric rescaling preserves the Pólya-frequency
property. -/
protected theorem IsPolyaFreqSeq.geometricScale
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (c : ℝ) (hc : 0 ≤ c) :
    IsPolyaFreqSeq (geometricScale c a) := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · have htoeplitz : toeplitz (geometricScale 0 a) = a 0 • 1 := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.one_apply]
      rcases eq_or_ne i j with rfl | hij
      · simp [toeplitz_apply]
      · by_cases hji : j ≤ i
        · have hlt : j < i := lt_of_le_of_ne hji (Ne.symm hij)
          have hsub : i - j ≠ 0 := Nat.sub_ne_zero_of_lt hlt
          simp [toeplitz_apply, hji, geometricScale, hsub, hij]
        · simp [toeplitz_apply, hji, hij]
    rw [IsPolyaFreqSeq, htoeplitz]
    exact Matrix.IsTotallyNonneg.smul Matrix.IsTotallyNonneg.one (a 0)
      (ha.nonneg 0)
  · have hcne : c ≠ 0 := ne_of_gt hcpos
    have htoeplitz : toeplitz (geometricScale c a) =
        Matrix.of fun i j => c ^ i * ((c⁻¹) ^ j * (toeplitz a) i j) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [toeplitz_apply]
      by_cases hji : j ≤ i
      · rw [if_pos hji, toeplitz_apply, if_pos hji, geometricScale,
          pow_sub₀ c hcne hji]
        simp only [inv_pow]
        ring
      · rw [if_neg hji, toeplitz_apply, if_neg hji]
        ring
    rw [IsPolyaFreqSeq, htoeplitz]
    exact ha.scaleRowsCols (fun i => c ^ i) (fun j => (c⁻¹) ^ j)
      (fun _ => pow_nonneg hc _) (fun _ => pow_nonneg (inv_nonneg.mpr hc) _)

/-- Every nonnegative geometric sequence is Pólya-frequency. -/
theorem geometric_isPolyaFreqSeq (c : ℝ) (hc : 0 ≤ c) :
    IsPolyaFreqSeq (fun n : ℕ => c ^ n) := by
  convert constantOne_isPolyaFreqSeq.geometricScale c hc using 1
  funext n
  simp [geometricScale]

end RealRooted
