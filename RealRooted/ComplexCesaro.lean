import Mathlib

/-!
# Cesaro averages of complex geometric sequences

This file proves a boundary case of the Cesaro convergence of geometric
sequences. If a complex number lies in the closed unit disk but is not one,
then the Cesaro averages of its powers tend to zero. The proof uses the finite
geometric-sum identity and does not require a density or equidistribution
argument.
-/

open Filter Finset

namespace RealRooted

private lemma tendsto_inv_nat :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- If `w` lies in the closed complex unit disk and is not one, then the
Cesaro averages of the powers of `w` tend to zero. -/
lemma tendsto_cesaro_pow_of_norm_le_one_of_ne_one
    {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ range N, w ^ n)
      atTop (nhds 0) := by
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => w ^ N - 1) := by
    refine ⟨2, eventually_map.mpr (Eventually.of_forall fun N => ?_)⟩
    dsimp
    calc
      ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖w‖ ^ N + 1 := by rw [norm_pow, norm_one]
      _ ≤ 2 := by
        have hpow : ‖w‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
        linarith
  have hnum : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • (w ^ N - 1))
      atTop (nhds 0) :=
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      tendsto_inv_nat hbounded
  have hmul : (fun N : ℕ =>
      ((N : ℝ)⁻¹ • ∑ n ∈ range N, w ^ n) * (w - 1))
      = fun N : ℕ => (N : ℝ)⁻¹ • (w ^ N - 1) := by
    funext N
    simp only [Complex.real_smul]
    rw [mul_assoc, geom_sum_mul]
  have hprod : Tendsto (fun N : ℕ =>
      ((N : ℝ)⁻¹ • ∑ n ∈ range N, w ^ n) * (w - 1))
      atTop (nhds 0) := hmul.symm ▸ hnum
  have hinv := hprod.mul_const (w - 1)⁻¹
  have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  convert hinv using 1
  · funext N
    simp only [Complex.real_smul]
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · simp

/-- A nonnegative real sequence containing a nonzero conjugate pair of
geometric modes cannot have those modes grow faster than its nonnegative real
mode. -/
theorem norm_le_of_nonneg_conjugate_geometric
    {x : ℕ → ℝ} {r : ℝ} {A z B : ℂ}
    (hr : 0 ≤ r)
    (hz : z.im ≠ 0)
    (hB : B ≠ 0)
    (hx : ∀ n,
      (x n : ℂ) =
        A * (r : ℂ) ^ n +
          B * z ^ n +
          (starRingEnd ℂ B) * (starRingEnd ℂ z) ^ n)
    (hx_nonneg : ∀ n, 0 ≤ x n) :
    ‖z‖ ≤ r := by
  by_contra hle
  have hzr : r < ‖z‖ := lt_of_not_ge hle
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    simp [h]
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let q : ℝ := r / ‖z‖
  let w : ℂ := z / (‖z‖ : ℂ)
  let y : ℕ → ℝ := fun n => x n / ‖z‖ ^ n
  have hnormalized : ∀ n,
      (y n : ℂ) =
        A * (q : ℂ) ^ n +
          B * w ^ n +
          (starRingEnd ℂ B) * (starRingEnd ℂ w) ^ n := by
    intro n
    simp only [y, q, w]
    rw [Complex.ofReal_div, Complex.ofReal_pow, hx, Complex.ofReal_div,
      div_pow, div_pow, map_div₀, Complex.conj_ofReal, div_pow]
    field_simp
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hq_nonneg : 0 ≤ q := by
    exact div_nonneg hr (norm_nonneg z)
  have hq_lt : q < 1 := by
    exact (div_lt_one hnorm_pos).mpr hzr
  have hw_norm : ‖w‖ = 1 := by
    simp [w, hnorm]
  have hw_im : w.im ≠ 0 := by
    simp only [w, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_div, sub_zero]
    exact div_ne_zero (mul_ne_zero hz hnorm)
      (Complex.normSq_pos.mpr (Complex.ofReal_ne_zero.mpr hnorm)).ne'
  have hy_nonneg : ∀ n, 0 ≤ y n := by
    intro n
    exact div_nonneg (hx_nonneg n) (pow_nonneg (norm_nonneg z) n)
  have hw_ne_one : w ≠ 1 := by
    intro h
    apply hw_im
    rw [h]
    simp
  have hcw_norm : ‖starRingEnd ℂ w‖ = 1 := by
    rw [Complex.norm_conj, hw_norm]
  have hcw_im : (starRingEnd ℂ w).im ≠ 0 := by
    simpa using neg_ne_zero.mpr hw_im
  have hcw_ne_one : starRingEnd ℂ w ≠ 1 := by
    intro h
    apply hcw_im
    rw [h]
    simp
  have hcw_sq_ne_one : (starRingEnd ℂ w) ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact hcw_ne_one h
    · apply hcw_im
      rw [h]
      simp
  have hq_norm : ‖(q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hq_nonneg]
    exact hq_lt.le
  have hq_ne_one : (q : ℂ) ≠ 1 := by
    exact_mod_cast ne_of_lt hq_lt
  let avg : (ℕ → ℂ) → ℕ → ℂ := fun f N =>
    ((N + 1 : ℕ) : ℝ)⁻¹ • ∑ n ∈ range (N + 1), f n
  have havg_q : Tendsto (avg fun n => (q : ℂ) ^ n) atTop (nhds 0) := by
    simpa [avg, Function.comp_def] using
      (tendsto_cesaro_pow_of_norm_le_one_of_ne_one hq_norm hq_ne_one).comp
        (tendsto_add_atTop_nat 1)
  have havg_w : Tendsto (avg fun n => w ^ n) atTop (nhds 0) := by
    simpa [avg, Function.comp_def] using
      (tendsto_cesaro_pow_of_norm_le_one_of_ne_one hw_norm.le hw_ne_one).comp
        (tendsto_add_atTop_nat 1)
  have havg_cw : Tendsto (avg fun n => (starRingEnd ℂ w) ^ n) atTop (nhds 0) := by
    simpa [avg, Function.comp_def] using
      (tendsto_cesaro_pow_of_norm_le_one_of_ne_one hcw_norm.le hcw_ne_one).comp
        (tendsto_add_atTop_nat 1)
  have havg_y_eq : ∀ N,
      avg (fun n => (y n : ℂ)) N =
        A * avg (fun n => (q : ℂ) ^ n) N +
          B * avg (fun n => w ^ n) N +
          (starRingEnd ℂ B) * avg (fun n => (starRingEnd ℂ w) ^ n) N := by
    intro N
    simp only [avg, hnormalized]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Complex.real_smul]
    ring
  have havg_y : Tendsto (avg fun n => (y n : ℂ)) atTop (nhds 0) := by
    rw [show avg (fun n => (y n : ℂ)) = fun N =>
      A * avg (fun n => (q : ℂ) ^ n) N +
        B * avg (fun n => w ^ n) N +
        (starRingEnd ℂ B) * avg (fun n => (starRingEnd ℂ w) ^ n) N by
      funext N
      exact havg_y_eq N]
    simpa using
      ((havg_q.const_mul A).add (havg_w.const_mul B)).add
        (havg_cw.const_mul (starRingEnd ℂ B))
  let mean : ℕ → ℝ := fun N =>
    ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ range (N + 1), y n
  have hmean_cast : ∀ N, (mean N : ℂ) = avg (fun n => (y n : ℂ)) N := by
    intro N
    simp [mean, avg, Complex.real_smul]
  have hmean : Tendsto mean atTop (nhds 0) := by
    have hre := (Complex.continuous_re.tendsto 0).comp havg_y
    convert hre using 1
    · funext N
      rw [Function.comp_apply, ← hmean_cast]
      simp
    · simp
  let weightedMean : ℕ → ℂ := fun N =>
    ((N + 1 : ℕ) : ℝ)⁻¹ •
      ∑ n ∈ range (N + 1), (y n : ℂ) * (starRingEnd ℂ w) ^ n
  have hweightedMean_zero : Tendsto weightedMean atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro N
      calc
        ‖weightedMean N‖ =
            ‖((N + 1 : ℕ) : ℝ)⁻¹‖ *
              ‖∑ n ∈ range (N + 1), (y n : ℂ) * (starRingEnd ℂ w) ^ n‖ := by
                simp only [weightedMean, norm_smul]
        _ ≤ ‖((N + 1 : ℕ) : ℝ)⁻¹‖ *
              ∑ n ∈ range (N + 1),
                ‖(y n : ℂ) * (starRingEnd ℂ w) ^ n‖ := by
                  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
        _ = ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ range (N + 1), y n := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
              congr 1
              apply Finset.sum_congr rfl
              intro n hn
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hy_nonneg n),
                norm_pow, hcw_norm, one_pow, mul_one]
        _ = mean N := rfl
    · exact hmean
  have hqcw_norm_lt : ‖(q : ℂ) * starRingEnd ℂ w‖ < 1 := by
    rw [norm_mul, hcw_norm, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hq_nonneg]
    exact hq_lt
  have hqcw_ne_one : (q : ℂ) * starRingEnd ℂ w ≠ 1 := by
    intro h
    have hnorm_eq := congrArg norm h
    rw [norm_one] at hnorm_eq
    exact (ne_of_lt hqcw_norm_lt) hnorm_eq
  have hcw_sq_norm : ‖(starRingEnd ℂ w) ^ 2‖ = 1 := by
    rw [norm_pow, hcw_norm, one_pow]
  have havg_qcw : Tendsto
      (avg fun n => ((q : ℂ) * starRingEnd ℂ w) ^ n) atTop (nhds 0) := by
    simpa [avg, Function.comp_def] using
      (tendsto_cesaro_pow_of_norm_le_one_of_ne_one hqcw_norm_lt.le
        hqcw_ne_one).comp (tendsto_add_atTop_nat 1)
  have havg_cw_sq : Tendsto
      (avg fun n => ((starRingEnd ℂ w) ^ 2) ^ n) atTop (nhds 0) := by
    simpa [avg, Function.comp_def] using
      (tendsto_cesaro_pow_of_norm_le_one_of_ne_one hcw_sq_norm.le
        hcw_sq_ne_one).comp (tendsto_add_atTop_nat 1)
  have hw_mul_cw : w * starRingEnd ℂ w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw_norm]
    norm_num
  have hweightedMean_eq : ∀ N,
      weightedMean N =
        A * avg (fun n => ((q : ℂ) * starRingEnd ℂ w) ^ n) N + B +
          (starRingEnd ℂ B) * avg (fun n => ((starRingEnd ℂ w) ^ 2) ^ n) N := by
    intro N
    have hterm : ∀ n,
        (y n : ℂ) * (starRingEnd ℂ w) ^ n =
          A * ((q : ℂ) * starRingEnd ℂ w) ^ n + B +
            (starRingEnd ℂ B) * ((starRingEnd ℂ w) ^ 2) ^ n := by
      intro n
      rw [hnormalized]
      simp only [add_mul, mul_assoc, ← mul_pow, hw_mul_cw, one_pow, mul_one,
        pow_two]
    simp only [weightedMean, avg]
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Complex.real_smul, Finset.sum_const, card_range, nsmul_eq_mul]
    have hcast : ((((N + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    have hnatcast : ((N + 1 : ℕ) : ℂ) = ((((N + 1 : ℕ) : ℝ) : ℂ)) := by
      norm_num
    rw [Complex.ofReal_inv]
    field_simp [hcast]
    rw [hnatcast]
  have hweightedMean_B : Tendsto weightedMean atTop (nhds B) := by
    rw [show weightedMean = fun N =>
      A * avg (fun n => ((q : ℂ) * starRingEnd ℂ w) ^ n) N + B +
        (starRingEnd ℂ B) * avg (fun n => ((starRingEnd ℂ w) ^ 2) ^ n) N by
      funext N
      exact hweightedMean_eq N]
    simpa using
      (((havg_qcw.const_mul A).add tendsto_const_nhds).add
        (havg_cw_sq.const_mul (starRingEnd ℂ B)))
  have hzero_eq_B : (0 : ℂ) = B :=
    tendsto_nhds_unique hweightedMean_zero hweightedMean_B
  exact hB hzero_eq_B.symm

end RealRooted
