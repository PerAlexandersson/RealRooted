module

public import RealRooted.TuranHurwitz.NormalizedLeading
public import RealRooted.TuranHurwitz.KernelLeading
public import RealRooted.TuranHurwitz.NormalizedTuran
import RealRooted.TuranHurwitz.InteriorStability
import RealRooted.TuranHurwitz.DiskNormLowerBound
import RealRooted.TuranHurwitz.TanhCoefficients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative nonvanishing before taking the exponential boundary limit

The exterior disk bound supplies a uniform positive value at `x = 1 - lambda`.
It avoids having to determine the boundary Turán polynomial's exact leading term.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- A normalized row has a quantitative exterior lower bound. -/
theorem normalized_norm_lower {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (m : ℕ) {u : ℂ} (hu : 1 < ‖u‖) :
    d ^ m * (‖u‖ - 1) ^ m ≤ ‖Polynomial.aeval u (normalized d h m)‖ := by
  have hs := normalized_splits hd hlo hhi m
  have hr := roots_map_real_norm_le_one hs (normalized_roots_mem_Icc hd hlo hhi m)
  have hbound := norm_leadingCoeff_mul_pow_le_norm_eval hr hu
  rw [natDegree_map, (normalized_natDegree_and_leadingCoeff_pos hd h m).1,
    Polynomial.eval_map_algebraMap, leadingCoeff_map_of_injective
      (algebraMap ℝ ℂ).injective, normalized_leadingCoeff hd] at hbound
  have hleader : ‖(algebraMap ℝ ℂ) (rising d m)‖ = rising d m := by
    change ‖(rising d m : ℂ)‖ = rising d m
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rising_pos hd m).le]
  rw [hleader] at hbound
  exact (mul_le_mul_of_nonneg_right (pow_le_rising hd m)
    (pow_nonneg (by linarith) m)).trans hbound

/-- The normalized Turán value has a lower bound uniform in all paired-root parameters. -/
theorem normalized_turan_norm_lower {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (m n : ℕ) {u : ℂ} (hu : 1 < ‖u‖) :
    (d ^ m * (‖u‖ - 1) ^ m) ^ 2 *
        (((2 * d) ^ n / ((2 * n).factorial : ℝ)) * (‖u‖ - 1) ^ n) ≤
      ‖Polynomial.aeval u (turan m n (normalized d h))‖ := by
  let eta := fun j => pairedParameter u (indexedRoots (normalized d h m) j)
  have heta : ∀ j, ‖eta j‖ ≤ 1 := normalized_pairedParameter_norm_le_one hd hlo hhi m hu
  obtain ⟨_, hdeg, hroots⟩ := diskCoefficient_degree_and_roots hd eta heta n m
  have hu2 : 1 < ‖u ^ 2‖ := by rw [norm_pow]; nlinarith [norm_nonneg u]
  have hg := norm_leadingCoeff_mul_pow_le_norm_eval hroots hu2
  rw [hdeg] at hg
  have hleader := pow_div_factorial_le_norm_leadingCoeff_diskCoefficient hd eta heta n m
  have hdelta : ‖u‖ - 1 ≤ ‖u ^ 2‖ - 1 := by rw [norm_pow]; nlinarith [norm_nonneg u]
  have hG : ((2 * d) ^ n / ((2 * n).factorial : ℝ)) * (‖u‖ - 1) ^ n ≤
      ‖(diskCoefficient d eta n m).eval (u ^ 2)‖ := by
    apply le_trans _ hg
    exact mul_le_mul hleader (pow_le_pow_left₀ (by linarith) hdelta n)
      (pow_nonneg (by linarith) _)
      (norm_nonneg (diskCoefficient d eta n m).leadingCoeff)
  have hR := normalized_norm_lower hd hlo hhi m hu
  have hk := congrArg norm (normalized_turan_kernel hd hlo hhi m n hu)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hk
  rw [hk]
  apply mul_le_mul (pow_le_pow_left₀ (by positivity) hR 2) hG
    (by positivity) (by positivity)

/-- A uniform positive lower bound for `tau = 0` as `b₁` decreases to zero. -/
theorem family_turan_norm_lower_of_tau_eq_zero {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb : 0 < c.b₁) (ht : c.tau = 0) (hb₂ : 0 < c.b₂) (m n : ℕ) :
    c.a₁ ^ n * c.b₂ ^ (2 * m + n) / ((2 * n).factorial : ℝ) ≤
      ‖Polynomial.aeval (1 - (c.lam : ℂ)) (turan m n (family c))‖ := by
  let s : ℝ := c.a₁ / 2
  let d : ℝ := (c.b₁ + c.b₂) / c.b₁
  let v : ℝ := 1 + c.b₁ / s
  have hs : 0 < s := by dsimp [s]; linarith
  have hv : 1 < v := by dsimp [v]; linarith [div_pos hb hs]
  have hd : 0 < d := by dsimp [d]; exact div_pos (add_pos hb hb₂) hb
  have hden : 0 < c.b₁ + c.tau * c.a₁ := by simpa [ht] using hb
  have hdeq : normalizedExponent c = d := by simp [normalizedExponent, ht, d]
  have hh := normalizedOffset_mem_Icc hc ha hden
  rw [hdeq] at hh
  have hnormv : ‖(v : ℂ)‖ = v := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hscale : normalizationScale c (1 - (c.lam : ℂ)) = (s : ℂ) := by
    simp [normalizationScale, ht, s]
  have harg : normalizationArgument c (1 - (c.lam : ℂ)) = (v : ℂ) := by
    rw [normalizationArgument, hscale]
    simp only [ht, Complex.ofReal_zero, mul_zero, add_zero, sub_add_cancel]
    dsimp [v, s]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
  have hscaleNe : normalizationScale c (1 - (c.lam : ℂ)) ≠ 0 := by
    rw [hscale]
    exact Complex.ofReal_ne_zero.mpr hs.ne'
  rw [aeval_family_turan_normalization c ha.ne' hden.ne' _ hscaleNe,
    hscale, harg, hdeq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs]
  have hbase := normalized_turan_norm_lower hd hh.1 hh.2 m n
    (u := (v : ℂ)) (by rw [hnormv]; exact hv)
  rw [hnormv] at hbase
  have hprod : d * (v - 1) = (c.b₁ + c.b₂) / s := by
    dsimp [d, v]
    field_simp
    ring
  have hsmall : c.b₂ / s ≤ d * (v - 1) := by rw [hprod]; gcongr; linarith
  have hR : (c.b₂ / s) ^ m ≤ d ^ m * (v - 1) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (div_nonneg hb₂.le hs.le) hsmall m
  have hG : (2 * c.b₂ / s) ^ n ≤ (2 * d) ^ n * (v - 1) ^ n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    convert mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring
  have hfac : 0 < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hlower : ((c.b₂ / s) ^ m) ^ 2 *
      ((2 * c.b₂ / s) ^ n / ((2 * n).factorial : ℝ)) ≤
      ‖Polynomial.aeval (v : ℂ)
        (turan m n (normalized d (normalizedOffset c)))‖ := by
    apply le_trans _ hbase
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) hR 2)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        div_le_div_of_nonneg_right hG hfac.le
    · positivity
    · positivity
  apply le_trans _ (mul_le_mul_of_nonneg_left hlower (pow_nonneg hs.le _))
  apply le_of_eq
  have hidentity : s ^ (2 * m + 2 * n) *
      (((c.b₂ / s) ^ m) ^ 2 * ((2 * c.b₂ / s) ^ n / ((2 * n).factorial : ℝ))) =
      c.a₁ ^ n * c.b₂ ^ (2 * m + n) / ((2 * n).factorial : ℝ) := by
    dsimp [s]
    simp only [div_pow, mul_pow, pow_add, pow_mul']
    field_simp [ha.ne', hfac.ne']
  exact hidentity.symm

end RealRooted.TuranHurwitz
