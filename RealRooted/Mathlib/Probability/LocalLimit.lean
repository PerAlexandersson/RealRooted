/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.CDF
public import RealRooted.Mathlib.Probability.CoeffDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Bender's local limit theorem for polynomial coefficients

Let `P n` be real polynomials with nonnegative, log-concave coefficients and no internal zeros,
whose coefficient distributions (see `RealRooted.Mathlib.Probability.CoeffDistribution`) have
variances tending to infinity and, after standardization, converge weakly to the standard Gaussian.
Then the coefficients satisfy the Gaussian local limit theorem uniformly in `k`:
`σₙ * (P n).coeff k / (P n).eval 1 - φ ((k - μₙ) / σₙ)` tends to zero, where `μₙ` and
`σₙ` are the mean and standard deviation of the coefficient distribution and `φ` is the standard
Gaussian density. For real-rooted `P n`, the weak convergence hypothesis is Harper's central limit
theorem.

The proof is organized as follows. We first collect elementary facts about the Gaussian density
and distribution function, and show that a log-concave sequence without internal zeros is
quasi-concave. We then prove deterministic window estimates for a sequence on `ℤ` whose window
sums are uniformly close to Gaussian integrals, which give an abstract local limit theorem.
Pólya's theorem upgrades pointwise convergence of the distribution functions to uniform
convergence, and the portmanteau theorem turns weak convergence into pointwise convergence of the
standardized distribution functions at every point.

## Main statements

* `Polynomial.tendsto_localLimit_of_logConcave`: the local limit theorem described above (Bender
  1973, Theorem 2). All other declarations in the file are private.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Polynomial

noncomputable section

namespace Polynomial

/-! ## Auxiliary development

The proof of the local limit theorem is organized as follows.

* Elementary facts about the standard Gaussian density `φ` and distribution function `Phi`.
* Discrete concavity: a log-concave sequence without internal zeros satisfies the chord
  inequality for `log`, hence is quasi-concave (`min (b i) (b j) ≤ b k` for `i ≤ k ≤ j`).
* Deterministic window estimates (`lower_det`, `upper_det`, `desc_det`, `rtail_det`) for a
  sequence `b : ℤ → ℝ` whose window sums are uniformly close to Gaussian integrals
  (`WinApprox`).
* The abstract local limit theorem `LLTData.llt`.
* The bridge from polynomials (`llt_of_poly`), including Pólya's uniformity theorem.
-/

section Aux

/-- Standard Gaussian density (local notation). -/
local notation "φ" => gaussianPDFReal 0 1


private lemma gpdf_eq (t : ℝ) : φ t = (√(2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
  simp [gaussianPDFReal_def]

private lemma gpdf_pos (t : ℝ) : 0 < φ t := gaussianPDFReal_pos _ _ _ one_ne_zero

private lemma sqrt_two_pi_ge_two : (2 : ℝ) ≤ √(2 * Real.pi) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [Real.pi_gt_three]

private lemma gpdf_le_half (t : ℝ) : φ t ≤ 1 / 2 := by
  rw [gpdf_eq]
  have h1 : Real.exp (-t ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  have h2 : (√(2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) sqrt_two_pi_ge_two
  nlinarith [Real.exp_pos (-t ^ 2 / 2)]

private lemma gpdf_neg (t : ℝ) : φ (-t) = φ t := by
  rw [gpdf_eq, gpdf_eq]; ring_nf

private lemma gpdf_le_of_sq_le {s t : ℝ} (h : s ^ 2 ≤ t ^ 2) : φ t ≤ φ s := by
  rw [gpdf_eq, gpdf_eq]; gcongr

private lemma gpdf_lt_of_sq_lt {s t : ℝ} (h : s ^ 2 < t ^ 2) : φ t < φ s := by
  rw [gpdf_eq, gpdf_eq]
  have : 0 < (√(2 * Real.pi))⁻¹ := by positivity
  gcongr

private lemma gpdf_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : φ t ≤ φ s :=
  gpdf_le_of_sq_le (by nlinarith)

private lemma gpdf_strictAnti {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : φ t < φ s :=
  gpdf_lt_of_sq_lt (by nlinarith)

private lemma abs_mul_exp_neg_sq_le (t : ℝ) : |t| * Real.exp (-t ^ 2 / 2) ≤ 1 := by
  have h := Real.add_one_le_exp (t ^ 2 / 2)
  have hpos := Real.exp_pos (t ^ 2 / 2)
  have e : Real.exp (-t ^ 2 / 2) = (Real.exp (t ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e, ← div_eq_mul_inv, div_le_one hpos]
  have : |t| ≤ t ^ 2 / 2 + 1 := by
    have := sq_abs t
    nlinarith [sq_nonneg (|t| - 1), abs_nonneg t]
  linarith

private lemma gpdf_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t => φ t) ((√(2 * Real.pi))⁻¹ * (Real.exp (-t ^ 2 / 2) * (-t))) t := by
  have : (fun t => φ t) = fun t => (√(2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
    funext s; exact gpdf_eq s
  rw [this]
  apply HasDerivAt.const_mul
  have h2 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-t) t := by
    have := ((hasDerivAt_pow 2 t).neg).div_const 2
    convert this using 1; ring
  exact h2.exp

private lemma gpdf_lip (s t : ℝ) : |φ s - φ t| ≤ |s - t| := by
  have key := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := fun t => φ t) (C := 1) (fun x _ => (gpdf_hasDerivAt x).differentiableAt)
    (fun x _ => by
      rw [(gpdf_hasDerivAt x).deriv, Real.norm_eq_abs]
      have h1 := abs_mul_exp_neg_sq_le x
      have h2 : (√(2 * Real.pi))⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) sqrt_two_pi_ge_two
      have h3 : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_pos (Real.exp_pos _), abs_neg]
      nlinarith [abs_nonneg x, Real.exp_pos (-x ^ 2 / 2)])
    (Set.mem_univ t) (Set.mem_univ s)
  simpa [Real.norm_eq_abs] using key

private lemma gpdf_intervalIntegrable (u v : ℝ) : IntervalIntegrable (fun t => φ t) volume u v :=
  (continuous_iff_continuousAt.2 fun t => (gpdf_hasDerivAt t).continuousAt).intervalIntegrable u v

private lemma gpdf_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ, 0 ≤ y ∧ ∀ t, y ≤ t → φ t < ε := by
  refine ⟨max 2 (1 / ε), by positivity, fun t ht => ?_⟩
  have h2 : 2 ≤ t := le_trans (le_max_left _ _) ht
  have hε' : 1 / ε ≤ t := le_trans (le_max_right _ _) ht
  rw [gpdf_eq]
  have he : Real.exp (-t ^ 2 / 2) * (1 + t ^ 2 / 2) ≤ 1 := by
    have h := Real.add_one_le_exp (t ^ 2 / 2)
    have e : Real.exp (-t ^ 2 / 2) * Real.exp (t ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    nlinarith [Real.exp_pos (-t ^ 2 / 2)]
  have h4 : (√(2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) sqrt_two_pi_ge_two
  have h3 : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  have ht1 : 1 < ε * (1 + t ^ 2 / 2) := by
    have : 1 ≤ ε * t := by rwa [div_le_iff₀ hε, mul_comm] at hε'
    nlinarith
  have hE : Real.exp (-t ^ 2 / 2) < ε := by
    exact lt_of_not_ge fun hc => by nlinarith
  calc (√(2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) ≤ 1 / 2 * Real.exp (-t ^ 2 / 2) := by
        gcongr
    _ < ε := by nlinarith [Real.exp_pos (-t ^ 2 / 2)]

/-! ### Integral estimates -/

private lemma int_gpdf_nonneg {u v : ℝ} (h : u ≤ v) : 0 ≤ ∫ t in u..v, φ t :=
  intervalIntegral.integral_nonneg h fun t _ => (gpdf_pos t).le

private lemma int_gpdf_le_half {u v : ℝ} (h : u ≤ v) : ∫ t in u..v, φ t ≤ (v - u) / 2 := by
  have := intervalIntegral.integral_mono_on h (gpdf_intervalIntegrable u v)
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) fun t _ => gpdf_le_half t
  simp at this; linarith

private lemma int_gpdf_upper {u v s w : ℝ} (h : u ≤ v)
    (hw : ∀ t ∈ Set.Icc u v, |t - s| ≤ w) :
    ∫ t in u..v, φ t ≤ (v - u) * (φ s + w) := by
  have := intervalIntegral.integral_mono_on h (gpdf_intervalIntegrable u v)
    (intervalIntegrable_const (c := φ s + w)) fun t ht => by
      linarith [gpdf_lip t s, hw t ht, le_abs_self (φ t - φ s)]
  simp at this; linarith

private lemma int_gpdf_lower {u v s w : ℝ} (h : u ≤ v)
    (hw : ∀ t ∈ Set.Icc u v, |t - s| ≤ w) :
    (v - u) * (φ s - w) ≤ ∫ t in u..v, φ t := by
  have := intervalIntegral.integral_mono_on h
    (intervalIntegrable_const (c := φ s - w)) (gpdf_intervalIntegrable u v) fun t ht => by
      linarith [gpdf_lip t s, hw t ht, neg_abs_le (φ t - φ s)]
  simp at this; linarith

private lemma int_gpdf_upper_anti {u v : ℝ} (hu : 0 ≤ u) (h : u ≤ v) :
    ∫ t in u..v, φ t ≤ (v - u) * φ u := by
  have := intervalIntegral.integral_mono_on h (gpdf_intervalIntegrable u v)
    (intervalIntegrable_const (c := φ u)) fun t ht => gpdf_antitone hu ht.1
  simp at this; linarith

private lemma int_gpdf_lower_anti {u v : ℝ} (hu : 0 ≤ u) (h : u ≤ v) :
    (v - u) * φ v ≤ ∫ t in u..v, φ t := by
  have := intervalIntegral.integral_mono_on h
    (intervalIntegrable_const (c := φ v)) (gpdf_intervalIntegrable u v)
    fun t ht => gpdf_antitone (hu.trans ht.1) ht.2
  simp at this; linarith

private lemma int_gpdf_neg (u v : ℝ) : ∫ t in -v..-u, φ t = ∫ t in u..v, φ t := by
  rw [← intervalIntegral.integral_comp_neg]; simp only [gpdf_neg]

/-! ### The Gaussian distribution function -/

/-- The standard Gaussian distribution function. -/
private def Phi (x : ℝ) : ℝ := ∫ t in Set.Iic x, φ t

private lemma Phi_sub (u v : ℝ) : Phi v - Phi u = ∫ t in u..v, φ t :=
  intervalIntegral.integral_Iic_sub_Iic (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn

private lemma Phi_eq_cdf (x : ℝ) : Phi x = cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal]
  · rfl
  · exact setIntegral_nonneg measurableSet_Iic fun t _ => (gpdf_pos t).le

private lemma Phi_tendsto_atTop : Tendsto Phi atTop (𝓝 1) := by
  rw [show Phi = cdf (gaussianReal 0 1) by ext x; exact Phi_eq_cdf x]
  exact tendsto_cdf_atTop _

private lemma Phi_tendsto_atBot : Tendsto Phi atBot (𝓝 0) := by
  rw [show Phi = cdf (gaussianReal 0 1) by ext x; exact Phi_eq_cdf x]
  exact tendsto_cdf_atBot _

private lemma Phi_mono {u v : ℝ} (h : u ≤ v) : Phi u ≤ Phi v := by
  linarith [Phi_sub u v, int_gpdf_nonneg h]

/-! ### Discrete concavity -/

private lemma concave_seq_diff_anti (u : ℕ → ℝ) (L : ℕ)
    (h : ∀ t, t + 2 ≤ L → u t + u (t + 2) ≤ 2 * u (t + 1)) :
    ∀ i m, i + m + 1 ≤ L → u (i + m + 1) - u (i + m) ≤ u (i + 1) - u i := by
  intro i m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by lia)
    have h2 := h (i + m) (by lia)
    have e1 : i + m + 2 = i + (m + 1) + 1 := by ring
    have e2 : i + m + 1 = i + (m + 1) := by ring
    rw [e1, e2] at h2
    rw [e2] at h1
    linarith

private lemma concave_seq_chord (u : ℕ → ℝ) (L : ℕ)
    (h : ∀ t, t + 2 ≤ L → u t + u (t + 2) ≤ 2 * u (t + 1)) (i : ℕ) (hi : i ≤ L) :
    ((L : ℝ) - i) * u 0 + i * u L ≤ L * u i := by
  have hanti := concave_seq_diff_anti u L h
  rcases eq_or_lt_of_le hi with rfl | hlt
  · simp
  -- (a) lower bound on the increment from 0 to i
  have ha : ∀ i, i + 1 ≤ L → (i : ℝ) * (u (i + 1) - u i) ≤ u i - u 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by lia)
      have h2 := h i (by lia)
      push_cast
      have h3 : u (i + 1 + 1) - u (i + 1) ≤ u (i + 1) - u i := by
        rw [show i + 1 + 1 = i + 2 by ring]; linarith
      have hi0 : (0 : ℝ) ≤ i := by positivity
      nlinarith
  -- (b) upper bound on the increment from i to L
  have hb : ∀ m, i + m + 1 ≤ L →
      u (i + m + 1) - u i ≤ ((m : ℝ) + 1) * (u (i + 1) - u i) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by lia)
      have h2 := hanti i (m + 1) hm
      rw [show i + (m + 1) = i + m + 1 by ring] at h2 ⊢
      push_cast; linarith
  have h1 := ha i (by lia)
  obtain ⟨m, rfl⟩ : ∃ m, L = i + m + 1 := ⟨L - i - 1, by lia⟩
  have h2 := hb m le_rfl
  push_cast at *
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-! ### Log-concave sequences on `ℤ` -/

section LogConcave

variable {b : ℤ → ℝ}

private lemma pos_between (hnn : ∀ j, 0 ≤ b j)
    (hnz : ∀ i j k, i < j → j < k → b i ≠ 0 → b k ≠ 0 → b j ≠ 0)
    {p q j : ℤ} (hp : 0 < b p) (hq : 0 < b q) (hpj : p ≤ j) (hjq : j ≤ q) : 0 < b j := by
  grind

private lemma log_chord (hnn : ∀ j, 0 ≤ b j) (hlc : ∀ j, b (j - 1) * b (j + 1) ≤ b j ^ 2)
    (hnz : ∀ i j k, i < j → j < k → b i ≠ 0 → b k ≠ 0 → b j ≠ 0)
    {p q : ℤ} (hp : 0 < b p) (hq : 0 < b q) (hpq : p ≤ q) (i : ℕ) (hi : (i : ℤ) ≤ q - p) :
    (((q - p : ℤ) : ℝ) - i) * Real.log (b p) + i * Real.log (b q) ≤
      ((q - p : ℤ) : ℝ) * Real.log (b (p + i)) := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, q - p = L := ⟨(q - p).toNat, by lia⟩
  have hq' : q = p + L := by lia
  rw [hL] at hi ⊢
  have key := concave_seq_chord (fun t => Real.log (b (p + t))) L (fun t ht => by
    have hpos : ∀ s : ℕ, s ≤ L → 0 < b (p + s) := fun s hs =>
      pos_between hnn hnz hp hq (by lia) (by lia)
    have h0 := hpos t (by lia)
    have h1 := hpos (t + 1) (by lia)
    have h2 := hpos (t + 2) (by lia)
    have hl := hlc (p + (t + 1 : ℕ))
    have e1 : p + ((t + 1 : ℕ) : ℤ) - 1 = p + (t : ℕ) := by push_cast; ring
    have e2 : p + ((t + 1 : ℕ) : ℤ) + 1 = p + ((t + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at hl
    rw [← Real.log_mul h0.ne' h2.ne', two_mul, ← Real.log_mul h1.ne' h1.ne']
    exact Real.log_le_log (mul_pos h0 h2) (by nlinarith)) i (by exact_mod_cast hi)
  simp only [Nat.cast_zero, add_zero] at key
  rw [hq']; push_cast; exact key

private lemma quasi_concave (hnn : ∀ j, 0 ≤ b j)
    (hlc : ∀ j, b (j - 1) * b (j + 1) ≤ b j ^ 2)
    (hnz : ∀ i j k, i < j → j < k → b i ≠ 0 → b k ≠ 0 → b j ≠ 0)
    {i k j : ℤ} (hik : i ≤ k) (hkj : k ≤ j) : min (b i) (b j) ≤ b k := by
  rcases eq_or_lt_of_le (hnn i) with h | hi
  · rw [← h]; exact (min_le_left _ _).trans (hnn k)
  rcases eq_or_lt_of_le (hnn j) with h | hj
  · rw [← h]; exact (min_le_right _ _).trans (hnn k)
  have hk := pos_between hnn hnz hi hj hik hkj
  obtain ⟨t, ht⟩ : ∃ t : ℕ, k = i + t := ⟨(k - i).toNat, by lia⟩
  have key := log_chord hnn hlc hnz hi hj (hik.trans hkj) t (by lia)
  rw [← ht] at key
  rcases eq_or_lt_of_le (hik.trans hkj) with hij | hij
  · subst hij
    have : k = i := le_antisymm hkj hik
    subst this; exact min_le_left _ _
  have hD : (0 : ℝ) < ((j - i : ℤ) : ℝ) := by exact_mod_cast (sub_pos.2 hij)
  have ht0 : (t : ℝ) ≤ ((j - i : ℤ) : ℝ) := by exact_mod_cast (by lia : (t : ℤ) ≤ j - i)
  have ht1 : (0 : ℝ) ≤ t := by positivity
  rw [← Real.log_le_log_iff (lt_min hi hj) hk]
  rcases le_total (b i) (b j) with h | h
  · rw [min_eq_left h]
    have := Real.log_le_log hi h
    by_contra hc; push Not at hc
    have : ((j - i : ℤ) : ℝ) * Real.log (b k) < ((j - i : ℤ) : ℝ) * Real.log (b i) :=
      mul_lt_mul_of_pos_left hc hD
    nlinarith
  · rw [min_eq_right h]
    have := Real.log_le_log hj h
    by_contra hc; push Not at hc
    have : ((j - i : ℤ) : ℝ) * Real.log (b k) < ((j - i : ℤ) : ℝ) * Real.log (b j) :=
      mul_lt_mul_of_pos_left hc hD
    nlinarith

private lemma mono_left_of_lt (hQ : ∀ i k j, i ≤ k → k ≤ j → min (b i) (b j) ≤ b k)
    {j : ℤ} (hj : b j < b (j + 1)) {i i' : ℤ} (hii' : i ≤ i') (hi' : i' ≤ j + 1) :
    b i ≤ b i' := by
  have hi_le : b i ≤ b (j + 1) := by
    rcases eq_or_lt_of_le (hii'.trans hi') with h | h
    · rw [h]
    · have := hQ i j (j + 1) (by lia) (by lia)
      rcases min_choice (b i) (b (j + 1)) with hm | hm <;> rw [hm] at this <;> linarith
  have := hQ i i' (j + 1) hii' hi'
  rwa [min_eq_left hi_le] at this

/-- The key interpolation estimate: with a positive lower bound `c` at distance `K * M`,
a value `A = σ b k ≥ c` forces `(σ b j) ^ K ≥ A ^ (K - 1) * c` on the next `M` sites. -/
private lemma pow_interp (hnn : ∀ j, 0 ≤ b j) (hlc : ∀ j, b (j - 1) * b (j + 1) ≤ b j ^ 2)
    (hnz : ∀ i j k, i < j → j < k → b i ≠ 0 → b k ≠ 0 → b j ≠ 0)
    {σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) {K M : ℕ} (hK : 1 ≤ K) (hM : 1 ≤ M) {k : ℤ}
    (hA : c ≤ σ * b k) (hB : c ≤ σ * b (k + (K * M : ℕ))) (i : ℕ) (hi : i ≤ M) :
    (σ * b k) ^ (K - 1) * c ≤ (σ * b (k + i)) ^ K := by
  have hk : 0 < b k := by
    by_contra h; push Not at h; nlinarith [hnn k]
  have hq : 0 < b (k + (K * M : ℕ)) := by
    by_contra h; push Not at h; nlinarith [hnn (k + (K * M : ℕ))]
  have hiN : i ≤ K * M := hi.trans (by nlinarith)
  have key := log_chord hnn hlc hnz hk hq (by lia) i (by push_cast; lia)
  have hj : 0 < b (k + i) := pos_between hnn hnz hk hq (by lia) (by push_cast; lia)
  have e : ((k + ((K * M : ℕ) : ℤ) - k : ℤ) : ℝ) = (K : ℝ) * M := by push_cast; ring
  rw [e] at key
  set la := Real.log (σ * b k)
  set lb := Real.log (σ * b (k + (K * M : ℕ)))
  set lj := Real.log (σ * b (k + i))
  have hla : la = Real.log σ + Real.log (b k) := Real.log_mul hσ.ne' hk.ne'
  have hlb : lb = Real.log σ + Real.log (b (k + (K * M : ℕ))) := Real.log_mul hσ.ne' hq.ne'
  have hlj : lj = Real.log σ + Real.log (b (k + i)) := Real.log_mul hσ.ne' hj.ne'
  have hca : Real.log c ≤ la := Real.log_le_log hc hA
  have hcb : Real.log c ≤ lb := Real.log_le_log hc hB
  have hiM : (i : ℝ) ≤ M := by exact_mod_cast hi
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : ((K : ℝ) * M - i) * la + i * lb ≤ (K : ℝ) * M * lj := by
    rw [hla, hlb, hlj]; nlinarith
  have h2 : (M : ℝ) * (((K : ℝ) - 1) * la + Real.log c) ≤ M * (K * lj) := by
    have : (0 : ℝ) ≤ (M - i) * (la - Real.log c) := mul_nonneg (by linarith) (by linarith)
    have : (i : ℝ) * Real.log c ≤ i * lb := mul_le_mul_of_nonneg_left hcb (by positivity)
    nlinarith
  have h3 : ((K : ℝ) - 1) * la + Real.log c ≤ K * lj := le_of_mul_le_mul_left h2 (by linarith)
  have hApos : 0 < σ * b k := mul_pos hσ hk
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity) hc.ne',
    Real.log_pow, Real.log_pow, Nat.cast_sub hK]
  push_cast; exact h3

end LogConcave

/-- Standardized lattice point `(j - μ) / σ`. -/
private def xs (μ σ : ℝ) (j : ℤ) : ℝ := ((j : ℝ) - μ) / σ

private lemma xs_add (μ σ : ℝ) (hσ : 0 < σ) (j m : ℤ) :
    xs μ σ (j + m) = xs μ σ j + m / σ := by
  unfold xs; push_cast; field_simp; ring

private lemma xs_sub (μ σ : ℝ) (hσ : 0 < σ) (j m : ℤ) :
    xs μ σ (j - m) = xs μ σ j - m / σ := by
  unfold xs; push_cast; field_simp; ring

private lemma xs_mono (μ σ : ℝ) (hσ : 0 < σ) {i j : ℤ} (h : i ≤ j) :
    xs μ σ i ≤ xs μ σ j := by
  unfold xs; gcongr

/-- Uniform approximation of window sums by Gaussian integrals, with error `η`. -/
private def WinApprox (b : ℤ → ℝ) (μ σ η : ℝ) : Prop :=
  ∀ p q : ℤ, p ≤ q →
    |∑ j ∈ Finset.Icc p q, b j - ∫ t in xs μ σ p..xs μ σ q, φ t| ≤ η

private lemma WinApprox.le {b : ℤ → ℝ} {μ σ η : ℝ} (h : WinApprox b μ σ η)
    {p q : ℤ} (hpq : p ≤ q) :
    ∑ j ∈ Finset.Icc p q, b j ≤ (∫ t in xs μ σ p..xs μ σ q, φ t) + η := by
  have := h p q hpq; have := le_abs_self (∑ j ∈ Finset.Icc p q, b j -
    ∫ t in xs μ σ p..xs μ σ q, φ t); linarith

private lemma WinApprox.ge {b : ℤ → ℝ} {μ σ η : ℝ} (h : WinApprox b μ σ η)
    {p q : ℤ} (hpq : p ≤ q) :
    (∫ t in xs μ σ p..xs μ σ q, φ t) - η ≤ ∑ j ∈ Finset.Icc p q, b j := by
  have := h p q hpq; have := neg_abs_le (∑ j ∈ Finset.Icc p q, b j -
    ∫ t in xs μ σ p..xs μ σ q, φ t); linarith

private lemma WinApprox.nonneg {b : ℤ → ℝ} {μ σ η : ℝ}
    (h : WinApprox b μ σ η) : 0 ≤ η :=
  (abs_nonneg _).trans (h 0 0 le_rfl)

private lemma card_Icc_sub (k : ℤ) (L : ℕ) : ((Finset.Icc (k - L) k).card : ℝ) = L + 1 := by
  rw [Int.card_Icc]
  have : (k + 1 - (k - L)).toNat = L + 1 := by lia
  rw [this]; push_cast; ring

private lemma card_Icc_add (k : ℤ) (L : ℕ) : ((Finset.Icc k (k + L)).card : ℝ) = L + 1 := by
  rw [Int.card_Icc]
  have : (k + L + 1 - k).toNat = L + 1 := by lia
  rw [this]; push_cast; ring

private lemma sum_Icc_shift (f : ℤ → ℝ) (p q c : ℤ) :
    ∑ i ∈ Finset.Icc p q, f (i + c) = ∑ i ∈ Finset.Icc (p + c) (q + c), f i := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-! ### Lower bound -/

private lemma lower_det {b : ℤ → ℝ} {μ σ η : ℝ}
    (hQ : ∀ i k j, i ≤ k → k ≤ j → min (b i) (b j) ≤ b k) (hσ : 0 < σ)
    (L : ℕ) (hH : WinApprox b μ σ η) (k : ℤ) :
    φ (xs μ σ k) - 1 / (L + 1) - L / σ - η * σ / (L + 1) ≤ σ * b k := by
  have hL1 : (0 : ℝ) < L + 1 := by positivity
  set X := φ (xs μ σ k) - L / σ
  have hX : X ≤ 1 := by
    have := gpdf_le_half (xs μ σ k); have : (0 : ℝ) ≤ L / σ := by positivity
    linarith
  -- integral lower bounds
  have hxl : xs μ σ (k - L) = xs μ σ k - L / σ := by
    rw [xs_sub _ _ hσ]; norm_cast
  have hxr : xs μ σ (k + L) = xs μ σ k + L / σ := by
    rw [xs_add _ _ hσ]; norm_cast
  have hLσ : (0 : ℝ) ≤ L / σ := by positivity
  have Il : L / σ * X ≤ ∫ t in xs μ σ (k - L)..xs μ σ k, φ t := by
    have := int_gpdf_lower (u := xs μ σ (k - L)) (v := xs μ σ k) (s := xs μ σ k) (w := L / σ)
      (by rw [hxl]; linarith) (fun t ht => by
        rw [hxl] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    simp only [hxl] at this ⊢; convert this using 1; ring
  have Ir : L / σ * X ≤ ∫ t in xs μ σ k..xs μ σ (k + L), φ t := by
    have := int_gpdf_lower (u := xs μ σ k) (v := xs μ σ (k + L)) (s := xs μ σ k) (w := L / σ)
      (by rw [hxr]; linarith) (fun t ht => by
        rw [hxr] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    simp only [hxr] at this ⊢; convert this using 1; ring
  have Sl := hH.ge (p := k - L) (q := k) (by lia)
  have Sr := hH.ge (p := k) (q := k + L) (by lia)
  -- the quasi-concavity step
  have hmin : min (∑ j ∈ Finset.Icc (k - L) k, b j) (∑ j ∈ Finset.Icc k (k + L), b j) ≤
      (L + 1) * b k := by
    by_contra hc
    push Not at hc
    have h1 : ∑ j ∈ Finset.Icc (k - L) k, b k < ∑ j ∈ Finset.Icc (k - L) k, b j := by
      rw [Finset.sum_const, nsmul_eq_mul, card_Icc_sub]; exact (lt_min_iff.1 hc).1
    have h2 : ∑ j ∈ Finset.Icc k (k + L), b k < ∑ j ∈ Finset.Icc k (k + L), b j := by
      rw [Finset.sum_const, nsmul_eq_mul, card_Icc_add]; exact (lt_min_iff.1 hc).2
    obtain ⟨i, hi, hbi⟩ := Finset.exists_lt_of_sum_lt h1
    obtain ⟨j, hj, hbj⟩ := Finset.exists_lt_of_sum_lt h2
    rw [Finset.mem_Icc] at hi hj
    have := hQ i k j hi.2 hj.1
    rcases min_choice (b i) (b j) with h | h <;> rw [h] at this <;> linarith
  have hbound : L / σ * X - η ≤ (L + 1) * b k := by
    rcases min_choice (∑ j ∈ Finset.Icc (k - L) k, b j) (∑ j ∈ Finset.Icc k (k + L), b j)
      with h | h <;> rw [h] at hmin <;> linarith
  -- arithmetic
  have key : (L / (L + 1)) * X - η * σ / (L + 1) ≤ σ * b k := by
    have := mul_le_mul_of_nonneg_left hbound (le_of_lt (div_pos hσ hL1))
    have e1 : σ / (L + 1) * (L / σ * X - η) = (L / (L + 1)) * X - η * σ / (L + 1) := by
      field_simp
    have e2 : σ / (L + 1) * ((L + 1) * b k) = σ * b k := by field_simp
    linarith
  have hX2 : X - 1 / (L + 1) ≤ (L / (L + 1)) * X := by
    have : X - (L / (L + 1)) * X = X / (L + 1) := by field_simp; ring
    have : X / (L + 1) ≤ 1 / (L + 1) := div_le_div_of_nonneg_right hX hL1.le
    linarith
  linarith

/-! ### Upper bound in the central region -/

private lemma upper_det {b : ℤ → ℝ} {μ σ η c ε : ℝ} (hnn : ∀ j, 0 ≤ b j)
    (hlc : ∀ j, b (j - 1) * b (j + 1) ≤ b j ^ 2)
    (hnz : ∀ i j k, i < j → j < k → b i ≠ 0 → b k ≠ 0 → b j ≠ 0)
    (hσ : 0 < σ) (hH : WinApprox b μ σ η) {k : ℤ} (hc : 0 < c) (hc1 : c ≤ φ (xs μ σ k))
    {K M : ℕ} (hK : 1 ≤ K) (hM : 1 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : c ≤ σ * b (k + (K * M : ℕ)))
    (hKbig : 1 < (1 + ((K : ℝ) - 1) * (ε / 2)) * c)
    (hsmall : M / σ + η * σ / (M + 1) ≤ ε / 2) :
    σ * b k < φ (xs μ σ k) + ε := by
  by_contra hcon
  push Not at hcon
  set A := σ * b k
  have hA : c ≤ A := by linarith
  have hpow := pow_interp hnn hlc hnz hσ hc hK hM hA hB
  -- the window sum
  have hS := hH.le (p := k) (q := k + M) (by lia)
  have hxr : xs μ σ (k + M) = xs μ σ k + M / σ := by
    rw [xs_add _ _ hσ]; norm_cast
  have hMσ : (0 : ℝ) ≤ M / σ := by positivity
  have hI : ∫ t in xs μ σ k..xs μ σ (k + M), φ t ≤
      M / σ * (φ (xs μ σ k) + M / σ) := by
    have := int_gpdf_upper (u := xs μ σ k) (v := xs μ σ (k + M))
      (s := xs μ σ k) (w := M / σ)
      (by rw [hxr]; linarith) (fun t ht => by
        rw [hxr] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    simp only [hxr] at this ⊢; convert this using 1; ring
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  obtain ⟨j, hj, hbj⟩ : ∃ j ∈ Finset.Icc k (k + M),
      b j ≤ (∑ j ∈ Finset.Icc k (k + M), b j) / (M + 1) := by
    by_contra hc'
    push Not at hc'
    have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_Icc.2 (by lia)) hc'
    rw [Finset.sum_const, nsmul_eq_mul, card_Icc_add] at this
    field_simp at this
    linarith
  rw [Finset.mem_Icc] at hj
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = k + i := ⟨(j - k).toNat, by lia⟩
  have hi : i ≤ M := by lia
  set m := σ * b (k + i)
  have hmpow : A ^ (K - 1) * c ≤ m ^ K := hpow i hi
  have hm0 : 0 ≤ m := mul_nonneg hσ.le (hnn _)
  have hApos : 0 < A := lt_of_lt_of_le hc hA
  have hmpos : 0 < m := by
    rcases eq_or_lt_of_le hm0 with hm | hm
    · rw [← hm, zero_pow (by lia)] at hmpow
      have : 0 < A ^ (K - 1) * c := by positivity
      linarith
    · exact hm
  -- `m ≤ φ + ε / 2`
  have hm_le : m ≤ φ (xs μ σ k) + ε / 2 := by
    have h1 : m ≤ σ * ((M / σ * (φ (xs μ σ k) + M / σ) + η) / (M + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hσ.le
      refine hbj.trans ?_
      gcongr
      linarith
    have h2 : σ * ((M / σ * (φ (xs μ σ k) + M / σ) + η) / (M + 1)) =
        (M / (M + 1)) * (φ (xs μ σ k) + M / σ) + η * σ / (M + 1) := by
      field_simp
    have h3 : (M / (M + 1)) * (φ (xs μ σ k) + M / σ) ≤ φ (xs μ σ k) + M / σ := by
      have : (M : ℝ) / (M + 1) ≤ 1 := by rw [div_le_one hM1]; linarith
      have : 0 ≤ φ (xs μ σ k) + M / σ := by linarith [gpdf_pos (xs μ σ k)]
      nlinarith
    linarith
  have hm1 : m ≤ 1 := by linarith [gpdf_le_half (xs μ σ k)]
  have hAm : m * (1 + ε / 2) ≤ A := by nlinarith
  have hbern : 1 + ((K - 1 : ℕ) : ℝ) * (ε / 2) ≤ (1 + ε / 2) ^ (K - 1) :=
    one_add_mul_le_pow (by linarith) _
  have hpowA : (m * (1 + ε / 2)) ^ (K - 1) ≤ A ^ (K - 1) :=
    pow_le_pow_left₀ (by positivity) hAm _
  rw [mul_pow] at hpowA
  have hmK : m ^ K ≤ m ^ (K - 1) := by
    have : m ^ K = m ^ (K - 1) * m := by rw [← pow_succ]; congr 1; lia
    rw [this]; nlinarith [pow_pos hmpos (K - 1)]
  have hmK1 : 0 < m ^ (K - 1) := pow_pos hmpos _
  have : m ^ (K - 1) * ((1 + ((K - 1 : ℕ) : ℝ) * (ε / 2)) * c) ≤ m ^ (K - 1) * 1 := by
    calc m ^ (K - 1) * ((1 + ((K - 1 : ℕ) : ℝ) * (ε / 2)) * c)
        ≤ m ^ (K - 1) * ((1 + ε / 2) ^ (K - 1) * c) := by gcongr
      _ = m ^ (K - 1) * (1 + ε / 2) ^ (K - 1) * c := by ring
      _ ≤ A ^ (K - 1) * c := by gcongr
      _ ≤ m ^ K := hmpow
      _ ≤ m ^ (K - 1) * 1 := by linarith
  have := le_of_mul_le_mul_left this hmK1
  rw [Nat.cast_sub hK] at this
  push_cast at this
  linarith

/-! ### Right tail -/

private lemma desc_det {b : ℤ → ℝ} {μ σ η y : ℝ}
    (hQ : ∀ i k j, i ≤ k → k ≤ j → min (b i) (b j) ≤ b k)
    (hσ : 4 ≤ σ) (hy : 4 ≤ y)
    (hη : 4 * η < φ (y - 3 / 2) - φ (y - 5 / 4)) (hH : WinApprox b μ σ η) :
    ∀ j, y ≤ xs μ σ j → b (j + 1) ≤ b j := by
  intro j hj
  by_contra hcon
  push Not at hcon
  have hσ0 : 0 < σ := by linarith
  set k1 : ℤ := ⌊μ + σ * y⌋
  have hk1a : (k1 : ℝ) ≤ μ + σ * y := Int.floor_le _
  have hk1b : μ + σ * y < k1 + 1 := Int.lt_floor_add_one _
  have hxk1a : xs μ σ k1 ≤ y := by
    unfold xs; rw [div_le_iff₀ hσ0]; linarith
  have hxk1b : y - 1 / σ < xs μ σ k1 := by
    unfold xs; rw [lt_div_iff₀ hσ0]; field_simp; linarith
  have hk1j : k1 ≤ j := by
    have : μ + σ * y ≤ j := by
      unfold xs at hj; rw [le_div_iff₀ hσ0] at hj; linarith
    have : (k1 : ℝ) ≤ j := hk1a.trans this
    exact_mod_cast this
  set L : ℕ := ⌊σ⌋₊
  have hLa : (L : ℝ) ≤ σ := Nat.floor_le hσ0.le
  have hLb : σ < L + 1 := Nat.lt_floor_add_one σ
  -- windows
  have hmono : ∀ i, i ≤ k1 - 2 * L → b i ≤ b (i + 2 * L) := fun i hi =>
    mono_left_of_lt hQ hcon (by lia) (by lia)
  have hS : ∑ i ∈ Finset.Icc (k1 - 3 * L) (k1 - 2 * L), b i ≤
      ∑ i ∈ Finset.Icc (k1 - L) k1, b i := by
    calc ∑ i ∈ Finset.Icc (k1 - 3 * L) (k1 - 2 * L), b i
        ≤ ∑ i ∈ Finset.Icc (k1 - 3 * L) (k1 - 2 * L), b (i + 2 * L) :=
          Finset.sum_le_sum fun i hi => hmono i (Finset.mem_Icc.1 hi).2
      _ = ∑ i ∈ Finset.Icc (k1 - L) k1, b i := by
          rw [sum_Icc_shift, show k1 - 3 * (L : ℤ) + 2 * L = k1 - L by ring,
            show k1 - 2 * (L : ℤ) + 2 * L = k1 by ring]
  have hS1 := hH.ge (p := k1 - 3 * L) (q := k1 - 2 * L) (by lia)
  have hS2 := hH.le (p := k1 - L) (q := k1) (by lia)
  have e3 : xs μ σ (k1 - 3 * L) = xs μ σ k1 - 3 * L / σ := by
    rw [xs_sub _ _ hσ0]; push_cast; ring
  have e2 : xs μ σ (k1 - 2 * L) = xs μ σ k1 - 2 * L / σ := by
    rw [xs_sub _ _ hσ0]; push_cast; ring
  have e1 : xs μ σ (k1 - L) = xs μ σ k1 - L / σ := by
    rw [xs_sub _ _ hσ0]; norm_cast
  have hLσ : (L : ℝ) / σ ≤ 1 := by rw [div_le_one hσ0]; exact hLa
  have hLσ' : 3 / 4 ≤ (L : ℝ) / σ := by
    rw [le_div_iff₀ hσ0]; linarith
  have h1σ : 1 / σ ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hσ0 (by norm_num)]; linarith
  have hx3 : 0 ≤ xs μ σ (k1 - 3 * L) := by
    rw [e3]; have : 3 * (L : ℝ) / σ ≤ 3 := by rw [mul_div_assoc]; linarith
    linarith
  have hI1 : L / σ * φ (y - 3 / 2) ≤
      ∫ t in xs μ σ (k1 - 3 * L)..xs μ σ (k1 - 2 * L), φ t := by
    have h := int_gpdf_lower_anti hx3 (xs_mono μ σ hσ0 (by lia : k1 - 3 * L ≤ k1 - 2 * L))
    have hlen : xs μ σ (k1 - 2 * L) - xs μ σ (k1 - 3 * L) = L / σ := by
      rw [e2, e3]; ring
    rw [hlen] at h
    have hx2 : xs μ σ (k1 - 2 * L) ≤ y - 3 / 2 := by
      rw [e2]
      have : 2 - 2 / σ ≤ 2 * (L : ℝ) / σ := by
        rw [le_div_iff₀ hσ0]; field_simp; linarith
      have : 2 / σ ≤ 1 / 2 := by rw [div_le_iff₀ hσ0]; linarith
      linarith
    have hx20 : 0 ≤ xs μ σ (k1 - 2 * L) := hx3.trans (xs_mono μ σ hσ0 (by lia))
    nlinarith [gpdf_antitone hx20 hx2, gpdf_pos (y - 3 / 2),
      gpdf_pos (xs μ σ (k1 - 2 * L)), show (0 : ℝ) ≤ L / σ by positivity]
  have hI2 : ∫ t in xs μ σ (k1 - L)..xs μ σ k1, φ t ≤ L / σ * φ (y - 5 / 4) := by
    have hx10 : 0 ≤ xs μ σ (k1 - L) := hx3.trans (xs_mono μ σ hσ0 (by lia))
    have h := int_gpdf_upper_anti hx10 (xs_mono μ σ hσ0 (by lia : k1 - L ≤ k1))
    have hlen : xs μ σ k1 - xs μ σ (k1 - L) = L / σ := by rw [e1]; ring
    rw [hlen] at h
    have hx1 : y - 5 / 4 ≤ xs μ σ (k1 - L) := by rw [e1]; linarith
    nlinarith [gpdf_antitone (show 0 ≤ y - 5 / 4 by linarith) hx1,
      show (0 : ℝ) ≤ L / σ by positivity]
  have hgap := gpdf_strictAnti (s := y - 3 / 2) (t := y - 5 / 4) (by linarith) (by linarith)
  have h1 : L / σ * (φ (y - 3 / 2) - φ (y - 5 / 4)) ≤ 2 * η := by linarith
  have h2 : 3 / 4 * (φ (y - 3 / 2) - φ (y - 5 / 4)) ≤
      L / σ * (φ (y - 3 / 2) - φ (y - 5 / 4)) :=
    mul_le_mul_of_nonneg_right hLσ' (by linarith)
  linarith

private lemma rtail_det {b : ℤ → ℝ} {μ σ η y : ℝ}
    (hdesc : ∀ j, y ≤ xs μ σ j → b (j + 1) ≤ b j) (hσ : 1 ≤ σ) (hy : 0 ≤ y)
    (hH : WinApprox b μ σ η) (k : ℤ) (hk : y + 1 ≤ xs μ σ k) :
    σ * b k ≤ φ y + η := by
  have hσ0 : 0 < σ := by linarith
  have hanti : ∀ m : ℕ, ∀ i, y ≤ xs μ σ i → b (i + m) ≤ b i := by
    intro m
    induction m with
    | zero => intro i _; simp
    | succ m ih =>
      intro i hi
      have h1 := hdesc (i + m) (hi.trans (xs_mono μ σ hσ0 (by lia)))
      have h2 := ih i hi
      push_cast; rw [← add_assoc]; linarith
  set L : ℕ := ⌊σ⌋₊
  have hLa : (L : ℝ) ≤ σ := Nat.floor_le hσ0.le
  have hLb : σ < L + 1 := Nat.lt_floor_add_one σ
  have e1 : xs μ σ (k - L) = xs μ σ k - L / σ := by rw [xs_sub _ _ hσ0]; norm_cast
  have hLσ : (L : ℝ) / σ ≤ 1 := by rw [div_le_one hσ0]; exact hLa
  have hxL : y ≤ xs μ σ (k - L) := by rw [e1]; linarith
  have hbk : ∀ i ∈ Finset.Icc (k - L) k, b k ≤ b i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have := hanti (k - i).toNat i (hxL.trans (xs_mono μ σ hσ0 hi.1))
    rwa [show i + ((k - i).toNat : ℤ) = k by lia] at this
  have hsum : (L + 1) * b k ≤ ∑ i ∈ Finset.Icc (k - L) k, b i := by
    have := Finset.sum_le_sum hbk
    rwa [Finset.sum_const, nsmul_eq_mul, card_Icc_sub] at this
  have hS := hH.le (p := k - L) (q := k) (by lia)
  have hI : ∫ t in xs μ σ (k - L)..xs μ σ k, φ t ≤ L / σ * φ y := by
    have h := int_gpdf_upper_anti (hy.trans hxL) (xs_mono μ σ hσ0 (by lia : k - L ≤ k))
    have hlen : xs μ σ k - xs μ σ (k - L) = L / σ := by rw [e1]; ring
    rw [hlen] at h
    nlinarith [gpdf_antitone hy hxL, show (0 : ℝ) ≤ L / σ by positivity]
  have hη := hH.nonneg
  have hL1 : (0 : ℝ) < L + 1 := by positivity
  have h1 : (L + 1) * b k ≤ L / σ * φ y + η := by linarith
  calc
    σ * b k ≤ σ / (L + 1) * (L / σ * φ y + η) := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos hσ0 hL1))
      calc σ * b k = σ / (L + 1) * ((L + 1) * b k) := by field_simp
        _ ≤ _ := this
    _ = L / (L + 1) * φ y + σ / (L + 1) * η := by field_simp
    _ ≤ φ y + η := by
      have hL : (L : ℝ) / (L + 1) ≤ 1 := by rw [div_le_one hL1]; linarith
      have hσ : σ / (L + 1) ≤ 1 := by rw [div_le_one hL1]; linarith
      nlinarith [gpdf_pos y]

/-- Hypotheses of the abstract local limit theorem for a family of sequences on `ℤ`. -/
private structure LLTData (b : ℕ → ℤ → ℝ) (μ σ : ℕ → ℝ) : Prop where
  nonneg : ∀ n j, 0 ≤ b n j
  logconc : ∀ n j, b n (j - 1) * b n (j + 1) ≤ b n j ^ 2
  nozero : ∀ n i j k, i < j → j < k → b n i ≠ 0 → b n k ≠ 0 → b n j ≠ 0
  sigma : Tendsto σ atTop atTop
  win : ∀ η > 0, ∀ᶠ n in atTop, WinApprox (b n) (μ n) (σ n) η

section
variable {b : ℕ → ℤ → ℝ} {μ σ : ℕ → ℝ}

private lemma LLTData.quasi (h : LLTData b μ σ) (n : ℕ) :
    ∀ i k j, i ≤ k → k ≤ j → min (b n i) (b n j) ≤ b n k := fun _ _ _ hik hkj =>
  quasi_concave (h.nonneg n) (h.logconc n) (h.nozero n) hik hkj

private lemma LLTData.lower (h : LLTData b μ σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j, φ (xs (μ n) (σ n) j) - ε < σ n * b n j := by
  set δ := ε / 4 with hδ
  set η := δ * ε / 4
  filter_upwards [h.win η (by positivity),
    h.sigma.eventually_gt_atTop (2 * (1 + 1 / δ) / ε + 1)] with n hW hσn
  intro j
  have hσ0 : 0 < σ n := by
    have : 0 < 2 * (1 + 1 / δ) / ε := by positivity
    linarith
  set L : ℕ := ⌈δ * σ n⌉₊
  have hLa : δ * σ n ≤ L := Nat.le_ceil _
  have hLb : (L : ℝ) < δ * σ n + 1 := Nat.ceil_lt_add_one (by positivity)
  have key := lower_det (h.quasi n) hσ0 L hW j
  have t1 : 1 / ((L : ℝ) + 1) ≤ 1 / (δ * σ n) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have t2 : (L : ℝ) / σ n ≤ δ + 1 / σ n := by
    rw [div_le_iff₀ hσ0]; field_simp; linarith
  have t3 : η * σ n / ((L : ℝ) + 1) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : η * σ n = ε / 4 * (δ * σ n) := by ring
    rw [this]; gcongr; linarith
  have t4 : 1 / (δ * σ n) + 1 / σ n < ε / 2 := by
    have : 1 / (δ * σ n) + 1 / σ n = (1 + 1 / δ) / σ n := by field_simp; ring
    rw [this, div_lt_iff₀ hσ0]
    have : 2 * (1 + 1 / δ) / ε * ε = 2 * (1 + 1 / δ) := by field_simp
    nlinarith
  linarith

private lemma LLTData.upper (h : LLTData b μ σ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᶠ n in atTop, ∀ j, |xs (μ n) (σ n) j| ≤ T →
      σ n * b n j < φ (xs (μ n) (σ n) j) + ε := by
  set c := φ (T + 1) / 2 with hc
  have hc0 : 0 < c := by have := gpdf_pos (T + 1); positivity
  set K : ℕ := ⌈2 / (c * ε)⌉₊ + 2
  have hK1 : 1 ≤ K := by lia
  have hKbig : 1 < (1 + ((K : ℝ) - 1) * (ε / 2)) * c := by
    have h1 : 2 / (c * ε) ≤ (⌈2 / (c * ε)⌉₊ : ℝ) := Nat.le_ceil _
    have : 1 ≤ (⌈2 / (c * ε)⌉₊ : ℝ) * (ε / 2) * c := by
      calc (1 : ℝ) = 2 / (c * ε) * (ε / 2) * c := by field_simp
        _ ≤ _ := by gcongr
    simp only [K]; push_cast
    nlinarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set δ := min (ε / 8) (1 / (K : ℝ))
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  set η := δ * ε / 8
  filter_upwards [h.win η (by positivity), h.lower hc0,
    h.sigma.eventually_gt_atTop (1 / δ)] with n hW hlow hσn
  intro j hj
  have hσ0 : 0 < σ n := lt_trans (by positivity) hσn
  set M : ℕ := ⌊δ * σ n⌋₊
  have hδσ1 : 1 < δ * σ n := by rwa [div_lt_iff₀ hδ0, mul_comm] at hσn
  have hMa : (M : ℝ) ≤ δ * σ n := Nat.floor_le (by positivity)
  have hMb : δ * σ n < M + 1 := Nat.lt_floor_add_one _
  have hM1 : 1 ≤ M := by
    have : (1 : ℕ) < M + 1 := by exact_mod_cast (show (1 : ℝ) < M + 1 by linarith)
    lia
  have hjc : c ≤ φ (xs (μ n) (σ n) j) := by
    have : φ (T + 1) ≤ φ (xs (μ n) (σ n) j) := gpdf_le_of_sq_le (by
      have := sq_abs (xs (μ n) (σ n) j)
      have : |xs (μ n) (σ n) j| ^ 2 ≤ (T + 1) ^ 2 := by
        have := abs_nonneg (xs (μ n) (σ n) j)
        nlinarith
      linarith)
    have := gpdf_pos (T + 1)
    linarith
  have hB : c ≤ σ n * b n (j + (K * M : ℕ)) := by
    have hl := hlow (j + (K * M : ℕ))
    have hx : xs (μ n) (σ n) (j + (K * M : ℕ)) = xs (μ n) (σ n) j + (K * M : ℕ) / σ n := by
      rw [xs_add _ _ hσ0]; norm_cast
    have hKM : ((K * M : ℕ) : ℝ) / σ n ≤ 1 := by
      rw [div_le_one hσ0]; push_cast
      have : (K : ℝ) * δ ≤ 1 := by
        have : δ ≤ 1 / K := min_le_right _ _
        rw [le_div_iff₀ hKpos] at this; linarith
      nlinarith
    have hKM0 : (0 : ℝ) ≤ ((K * M : ℕ) : ℝ) / σ n := by positivity
    have : φ (T + 1) ≤ φ (xs (μ n) (σ n) (j + (K * M : ℕ))) := gpdf_le_of_sq_le (by
      rw [hx]
      have h1 := abs_le.1 hj
      nlinarith)
    linarith
  have hsmall : (M : ℝ) / σ n + η * σ n / (M + 1) ≤ ε / 2 := by
    have t1 : (M : ℝ) / σ n ≤ ε / 8 := by
      rw [div_le_iff₀ hσ0]
      have : δ ≤ ε / 8 := min_le_left _ _
      nlinarith
    have t2 : η * σ n / ((M : ℝ) + 1) ≤ ε / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have : η * σ n = ε / 8 * (δ * σ n) := by ring
      rw [this]; gcongr
    linarith
  exact upper_det (h.nonneg n) (h.logconc n) (h.nozero n) hσ0 hW hc0 hjc hK1 hM1 hε hε1 hB
    hKbig hsmall

private lemma LLTData.rtail (h : LLTData b μ σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ᶠ n in atTop, ∀ j, T ≤ xs (μ n) (σ n) j →
      |σ n * b n j - φ (xs (μ n) (σ n) j)| < ε := by
  obtain ⟨y0, hy00, hy0⟩ := gpdf_tail (show 0 < ε / 2 by positivity)
  set y := max y0 4
  have hy4 : 4 ≤ y := le_max_right _ _
  have hyε : φ y < ε / 2 := hy0 y (le_max_left _ _)
  have hg : 0 < φ (y - 3 / 2) - φ (y - 5 / 4) :=
    sub_pos.mpr (gpdf_strictAnti (by linarith) (by linarith))
  set η := min (ε / 4) ((φ (y - 3 / 2) - φ (y - 5 / 4)) / 8)
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨y + 1, by linarith, ?_⟩
  filter_upwards [h.win η hη0, h.sigma.eventually_ge_atTop 4] with n hW hσn
  intro j hj
  have hdesc := desc_det (h.quasi n) hσn hy4 (by
    linarith [min_le_right (ε / 4) ((φ (y - 3 / 2) - φ (y - 5 / 4)) / 8)]) hW
  have hup := rtail_det hdesc (by linarith) (by linarith) hW j hj
  have h0 : 0 ≤ σ n * b n j := mul_nonneg (by linarith) (h.nonneg n j)
  rw [abs_lt]
  constructor <;> linarith [min_le_left (ε / 4)
      ((φ (y - 3 / 2) - φ (y - 5 / 4)) / 8),
    gpdf_antitone (show 0 ≤ y by linarith) (show y ≤ xs (μ n) (σ n) j by linarith),
    gpdf_pos (xs (μ n) (σ n) j)]

/-- Reflection `j ↦ -j` of the data. -/
private lemma LLTData.reflect (h : LLTData b μ σ) :
    LLTData (fun n j => b n (-j)) (fun n => -μ n) σ where
  nonneg n j := h.nonneg n (-j)
  logconc n j := by
    simpa only [show -(j - 1) = -j + 1 by ring,
      show -(j + 1) = -j - 1 by ring, mul_comm] using h.logconc n (-j)
  nozero n i j k hij hjk hi hk := h.nozero n (-k) (-j) (-i) (by lia) (by lia) hk hi
  sigma := h.sigma
  win η hη := by
    filter_upwards [h.win η hη] with n hW
    intro p q hpq
    have hx : ∀ j : ℤ, xs (-μ n) (σ n) j = -xs (μ n) (σ n) (-j) := by
      intro j; unfold xs; push_cast; ring
    have hsum : ∑ j ∈ Finset.Icc p q, b n (-j) = ∑ j ∈ Finset.Icc (-q) (-p), b n j := by
      apply Finset.sum_nbij' (fun j => -j) (fun j => -j)
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; lia
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; lia
      · intro a _; simp
      · intro a _; simp
      · intro a _; rfl
    rw [hsum, hx, hx, int_gpdf_neg]
    exact hW (-q) (-p) (by lia)

end

/-- **Abstract local limit theorem.** -/
private theorem LLTData.llt {b : ℕ → ℤ → ℝ} {μ σ : ℕ → ℝ}
    (h : LLTData b μ σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j, |σ n * b n j - φ (xs (μ n) (σ n) j)| < ε := by
  set ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'e : ε' ≤ ε := min_le_left _ _
  obtain ⟨T1, hT1, h1⟩ := h.rtail hε'
  obtain ⟨T2, hT2, h2⟩ := h.reflect.rtail hε'
  have hT : 0 ≤ max T1 T2 := le_max_of_le_left hT1
  filter_upwards [h1, h2, h.lower hε', h.upper hε' hε'1 hT] with n hr hl hlow hup
  intro j
  by_cases hj1 : T1 ≤ xs (μ n) (σ n) j
  · exact lt_of_lt_of_le (hr j hj1) hε'e
  by_cases hj2 : xs (μ n) (σ n) j ≤ -T2
  · have hx : xs (-μ n) (σ n) (-j) = -xs (μ n) (σ n) j := by
      unfold xs; push_cast; ring
    have := hl (-j) (by rw [hx]; linarith)
    simp only [neg_neg, hx, gpdf_neg] at this
    exact lt_of_lt_of_le this hε'e
  push Not at hj1 hj2
  have habs : |xs (μ n) (σ n) j| ≤ max T1 T2 := by
    rw [abs_le]; constructor
    · linarith [le_max_right T1 T2]
    · linarith [le_max_left T1 T2]
  rw [abs_lt]
  constructor <;> linarith [hlow j, hup j habs]

private lemma Phi_sub_le {u v : ℝ} (h : u ≤ v) : Phi v - Phi u ≤ (v - u) / 2 := by
  rw [Phi_sub]; exact int_gpdf_le_half h

/-- Pólya's theorem for the Gaussian limit: pointwise convergence of distribution functions to
`Phi` is uniform. -/
private lemma polya {F : ℕ → ℝ → ℝ} (hmono : ∀ n, Monotone (F n))
    (h0 : ∀ n x, 0 ≤ F n x)
    (h1 : ∀ n x, F n x ≤ 1) (hconv : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (Phi x)))
    {η : ℝ} (hη : 0 < η) : ∀ᶠ n in atTop, ∀ x, |F n x - Phi x| < η := by
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨a, ha⟩ := (Phi_tendsto_atBot.eventually (gt_mem_nhds hη2)).exists_forall_of_atBot
  obtain ⟨b, hb⟩ := (Phi_tendsto_atTop.eventually
    (lt_mem_nhds (show 1 - η / 2 < 1 by linarith))).exists_forall_of_atTop
  set m : ℕ := ⌈(b - a) / (η / 2)⌉₊
  set g : ℕ → ℝ := fun i => a + i * (η / 2)
  have hgm : b ≤ g m := by
    have : (b - a) / (η / 2) ≤ m := Nat.le_ceil _
    rw [div_le_iff₀ hη2] at this
    simp only [g]; linarith
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (m + 1),
      |F n (g i) - Phi (g i)| < η / 2 := by
    rw [Filter.eventually_all_finset]
    intro i _
    have := (hconv (g i)).sub_const (Phi (g i))
    rw [sub_self] at this
    have := this.abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds hη2)
  filter_upwards [hev] with n hn
  intro x
  have hga : g 0 = a := by simp [g]
  by_cases hxa : x < a
  · have e1 := hn 0 (by simp)
    rw [hga] at e1
    rw [abs_lt] at e1 ⊢
    constructor <;>
      linarith [hmono n hxa.le, ha a le_rfl, Phi_mono hxa.le, h0 n x,
        show 0 ≤ Phi x from
          setIntegral_nonneg measurableSet_Iic fun t _ => (gpdf_pos t).le]
  push Not at hxa
  by_cases hxb : g m ≤ x
  · have e1 := hn m (by simp)
    rw [abs_lt] at e1 ⊢
    constructor <;>
      linarith [hmono n hxb, hb (g m) hgm, Phi_mono hxb, h1 n x,
        show Phi x ≤ 1 by rw [Phi_eq_cdf]; exact cdf_le_one _ _]
  push Not at hxb
  set i : ℕ := ⌊(x - a) / (η / 2)⌋₊
  have hi1 : (i : ℝ) ≤ (x - a) / (η / 2) := Nat.floor_le (div_nonneg (by linarith) hη2.le)
  have hi2 : (x - a) / (η / 2) < i + 1 := Nat.lt_floor_add_one _
  have hgi : g i ≤ x := by
    rw [le_div_iff₀ hη2] at hi1; simp only [g]; linarith
  have hgi1 : x < g (i + 1) := by
    rw [div_lt_iff₀ hη2] at hi2; simp only [g]; push_cast; linarith
  have him : i < m := by
    by_contra hc; push Not at hc
    have : g m ≤ g i := by
      simp only [g]; have : (m : ℝ) ≤ i := by exact_mod_cast hc
      nlinarith
    linarith
  have e1 := hn i (by simp; lia)
  have e2 := hn (i + 1) (by simp; lia)
  have hstep : g (i + 1) - g i = η / 2 := by simp only [g]; push_cast; ring
  rw [abs_lt] at e1 e2 ⊢
  constructor <;> nlinarith [hmono n hgi, hmono n hgi1.le, Phi_sub_le hgi,
    Phi_sub_le hgi1.le, Phi_mono hgi, Phi_mono hgi1.le]

/-! ### From polynomials to the abstract data -/

private lemma eval_one_eq_sum (p : ℝ[X]) :
    p.eval 1 = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := by
  simp [eval_eq_sum_range]

private lemma sum_coeff_div_eval_one {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0) :
    ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k / p.eval 1 = 1 := by
  rw [← Finset.sum_div, ← eval_one_eq_sum,
    div_self (eval_pos_of_coeff_nonneg hnn hp one_pos).ne']

/-- The coefficient sequence of `p`, normalized and extended by zero to `ℤ`. -/
private def bP (p : ℝ[X]) (j : ℤ) : ℝ := if 0 ≤ j then p.coeff j.toNat / p.eval 1 else 0

/-- The standardized distribution function of the coefficient distribution. -/
private def cdfP (p : ℝ[X]) (μ σ x : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (p.natDegree + 1)).filter (fun k : ℕ => ((k : ℝ) - μ) / σ ≤ x),
    p.coeff k / p.eval 1

private lemma bP_natCast (p : ℝ[X]) (k : ℕ) : bP p k = p.coeff k / p.eval 1 := by
  simp [bP]

private lemma cdfP_mono {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0) (μ σ : ℝ) :
    Monotone (cdfP p μ σ) := by
  intro x x' hxx'
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · grind
  · intro k _ _
    exact div_nonneg (hnn k) (eval_pos_of_coeff_nonneg hnn hp one_pos).le

private lemma cdfP_xs {p : ℝ[X]} {μ σ : ℝ} (hσ : 0 < σ) (q : ℤ) :
    cdfP p μ σ (xs μ σ q) = ∑ k ∈ Finset.range (p.natDegree + 1),
      if (k : ℤ) ≤ q then p.coeff k / p.eval 1 else 0 := by
  rw [cdfP, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  have : ((k : ℝ) - μ) / σ ≤ xs μ σ q ↔ (k : ℤ) ≤ q := by
    unfold xs
    rw [div_le_div_iff_of_pos_right hσ, sub_le_sub_iff_right]
    have : ((k : ℕ) : ℝ) = (((k : ℕ) : ℤ) : ℝ) := by push_cast; rfl
    rw [this]; exact Int.cast_le
  simp only [this]

private lemma sum_Icc_bP (p : ℝ[X]) (a b : ℤ) :
    ∑ j ∈ Finset.Icc a b, bP p j = ∑ k ∈ Finset.range (p.natDegree + 1),
      if a ≤ (k : ℤ) ∧ (k : ℤ) ≤ b then p.coeff k / p.eval 1 else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij_ne_zero (fun (k : ℕ) _ _ => (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk _
    simp only [Finset.mem_filter] at hk
    simpa [Finset.mem_Icc] using hk.2
  · intro k₁ _ _ k₂ _ _ h
    exact_mod_cast h
  · intro j hj hne
    rw [Finset.mem_Icc] at hj
    have hj0 : 0 ≤ j := by
      by_contra hc
      simp [bP, hc] at hne
    have hne' : p.coeff j.toNat / p.eval 1 ≠ 0 := by simpa [bP, hj0] using hne
    have hdeg : j.toNat ≤ p.natDegree := by
      by_contra hc
      push Not at hc
      rw [coeff_eq_zero_of_natDegree_lt hc] at hne'
      simp at hne'
    refine ⟨j.toNat, ?_, hne', ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by lia, by lia, by lia⟩
    · simp; lia
  · intro k _ _
    rw [bP_natCast]

private lemma window_eq {p : ℝ[X]} {μ σ : ℝ} (hσ : 0 < σ) {a b : ℤ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, bP p j =
      cdfP p μ σ (xs μ σ b) - cdfP p μ σ (xs μ σ (a - 1)) := by
  rw [sum_Icc_bP, cdfP_xs hσ, cdfP_xs hσ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h1 : a ≤ (k : ℤ) <;>
    by_cases h2 : (k : ℤ) ≤ b <;>
      by_cases h3 : (k : ℤ) ≤ a - 1 <;>
        simp only [h1, h2, h3, and_self, ite_true, ite_false, sub_self, sub_zero] <;> lia

private theorem lltData_of_poly {P : ℕ → ℝ[X]} {μ σ : ℕ → ℝ}
    (hnn : ∀ n k, 0 ≤ (P n).coeff k) (hne : ∀ n, P n ≠ 0)
    (hlc : ∀ n k, 0 < k → (P n).coeff (k - 1) * (P n).coeff (k + 1) ≤ (P n).coeff k ^ 2)
    (hnz : ∀ n i j k, i < j → j < k → (P n).coeff i ≠ 0 → (P n).coeff k ≠ 0 →
      (P n).coeff j ≠ 0)
    (hσ : Tendsto σ atTop atTop)
    (hcdf : ∀ x, Tendsto (fun n => cdfP (P n) (μ n) (σ n) x) atTop (𝓝 (Phi x))) :
    LLTData (fun n => bP (P n)) μ σ where
  nonneg n j := by
    unfold bP; split_ifs
    · exact div_nonneg (hnn n _) (eval_pos_of_coeff_nonneg (hnn n) (hne n) one_pos).le
    · exact le_rfl
  logconc n j := by
    have he := eval_pos_of_coeff_nonneg (hnn n) (hne n) one_pos
    by_cases hj : 1 ≤ j
    · have h1 : bP (P n) (j - 1) = (P n).coeff (j.toNat - 1) / (P n).eval 1 := by
        simp only [bP, show 0 ≤ j - 1 by lia, ite_true]
        congr 2; lia
      have h2 : bP (P n) (j + 1) = (P n).coeff (j.toNat + 1) / (P n).eval 1 := by
        simp only [bP, show 0 ≤ j + 1 by lia, ite_true]
        congr 2; lia
      have h3 : bP (P n) j = (P n).coeff j.toNat / (P n).eval 1 := by
        simp only [bP, show 0 ≤ j by lia, ite_true]
      rw [h1, h2, h3, div_mul_div_comm, div_pow, ← sq]
      exact div_le_div_of_nonneg_right (hlc n j.toNat (by lia)) (by positivity)
    · have h1 : bP (P n) (j - 1) = 0 := by
        simp only [bP]
        split
        next h => lia
        next => rfl
      rw [h1, zero_mul]; positivity
  nozero n i j k hij hjk hi hk := by
    have hi0 : 0 ≤ i := by by_contra hc; simp [bP, hc] at hi
    have he := eval_pos_of_coeff_nonneg (hnn n) (hne n) one_pos
    simp only [bP, hi0, ite_true, show 0 ≤ k by lia, show 0 ≤ j by lia, ne_eq,
      div_eq_zero_iff, he.ne', or_false] at hi hk ⊢
    exact hnz n i.toNat j.toNat k.toNat (by lia) (by lia) hi hk
  sigma := hσ
  win η hη := by
    have hη4 : 0 < η / 4 := by positivity
    filter_upwards [polya (fun n => cdfP_mono (hnn n) (hne n) (μ n) (σ n))
      (fun n _ => Finset.sum_nonneg fun k _ =>
        div_nonneg (hnn n k) (eval_pos_of_coeff_nonneg (hnn n) (hne n) one_pos).le)
      (fun n _ => by
        rw [← sum_coeff_div_eval_one (hnn n) (hne n)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => div_nonneg (hnn n k)
            (eval_pos_of_coeff_nonneg (hnn n) (hne n) one_pos).le)) hcdf hη4,
      hσ.eventually_gt_atTop (2 / η)] with n hpol hσn
    have hσ0 : 0 < σ n := lt_trans (by positivity) hσn
    intro a b hab
    rw [window_eq hσ0 hab]
    · have e1 := abs_lt.1 (hpol (xs (μ n) (σ n) b))
      have e2 := abs_lt.1 (hpol (xs (μ n) (σ n) (a - 1)))
      have hP := Phi_sub (xs (μ n) (σ n) (a - 1)) (xs (μ n) (σ n) b)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (gpdf_intervalIntegrable (xs (μ n) (σ n) (a - 1)) (xs (μ n) (σ n) a))
        (gpdf_intervalIntegrable (xs (μ n) (σ n) a) (xs (μ n) (σ n) b))
      have hx : xs (μ n) (σ n) a - xs (μ n) (σ n) (a - 1) = 1 / σ n := by
        rw [xs_sub _ _ hσ0]
        push_cast
        ring
      have hle : xs (μ n) (σ n) (a - 1) ≤ xs (μ n) (σ n) a :=
        xs_mono _ _ hσ0 (by lia)
      have i1 := int_gpdf_nonneg hle
      have i2 := int_gpdf_le_half hle
      rw [hx] at i2
      have : 1 / σ n / 2 ≤ η / 4 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        rw [div_lt_iff₀ hη] at hσn
        linarith
      rw [abs_le]
      constructor <;> linarith

end Aux

/-- Reduction of weak convergence to pointwise convergence of the standardized distribution
function.  This is a portmanteau argument: the Gaussian has no atoms, so every `Iic x` is a
continuity set; `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
(`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`). -/
private theorem tendsto_cdf_of_tendsto_standardized {P : ℕ → ℝ[X]}
    (hnn : ∀ n k, 0 ≤ (P n).coeff k) (hne : ∀ n, P n ≠ 0)
    (hclt : Tendsto (fun n => standardizedCoeffDistribution (P n)) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩)) (x : ℝ) :
    Tendsto (fun n => ∑ k ∈ (Finset.range ((P n).natDegree + 1)).filter
        (fun k : ℕ => ((k : ℝ) - coeffMean (P n)) / coeffStdDev (P n) ≤ x),
          (P n).coeff k / (P n).eval 1) atTop
      (𝓝 (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)) := by
  set γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩ with hγ
  have hfr : γ (frontier (Set.Iic x)) = 0 := by
    rw [frontier_Iic, ProbabilityMeasure.coeFn_def]
    change ((gaussianReal 0 1) {x}).toNNReal = 0
    rw [gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton (a := x))]
    rfl
  have key := (NNReal.continuous_coe.tendsto _).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hclt hfr)
  have hlim : ((γ (Set.Iic x) : NNReal) : ℝ) = ∫ t in Set.Iic x, gaussianPDFReal 0 1 t := by
    rw [ProbabilityMeasure.coeFn_def]
    change ((gaussianReal 0 1) (Set.Iic x)).toReal = _
    rw [gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Iic fun t _ => (gaussianPDFReal_pos _ _ _
      one_ne_zero).le
  rw [hlim] at key
  refine key.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [ProbabilityMeasure.coeFn_def]
  change ((standardizedCoeffDistribution (P n) : Measure ℝ) (Set.Iic x)).toReal = _
  have hmeas : Measurable fun t : ℝ => (t - coeffMean (P n)) / coeffStdDev (P n) := by
    fun_prop
  rw [standardizedCoeffDistribution, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hmeas measurableSet_Iic]
  rw [coeffDistribution_toMeasure (hnn n) (hne n), coeffMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun k _ => by
    rw [Measure.dirac_apply' _ (hmeas measurableSet_Iic)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by unfold Set.indicator; split_ifs <;> simp)), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [Measure.dirac_apply' _ (hmeas measurableSet_Iic), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (div_nonneg (hnn n k) (eval_pos_of_coeff_nonneg (hnn n) (hne n) one_pos).le)]
  by_cases hk : ((k : ℝ) - coeffMean (P n)) / coeffStdDev (P n) ≤ x <;> simp [hk]

/-- **Bender's local limit theorem** (Bender 1973, Theorem 2; log-concavity plus the CLT).
If `P n` have nonnegative, log-concave coefficients without internal zeros, `Var → ∞`, and the
standardized coefficient distributions converge weakly to `N(0,1)` (for real-rooted `P n` this is
Harper's theorem), then uniformly in `k`
`σₙ · Pr[Kₙ = k] - φ((k - μₙ) / σₙ) → 0`. -/
theorem tendsto_localLimit_of_logConcave {P : ℕ → ℝ[X]}
    (hnn : ∀ n k, 0 ≤ (P n).coeff k) (hne : ∀ n, P n ≠ 0)
    (hlc : ∀ n k, 0 < k → (P n).coeff (k - 1) * (P n).coeff (k + 1) ≤ (P n).coeff k ^ 2)
    (hnz : ∀ n i j k, i < j → j < k → (P n).coeff i ≠ 0 → (P n).coeff k ≠ 0 →
      (P n).coeff j ≠ 0)
    (hvar : Tendsto (fun n => coeffVariance (P n)) atTop atTop)
    (hclt : Tendsto (fun n => standardizedCoeffDistribution (P n)) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : ℕ,
      |coeffStdDev (P n) * ((P n).coeff k / (P n).eval 1) -
        gaussianPDFReal 0 1 (((k : ℝ) - coeffMean (P n)) / coeffStdDev (P n))| < ε := by
  intro ε hε
  filter_upwards [(lltData_of_poly hnn hne hlc hnz (Real.tendsto_sqrt_atTop.comp hvar)
    (tendsto_cdf_of_tendsto_standardized hnn hne hclt)).llt hε] with n hn
  intro k
  simpa [bP_natCast, Function.comp_apply, coeffStdDev, xs] using hn (k : ℤ)

end Polynomial

