/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib

/-!
# Entire functions with polynomially bounded real part are polynomials

We show that an entire function `g : ℂ → ℂ` whose circle mean of the positive part of
`Re g` grows at most like `A * (1 + r) ^ k` is a polynomial of degree at most `k`. The
proof bounds the Taylor coefficients of `g` by circle means of `|Re g|`, and then gives
a Cauchy-type estimate for the derivative. The file also contains an elementary version
of Borel's growth lemma, used to turn a logarithmic growth inequality into a quadratic
bound.

## Main definitions

* `Complex.posMean`: the circle mean of `max (g z).re 0` on the circle of radius `r`.

## Main statements

* `Complex.circleAverage_abs_re`: the circle mean of `|Re h|` equals `2 * posMean h r - (h 0).re`.
* `Complex.norm_deriv_le_posMean`: a Cauchy-type bound on `‖deriv h z‖` in terms of
  `posMean h ρ`.
* `Complex.borel_growth`: for monotone `V ≥ 1`, every interval `[r, r + 2]` contains `s` with
  `V (s + 1 / V s) ≤ 2 * V s`.
* `Complex.growth_of_GI`: a logarithmic growth inequality for `T` implies `T r ≤ A * (1 + r) ^ 2`.
* `Complex.poly_of_mean_pos_re_le`: an entire function with `posMean g r ≤ A * (1 + r) ^ k` for
  all `r > 0` agrees with a polynomial of natural degree at most `k`.
-/

@[expose] public section

section Coeff_part


/-!
# Taylor coefficients of an entire function controlled by the real part on circles

For an entire function `h`, the `n`-th Taylor coefficient `a_n` (`n ≥ 1`) satisfies
`|a_n| ρ^n ≤ 2 · (circle mean of |Re h| on the circle of radius ρ)`, and the circle mean of
`|Re h|` equals `2 · posMean h ρ - Re h(0)`, where `posMean h ρ` is the circle mean of
`(Re h)⁺`.
Consequences: a Cauchy-type estimate for `h'` in terms of `posMean h`, and the polynomial lemma.
-/


open Complex Real

noncomputable section

namespace Complex

/-- The circle mean of the positive part of the real part of `g` (Nevanlinna's `T(r, e^g)`). -/
def posMean (g : ℂ → ℂ) (r : ℝ) : ℝ := Real.circleAverage (fun z => max (g z).re 0) 0 r

private theorem norm_circleAverage_le' {f : ℂ → ℂ} {c : ℂ} {R : ℝ} :
    ‖circleAverage f c R‖ ≤ circleAverage (fun z => ‖f z‖) c R := by
  unfold circleAverage
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  gcongr
  exact intervalIntegral.norm_integral_le_integral_norm (by positivity)

private theorem cA_coeff {h : ℂ → ℂ} (hh : Differentiable ℂ h) {ρ : ℝ}
    (hρ : 0 < ρ) (n : ℕ) :
    circleAverage (fun z => (z ^ n)⁻¹ * h z) 0 ρ = iteratedDeriv n h 0 / n.factorial := by
  rw [circleAverage_eq_circleIntegral hρ.ne']
  have h1 : (∮ z in C(0, ρ), (z - 0)⁻¹ • ((z ^ n)⁻¹ * h z)) =
      ∮ z in C(0, ρ), (1 / (z - 0) ^ (n + 1)) • h z := by
    apply circleIntegral.integral_congr hρ.le; intro z hz
    simp only [sub_zero, smul_eq_mul, pow_succ]
    field_simp
  rw [h1, (hh.diffContOnCl (s := Metric.ball (0:ℂ) ρ)).circleIntegral_one_div_sub_center_pow_smul
    hρ n, smul_smul, smul_eq_mul]
  have : (2 * ↑π * I) ≠ 0 := two_pi_I_ne_zero
  field_simp

private theorem cA_mul_pow {h : ℂ → ℂ} (hh : Differentiable ℂ h) {ρ : ℝ}
    (n : ℕ) (hn : 1 ≤ n) :
    circleAverage (fun z => h z * z ^ n) 0 ρ = 0 := by
  rw [((by fun_prop : Differentiable ℂ (fun z => h z * z ^ n)).diffContOnCl
    (s := Metric.ball (0:ℂ) |ρ|)).circleAverage]
  simp; lia

/-- Coefficient bound: `|a_n| ρ^n ≤ 2 · mean |Re h|`. -/
private theorem coeff_bound {h : ℂ → ℂ} (hh : Differentiable ℂ h) {ρ : ℝ}
    (hρ : 0 < ρ) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedDeriv n h 0 / n.factorial‖ * ρ ^ n ≤
      2 * circleAverage (fun z => |(h z).re|) 0 ρ := by
  set a := iteratedDeriv n h 0 / n.factorial
  set F : ℂ → ℂ := fun z => ((h z).re : ℂ) * (starRingEnd ℂ z) ^ n
  have hsph : ∀ z ∈ Metric.sphere (0:ℂ) |ρ|, F z =
      ((ρ : ℂ) ^ (2 * n) / 2) • ((z ^ n)⁻¹ * h z) +
        (1 / 2 : ℂ) • starRingEnd ℂ (h z * z ^ n) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hρ] at hz
    have hz0 : z ≠ 0 := by rintro rfl; simp_all
    have hzc : starRingEnd ℂ z = (ρ : ℂ) ^ 2 / z := by
      rw [eq_div_iff hz0, mul_comm, mul_conj, normSq_eq_norm_sq, hz]; push_cast; ring
    have hre : ((h z).re : ℂ) = (h z + starRingEnd ℂ (h z)) / 2 := by
      rw [add_conj]; push_cast; ring
    simp only [F, smul_eq_mul]
    rw [map_mul (starRingEnd ℂ) (h z), map_pow, hzc, hre, div_pow, ← pow_mul]
    have : z ^ n ≠ 0 := pow_ne_zero _ hz0
    field_simp
  have hint1 : CircleIntegrable (fun z : ℂ => ((ρ : ℂ) ^ (2 * n) / 2) • ((z ^ n)⁻¹ * h z))
      0 ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    refine ContinuousOn.const_smul (ContinuousOn.mul
      (ContinuousOn.inv₀ (f := fun z : ℂ => z ^ n) (continuous_pow n).continuousOn ?_)
      hh.continuous.continuousOn) ((ρ : ℂ) ^ (2 * n) / 2)
    intro z hz; apply pow_ne_zero; rintro rfl; simp_all
  have hc2 : Continuous (fun z : ℂ => h z * z ^ n) := hh.continuous.mul (continuous_pow n)
  have hint2 : CircleIntegrable (fun z : ℂ => h z * z ^ n) 0 ρ :=
    hc2.continuousOn.circleIntegrable hρ.le
  have hint3 :
      CircleIntegrable (fun z : ℂ => (1 / 2 : ℂ) • starRingEnd ℂ (h z * z ^ n)) 0 ρ :=
    (((continuous_conj.comp hc2).const_smul (1 / 2 : ℂ))).continuousOn.circleIntegrable hρ.le
  have hconj : circleAverage (fun z => starRingEnd ℂ (h z * z ^ n)) 0 ρ =
      starRingEnd ℂ (circleAverage (fun z => h z * z ^ n) 0 ρ) :=
    (conjCLE : ℂ →L[ℝ] ℂ).circleAverage_comp_comm hint2
  have hav : circleAverage F 0 ρ = ((ρ : ℂ) ^ (2 * n) / 2) * a := by
    rw [circleAverage_congr_sphere hsph, circleAverage_fun_add hint1 hint3,
      circleAverage_fun_smul, circleAverage_fun_smul, hconj, cA_mul_pow hh n hn,
      cA_coeff hh hρ n]
    simp [a]
  have hnorm : circleAverage (fun z => ‖F z‖) 0 ρ =
      ρ ^ n * circleAverage (fun z => |(h z).re|) 0 ρ := by
    rw [← smul_eq_mul, ← circleAverage_fun_smul]
    apply circleAverage_congr_sphere
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hρ] at hz
    simp [F, hz, smul_eq_mul, mul_comm]
  have key := norm_circleAverage_le' (f := F) (c := 0) (R := ρ)
  rw [hav, hnorm, norm_mul] at key
  have : ‖((ρ : ℂ) ^ (2 * n) / 2)‖ = ρ ^ n * ρ ^ n / 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    simp [pow_mul, ← mul_pow, sq]
  rw [this] at key
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  nlinarith

/-- Mean value property for the real part. -/
private theorem circleAverage_re_eq {h : ℂ → ℂ} (hh : Differentiable ℂ h) (r : ℝ) :
    circleAverage (fun z => (h z).re) 0 r = (h 0).re := by
  have hint : CircleIntegrable h 0 r := hh.continuous.continuousOn.circleIntegrable'
  have := (reCLM : ℂ →L[ℝ] ℝ).circleAverage_comp_comm hint
  simp only [reCLM_apply] at this
  rw [show (fun z => (h z).re) = (reCLM ∘ h) from rfl, this,
    (hh.diffContOnCl (s := Metric.ball (0:ℂ) |r|)).circleAverage]

/-- A continuous real-valued function is integrable on every complex circle. -/
theorem circleIntegrable_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (r : ℝ) :
    CircleIntegrable f 0 r := hf.continuousOn.circleIntegrable'

/-- The circle mean of `|Re h|` in terms of `posMean`. -/
theorem circleAverage_abs_re {h : ℂ → ℂ} (hh : Differentiable ℂ h) (r : ℝ) :
    circleAverage (fun z => |(h z).re|) 0 r = 2 * posMean h r - (h 0).re := by
  have hc : Continuous fun z => (h z).re := continuous_re.comp hh.continuous
  have e : (fun z => |(h z).re|) = fun z => (2 : ℝ) • max (h z).re 0 - (h z).re := by
    funext z
    rcases le_total (h z).re 0 with h1 | h1
    · simp [abs_of_nonpos h1, max_eq_right h1]
    · simp [abs_of_nonneg h1, max_eq_left h1]; ring
  rw [e, circleAverage_fun_sub, circleAverage_fun_smul, circleAverage_re_eq hh]
  · rfl
  · exact circleIntegrable_of_continuous ((hc.max continuous_const).const_smul (2 : ℝ)) r
  · exact circleIntegrable_of_continuous hc r

/-- The positive-real-part circle mean is nonnegative. -/
theorem posMean_nonneg (h : ℂ → ℂ) (r : ℝ) : 0 ≤ posMean h r :=
  circleAverage_nonneg_of_nonneg (fun _ _ => le_max_right _ _)

private theorem coeff_bound' {h : ℂ → ℂ} (hh : Differentiable ℂ h) {ρ : ℝ}
    (hρ : 0 < ρ) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedDeriv n h 0 / n.factorial‖ * ρ ^ n ≤ 2 * (2 * posMean h ρ - (h 0).re) := by
  rw [← circleAverage_abs_re hh]
  exact coeff_bound hh hρ hn

private theorem hasSum_succ_mul_geometric {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun m : ℕ => ((m : ℝ) + 1) * x ^ m) (1 / (1 - x) ^ 2) := by
  have hx : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have A := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have B := hasSum_geometric_of_lt_one h0 h1
  convert A.add B using 1
  · funext m; ring
  · have : (1 - x) ≠ 0 := by linarith
    field_simp; ring

/-- Cauchy-type estimate of `h'` in terms of `posMean h` on a larger circle. -/
theorem norm_deriv_le_posMean {h : ℂ → ℂ} (hh : Differentiable ℂ h) {ρ : ℝ} {z : ℂ}
    (hz : ‖z‖ < ρ) :
    ‖deriv h z‖ ≤ 2 * ρ / (ρ - ‖z‖) ^ 2 * (2 * posMean h ρ - (h 0).re) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hz
  set S := 2 * posMean h ρ - (h 0).re
  have hd : Differentiable ℂ (deriv h) :=
    differentiableOn_univ.mp ((hh.differentiableOn (s := Set.univ)).deriv isOpen_univ)
  have hT := Complex.hasSum_taylorSeries_of_entire hd 0 z
  set x := ‖z‖ / ρ
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [div_lt_one hρ]; exact hz
  have hG := (hasSum_succ_mul_geometric hx0 hx1).mul_left (2 * S / ρ)
  have hb := hT.norm_le_of_bounded hG ?_
  · convert hb using 1
    simp only [sub_zero] at *
    have : ρ - ‖z‖ ≠ 0 := by linarith
    have hx' : 1 - x = (ρ - ‖z‖) / ρ := by simp only [x]; field_simp
    rw [hx']
    field_simp
  · intro m
    simp only [sub_zero, smul_eq_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    rw [← iteratedDeriv_succ']
    have hc := coeff_bound' hh hρ (n := m + 1) (by lia)
    rw [norm_div, Complex.norm_natCast, Nat.factorial_succ, Nat.cast_mul] at hc
    have hfac : (0 : ℝ) < m.factorial := by positivity
    have hρm : 0 < ρ ^ (m + 1) := pow_pos hρ _
    have hc' : ‖iteratedDeriv (m + 1) h 0‖ ≤
        2 * S * (((m : ℝ) + 1) * m.factorial) / ρ ^ (m + 1) := by
      rw [le_div_iff₀ hρm]
      have := hc
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
      push_cast at this
      linarith
    calc (m.factorial : ℝ)⁻¹ * (‖z‖ ^ m * ‖iteratedDeriv (m + 1) h 0‖)
        ≤ (m.factorial : ℝ)⁻¹ * (‖z‖ ^ m *
            (2 * S * (((m:ℝ) + 1) * m.factorial) / ρ ^ (m + 1))) := by gcongr
      _ = 2 * S / ρ * (((m : ℝ) + 1) * x ^ m) := by
        simp only [x, div_pow, pow_succ]
        field_simp

/-- Taylor coefficients of degree `> k` vanish under a growth bound on `posMean`. -/
private theorem coeff_eq_zero_of_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {A : ℝ} {k : ℕ} (h : ∀ r : ℝ, 0 < r → posMean g r ≤ A * (1 + r) ^ k)
    {n : ℕ} (hn : k < n) :
    iteratedDeriv n g 0 / n.factorial = 0 := by
  set a := iteratedDeriv n g 0 / n.factorial
  by_contra ha
  have hε : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set B := 4 * |A| * 2 ^ k + 2 * |(g 0).re|
  set ρ := max 1 ((B + 1) / ‖a‖)
  have hρ1 : 1 ≤ ρ := le_max_left _ _
  have hρ0 : 0 < ρ := by linarith
  have hc := coeff_bound' hg hρ0 (n := n) (by lia)
  have hgr := h ρ hρ0
  have h1 : (1 + ρ) ^ k ≤ 2 ^ k * ρ ^ (n - 1) := by
    calc (1 + ρ) ^ k ≤ (2 * ρ) ^ k := by gcongr; linarith
      _ = 2 ^ k * ρ ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * ρ ^ (n - 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hρ1 (by lia)) (by positivity)
  have hpn : ρ ^ n = ρ * ρ ^ (n - 1) := by
    rw [← pow_succ']; congr 1; lia
  have hpos : 0 < ρ ^ (n - 1) := pow_pos hρ0 _
  have h2 : ‖a‖ * ρ * ρ ^ (n - 1) ≤ B * ρ ^ (n - 1) := by
    have hA : A * (1 + ρ) ^ k ≤ |A| * (2 ^ k * ρ ^ (n - 1)) := by
      calc A * (1 + ρ) ^ k ≤ |A| * (1 + ρ) ^ k := by gcongr; exact le_abs_self A
        _ ≤ _ := by gcongr
    have hg0 : -(g 0).re ≤ |(g 0).re| * ρ ^ (n - 1) := by
      have : 1 ≤ ρ ^ (n - 1) := one_le_pow₀ hρ1
      nlinarith [neg_le_abs (g 0).re, abs_nonneg (g 0).re]
    rw [hpn] at hc
    simp only [B]
    nlinarith
  have h3 : ‖a‖ * ρ ≤ B := le_of_mul_le_mul_right h2 hpos
  have h4 : (B + 1) / ‖a‖ ≤ ρ := le_max_right _ _
  rw [div_le_iff₀ hε] at h4
  nlinarith

end Complex
end
end Coeff_part

section Borel_part


/-!
# An elementary Borel growth lemma and absorption of logarithmic error terms
-/


open Real


namespace Complex

/-- Elementary form of Borel's growth lemma: for monotone `V ≥ 1`, every interval `[r, r+2]`
contains a point `s` with `V (s + 1 / V s) ≤ 2 V s`. -/
theorem borel_growth {V : ℝ → ℝ} (hmono : Monotone V) (h1 : ∀ r, 1 ≤ V r) (r : ℝ) :
    ∃ s ∈ Set.Icc r (r + 2), V (s + 1 / V s) ≤ 2 * V s := by
  by_contra H
  push Not at H
  let s : ℕ → ℝ := fun n => Nat.rec r (fun _ x => x + 1 / V x) n
  have hsS : ∀ n, s (n + 1) = s n + 1 / V (s n) := fun n => rfl
  have key : ∀ n, (r ≤ s n ∧ s n ≤ r + 2 - 2 / 2 ^ n) ∧ (2:ℝ) ^ n ≤ V (s n) := by
    intro n
    induction n with
    | zero => simp [s, h1 r]
    | succ n ih =>
      obtain ⟨⟨ha, hb⟩, hc⟩ := ih
      have hVpos : 0 < V (s n) := lt_of_lt_of_le one_pos (h1 _)
      have hinv : 1 / V (s n) ≤ 1 / 2 ^ n := one_div_le_one_div_of_le (by positivity) hc
      have hmem : s n ∈ Set.Icc r (r + 2) := ⟨ha, by
        nlinarith [show 0 ≤ 2 / (2:ℝ) ^ n by positivity]⟩
      have hlt := H (s n) hmem
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hsS]
        have : 0 ≤ 1 / V (s n) := by positivity
        linarith
      · rw [hsS, pow_succ]
        have : 2 / ((2:ℝ) ^ n * 2) = 1 / 2 ^ n := by field_simp
        rw [this]
        have : 2 / (2:ℝ) ^ n = 2 * (1 / 2 ^ n) := by ring
        rw [this] at hb
        linarith
      · rw [hsS, pow_succ]; linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (V (r + 2)) (by norm_num : (1:ℝ) < 2)
  have := (key n).2
  have hle : V (s n) ≤ V (r + 2) := hmono (by
    have := (key n).1.2
    nlinarith [show 0 ≤ 2 / (2:ℝ) ^ n by positivity])
  linarith

private theorem log_le_div_twelve_add {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 12 + 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 12 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  have h12 : Real.log 12 < 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 12 / 8 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at this
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  linarith

/-- The algebraic core: the displayed logarithmic inequality with `x, t ≥ 1` forces
`x ≤ (200 + 20 C)(1+t)²`. -/
private theorem absorb_log {x t C : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (h : x - 1 ≤ 2 * Real.log (2 + 2 * (t + 1) * x ^ 2 * (8 * x + C * (t + 2) ^ 2)) +
      C * (1 + t) ^ 2) :
    x ≤ (200 + 20 * C) * (1 + t) ^ 2 := by
  set W := 2 + 2 * (t + 1) * (8 + C * (t + 2) ^ 2)
  have hW1 : 1 ≤ W := by
    have : 0 ≤ 2 * (t + 1) * (8 + C * (t + 2) ^ 2) := by positivity
    simp only [W]; linarith
  have harg : 2 + 2 * (t + 1) * x ^ 2 * (8 * x + C * (t + 2) ^ 2) ≤ x ^ 3 * W := by
    simp only [W]
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
    have hx3 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx (by norm_num)
    have hx3' : x ^ 2 * x = x ^ 3 := by ring
    have hCt : 0 ≤ C * (t + 2) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx3
      (by positivity : (0 : ℝ) ≤ 2 * (t + 1) * (C * (t + 2) ^ 2))
    nlinarith
  have hpos : 0 < 2 + 2 * (t + 1) * x ^ 2 * (8 * x + C * (t + 2) ^ 2) := by positivity
  have hlog1 : Real.log (2 + 2 * (t + 1) * x ^ 2 * (8 * x + C * (t + 2) ^ 2)) ≤
      3 * Real.log x + Real.log W := by
    calc _ ≤ Real.log (x ^ 3 * W) := Real.log_le_log hpos harg
      _ = 3 * Real.log x + Real.log W := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num
  have hlogx := log_le_div_twelve_add (show 0 < x by linarith)
  have hWle : W ≤ (18 + 2 * C) * (t + 2) ^ 3 := by
    simp only [W]
    have : 1 ≤ (t + 2) ^ 3 := one_le_pow₀ (by linarith)
    have h2 : (t + 1) ≤ (t + 2) := by linarith
    have h3 : (t + 1) * (t + 2) ^ 2 ≤ (t + 2) ^ 3 := by
      calc _ ≤ (t + 2) * (t + 2) ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring
    have h4 : t + 1 ≤ (t + 2) ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hC]
  have hlogW : Real.log W ≤ (18 + 2 * C) + 3 * (t + 2) := by
    calc Real.log W ≤ Real.log ((18 + 2 * C) * (t + 2) ^ 3) :=
          Real.log_le_log (by linarith) hWle
      _ = Real.log (18 + 2 * C) + 3 * Real.log (t + 2) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num
      _ ≤ (18 + 2 * C) + 3 * (t + 2) := by
          have a1 := Real.log_le_sub_one_of_pos (show 0 < 18 + 2 * C by positivity)
          have a2 := Real.log_le_sub_one_of_pos (show 0 < t + 2 by positivity)
          linarith
  nlinarith [show t + 2 ≤ (1 + t) ^ 2 by nlinarith,
    show 1 ≤ (1 + t) ^ 2 by nlinarith]

/-- From the "growth inequality" (the output of the Nevanlinna-type estimate) to a quadratic
bound, via the sup-majorant and the elementary Borel lemma. -/
theorem growth_of_GI {T : ℝ → ℝ} (hT0 : ∀ r, 0 ≤ T r)
    (hbdd : ∀ R, ∃ B, ∀ r ∈ Set.Ioc 0 R, T r ≤ B) {C : ℝ} (hC : 0 ≤ C)
    (hGI : ∀ r ρ, 1 ≤ r → r < ρ →
      T r ≤ 2 * Real.log (2 + 2 * ρ / (ρ - r) ^ 2 * (4 * T ρ + C * (1 + ρ) ^ 2)) +
        C * (1 + r) ^ 2) :
    ∃ A, ∀ r, 0 < r → T r ≤ A * (1 + r) ^ 2 := by
  have hbddI : ∀ R, BddAbove (T '' Set.Icc 1 R) := by
    intro R
    obtain ⟨B, hB⟩ := hbdd R
    exact ⟨B, by rintro _ ⟨s, hs, rfl⟩; exact hB s ⟨by linarith [hs.1], hs.2⟩⟩
  let U : ℝ → ℝ := fun r => sSup (T '' Set.Icc 1 (max r 1))
  have hne : ∀ r, (T '' Set.Icc 1 (max r 1)).Nonempty :=
    fun r => ⟨T 1, 1, ⟨le_refl _, le_max_right _ _⟩, rfl⟩
  have hUmono : Monotone U := by
    intro r r' hrr'; apply csSup_le_csSup (hbddI _) (hne r)
    exact Set.image_mono (Set.Icc_subset_Icc (le_refl _) (max_le_max hrr' (le_refl _)))
  have hTU : ∀ r, 1 ≤ r → T r ≤ U r := by
    intro r hr; apply le_csSup (hbddI _)
    exact ⟨r, ⟨hr, le_max_left _ _⟩, rfl⟩
  have hU0 : ∀ r, 0 ≤ U r := fun r =>
    le_trans (hT0 1) (le_csSup (hbddI _) ⟨1, ⟨le_refl _, le_max_right _ _⟩, rfl⟩)
  have hUGI : ∀ r ρ, 1 ≤ r → r < ρ →
      U r ≤ 2 * Real.log (2 + 2 * ρ / (ρ - r) ^ 2 * (4 * U ρ + C * (1 + ρ) ^ 2)) +
        C * (1 + r) ^ 2 := by
    intro r ρ hr hrρ; apply csSup_le (hne r)
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
    rw [max_eq_left hr] at hs2
    have hsρ : s < ρ := lt_of_le_of_lt hs2 hrρ
    refine (hGI s ρ hs1 hsρ).trans ?_
    have hρ0 : 0 < ρ := by linarith
    have hTρ : T ρ ≤ U ρ := hTU ρ (by linarith)
    have hd : (ρ - r) ^ 2 ≤ (ρ - s) ^ 2 := by
      have : 0 < ρ - r := by linarith
      nlinarith
    have hdr : 0 < (ρ - r) ^ 2 := pow_pos (by linarith) 2
    have hq : 2 * ρ / (ρ - s) ^ 2 ≤ 2 * ρ / (ρ - r) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hdr hd
    have hinner : 0 ≤ 4 * T ρ + C * (1 + ρ) ^ 2 := by
      have := hT0 ρ; positivity
    have harg1 : 0 < 2 + 2 * ρ / (ρ - s) ^ 2 * (4 * T ρ + C * (1 + ρ) ^ 2) := by
      have := hT0 ρ; positivity
    have harg : 2 + 2 * ρ / (ρ - s) ^ 2 * (4 * T ρ + C * (1 + ρ) ^ 2) ≤
        2 + 2 * ρ / (ρ - r) ^ 2 * (4 * U ρ + C * (1 + ρ) ^ 2) := by
      have : 0 ≤ 2 * ρ / (ρ - s) ^ 2 := by positivity
      gcongr
    have hlog := Real.log_le_log harg1 harg
    have hsq : (1 + s) ^ 2 ≤ (1 + r) ^ 2 := by
      have : 0 ≤ 1 + s := by linarith
      gcongr
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  let V : ℝ → ℝ := fun r => U r + 1
  have hVmono : Monotone V := fun a b hab => by simp only [V]; linarith [hUmono hab]
  have hV1 : ∀ r, 1 ≤ V r := fun r => by simp only [V]; linarith [hU0 r]
  set A' := (200 + 20 * C)
  have hmain : ∀ r, 1 ≤ r → T r ≤ 9 * A' * (1 + r) ^ 2 := by
    intro r hr
    obtain ⟨s, ⟨hs1, hs2⟩, hsV⟩ := borel_growth hVmono hV1 r
    have hs1' : 1 ≤ s := le_trans hr hs1
    set x := V s
    have hx1 : 1 ≤ x := hV1 s
    set ρ := s + 1 / x
    have hρs : s < ρ := lt_add_of_pos_right s (by positivity)
    have hρle : ρ ≤ s + 1 := by
      simp only [ρ]
      nlinarith [one_div_le_one_div_of_le one_pos hx1]
    have hGIs := hUGI s ρ hs1' hρs
    have hdiff : ρ - s = 1 / x := by simp only [ρ]; ring
    have hfac : 2 * ρ / (ρ - s) ^ 2 = 2 * ρ * x ^ 2 := by rw [hdiff]; field_simp
    rw [hfac] at hGIs
    have hUρ : U ρ ≤ 2 * x - 1 := by
      simp only [V] at hsV; linarith
    have hx_eq : U s = x - 1 := by simp only [x, V]; ring
    have harg1 : 0 < 2 + 2 * ρ * x ^ 2 * (4 * U ρ + C * (1 + ρ) ^ 2) := by
      have := hU0 ρ
      have : 0 < ρ := by linarith
      positivity
    have harg : 2 + 2 * ρ * x ^ 2 * (4 * U ρ + C * (1 + ρ) ^ 2) ≤
        2 + 2 * (s + 1) * x ^ 2 * (8 * x + C * (s + 2) ^ 2) := by
      have hρ0 : 0 ≤ ρ := by linarith
      have h1 : 4 * U ρ + C * (1 + ρ) ^ 2 ≤ 8 * x + C * (s + 2) ^ 2 := by
        have : (1 + ρ) ^ 2 ≤ (s + 2) ^ 2 := by
          have : 0 ≤ 1 + ρ := by linarith
          exact pow_le_pow_left₀ this (by linarith) 2
        nlinarith [mul_le_mul_of_nonneg_left this hC]
      have h0 : 0 ≤ 4 * U ρ + C * (1 + ρ) ^ 2 := by have := hU0 ρ; positivity
      have : 2 * ρ * x ^ 2 ≤ 2 * (s + 1) * x ^ 2 := by gcongr
      have h2 : 0 ≤ 2 * ρ * x ^ 2 := by positivity
      nlinarith [mul_le_mul this h1 h0 (by positivity)]
    have hlog := Real.log_le_log harg1 harg
    have hx_bound : x ≤ A' * (1 + s) ^ 2 := by
      apply absorb_log hx1 hs1' hC
      rw [hx_eq] at hGIs; linarith
    calc T r ≤ U r := hTU r hr
      _ ≤ U s := hUmono hs1
      _ ≤ x := by simp only [x, V]; linarith
      _ ≤ A' * (1 + s) ^ 2 := hx_bound
      _ ≤ A' * (3 * (1 + r)) ^ 2 := by
          have : 0 ≤ A' := by simp only [A']; positivity
          gcongr
          linarith
      _ = 9 * A' * (1 + r) ^ 2 := by ring
  obtain ⟨B, hB⟩ := hbdd 1
  refine ⟨max (9 * A') (max B 0), fun r hr => ?_⟩
  rcases le_or_gt 1 r with h1 | h1
  · refine (hmain r h1).trans ?_
    gcongr; exact le_max_left _ _
  · have hTr := hB r ⟨hr, h1.le⟩
    have hsq : 1 ≤ (1 + r) ^ 2 := by nlinarith
    have : B ≤ max (9 * A') (max B 0) := le_trans (le_max_left _ _) (le_max_right _ _)
    have h0 : 0 ≤ max (9 * A') (max B 0) := le_trans (le_max_right _ _) (le_max_right _ _)
    nlinarith

end Complex
end Borel_part



open Complex Filter Topology

noncomputable section

namespace Complex

/-- **Polynomial lemma** (Nevanlinna-type, elementary: Fourier coefficients of `Re g` on
circles / Borel–Carathéodory + Cauchy estimates). An entire function whose positive-part circle
mean of the real part grows at most like `A (1 + r)^k` is a polynomial of degree `≤ k`. -/
theorem poly_of_mean_pos_re_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {A : ℝ} {k : ℕ}
    (h : ∀ r : ℝ, 0 < r →
      Real.circleAverage (fun z => max (g z).re 0) 0 r ≤ A * (1 + r) ^ k) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ k ∧ ∀ z, g z = p.eval z := by
  refine ⟨∑ n ∈ Finset.range (k + 1),
    Polynomial.C (iteratedDeriv n g 0 / n.factorial) * Polynomial.X ^ n, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  · intro z
    rw [← Complex.taylorSeries_eq_of_entire' 0 z hg, Polynomial.eval_finsetSum]
    rw [tsum_eq_sum (s := Finset.range (k + 1))]
    · apply Finset.sum_congr rfl
      intro n _
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        sub_zero]; ring
    · intro n hn
      have hn' : ¬ n < k + 1 := fun hlt => hn (Finset.mem_range.mpr hlt)
      have hnk : k < n := by lia
      have := coeff_eq_zero_of_growth hg h hnk
      rw [div_eq_inv_mul] at this
      simp [this]

end Complex

