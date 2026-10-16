/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import RealRooted.Mathlib.Analysis.Complex.EntireExponentialType
public import RealRooted.Mathlib.Analysis.Complex.WeierstrassProduct
public import RealRooted.Mathlib.Analysis.Complex.ZeroCounting

/-!
# Hadamard factorization for entire functions of exponential type

This file proves genus-one Hadamard factorization for an entire function of exponential type
whose zeros are enumerated with multiplicity. It also gives the finite-zero factorization.
-/

public noncomputable section

open Complex Filter Topology
open MeromorphicOn

namespace Differentiable

open Complex

private lemma order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (w : ℂ) :
    analyticOrderAt f w ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr h0)]; simp)

private lemma fibre_card_le {ι : Type*} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {z : ι → ℂ}
    (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) (s : Finset ι) {r : ℝ}
    {u : ℂ} (hu : ‖u‖ ≤ r) [DecidablePred (fun k => z k = u)] :
    ((s.filter (fun k => z k = u)).card : ℤ) ≤ divisor f (Metric.closedBall 0 r) u := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  rw [divisor_apply (ha.mono (Set.subset_univ _)).meromorphicOn (by simpa using hu),
    (hf.analyticAt u).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (order_ne_top hf h0 u)
  rw [← hn]
  simp only [ENat.map_natCast, WithTop.untop₀_coe]
  have : ((s.filter (fun k => z k = u)).card : ℕ∞) ≤ n := by
    rw [hn, hz u, ← Set.encard_coe_eq_coe_finsetCard]
    apply Set.encard_le_encard
    intro k hk
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hk ⊢
    exact hk.2
  exact_mod_cast this

private lemma count_le_divisor {ι : Type*} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0)
    {z : ι → ℂ} (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w})
    (s : Finset ι) (r : ℝ) :
    ((s.filter (fun k => ‖z k‖ ≤ r)).card : ℤ) ≤
      ∑ᶠ u, divisor f (Metric.closedBall 0 r) u := by
  classical
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  set D := divisor f (Metric.closedBall (0 : ℂ) r)
  have hDnn : ∀ u, 0 ≤ D u := fun u => (ha.mono (Set.subset_univ _)).divisor_nonneg u
  have hfin := D.finiteSupport (isCompact_closedBall 0 r)
  set s' := s.filter (fun k => ‖z k‖ ≤ r)
  set T := s'.image z
  rw [Finset.card_eq_sum_card_image z s']
  push_cast
  calc ∑ b ∈ T, (({a ∈ s' | z a = b}.card : ℕ) : ℤ)
      ≤ ∑ b ∈ T, D b := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
        refine le_trans ?_ (fibre_card_le hf h0 hz s (Finset.mem_filter.1 hk).2)
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    _ ≤ ∑ b ∈ T ∪ hfin.toFinset, D b :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hDnn i)
    _ = ∑ᶠ u, D u := by
        rw [finsum_eq_sum_of_support_subset (s := T ∪ hfin.toFinset)]
        intro u hu
        simp only [Finset.coe_union, Set.Finite.coe_toFinset]
        exact Or.inr hu
private theorem exists_entire_quotient {f P : ℂ → ℂ} (hf : Differentiable ℂ f) (hP :
  Differentiable ℂ P)
    (hf0 : f 0 ≠ 0) (hord : ∀ w, analyticOrderAt f w = analyticOrderAt P w) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ w, G w ≠ 0) ∧
      ∀ w, f w = G w * P w := by
  have hfa : ∀ w, AnalyticAt ℂ f w := fun w => hf.analyticAt w
  have hPa : ∀ w, AnalyticAt ℂ P w := fun w => hP.analyticAt w
  have hfin : ∀ w, analyticOrderAt f w ≠ ⊤ := fun w => order_ne_top hf hf0 w
  set q : ℂ → ℂ := f * P⁻¹ with hqdef
  have hq : MeromorphicOn q Set.univ := fun w _ =>
    (hfa w).meromorphicAt.mul (hPa w).meromorphicAt.inv
  set G := toMeromorphicNFOn q Set.univ with hGdef
  have hGnf : MeromorphicNFOn G Set.univ := meromorphicNFOn_toMeromorphicNFOn q Set.univ
  have hordq : ∀ w, meromorphicOrderAt q w = 0 := by
    intro w
    rw [hqdef, meromorphicOrderAt_mul (hfa w).meromorphicAt (hPa w).meromorphicAt.inv,
      meromorphicOrderAt_inv, (hfa w).meromorphicOrderAt_eq, (hPa w).meromorphicOrderAt_eq,
      ← hord w]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hfin w)
    rw [← hn]
    simp
  have hordG : ∀ w, meromorphicOrderAt G w = 0 := fun w => by
    rw [hGdef, meromorphicOrderAt_toMeromorphicNFOn hq (Set.mem_univ w), hordq]
  have hGa : ∀ w, AnalyticAt ℂ G w := fun w =>
    (hGnf (Set.mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.1 (hordG w).ge
  refine ⟨G, fun w => (hGa w).differentiableAt,
    fun w => (hGnf (Set.mem_univ w)).meromorphicOrderAt_eq_zero_iff.1 (hordG w), fun w => ?_⟩
  have h2 : ∀ᶠ x in 𝓝[≠] w, P x ≠ 0 := by
    exact ((hPa w).eventually_eq_zero_or_eventually_ne_zero).resolve_left fun hz =>
      hfin w (by rw [hord w]; exact analyticOrderAt_eq_top.2 hz)
  have hev : G * P =ᶠ[𝓝[≠] w] f := by
    have h1 := hq.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ w)
    filter_upwards [h1, h2] with x hx hx2
    simp only [Pi.mul_apply]
    rw [← hGdef] at hx
    simp [hx, hqdef, hx2]
  exact (tendsto_nhds_unique
    (((hGa w).mul (hPa w)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' hev)
    ((hfa w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).symm

/-- Common core: if `f = G P` with `G` zero-free and `P` bounded below on suitable circles,
then `f = exp (a w) P`. -/
private theorem eq_exp_mul_of_lower_bound {f P : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hP : Differentiable ℂ P) (h0 : f 0 = 1) (hP0 : P 0 = 1) {C : ℝ}
    (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖)))
    (hord : ∀ w, analyticOrderAt f w = analyticOrderAt P w)
    (hlow : ∃ B D : ℝ, ∀ x : ℝ, 0 ≤ x → ∃ R, x ≤ R ∧ R ≤ x + D ∧
      ∀ w : ℂ, ‖w‖ = R → Real.exp (-(B * (1 + R) ^ (3 / 2 : ℝ))) ≤ ‖P w‖) :
    ∃ a : ℂ, ∀ w, f w = Complex.exp (a * w) * P w := by
  obtain ⟨B, D, hBD⟩ := hlow
  have hf0 : f 0 ≠ 0 := by rw [h0]; exact one_ne_zero
  obtain ⟨G, hG, hGne, hfG⟩ := exists_entire_quotient hf hP hf0 hord
  set K := |C| + |B| with hK
  have hcirc : ∀ x : ℝ, 0 ≤ x → ∃ R, x ≤ R ∧ R ≤ x + D ∧
      ∀ w : ℂ, ‖w‖ = R → ‖G w‖ ≤ Real.exp (K * (1 + R) ^ (3 / 2 : ℝ)) := by
    intro x hx
    obtain ⟨R, hxR, hRD, hw⟩ := hBD x hx
    refine ⟨R, hxR, hRD, fun w hwR => ?_⟩
    have hR0 : 0 ≤ R := hx.trans hxR
    have hPw := hw w hwR
    have hfw := h w
    rw [hfG w, norm_mul, hwR] at hfw
    have h1 : ‖G w‖ * Real.exp (-(B * (1 + R) ^ (3 / 2 : ℝ))) ≤ Real.exp (C * (1 + R)) :=
      (mul_le_mul_of_nonneg_left hPw (norm_nonneg _)).trans hfw
    have h2 : ‖G w‖ ≤ Real.exp (C * (1 + R) + B * (1 + R) ^ (3 / 2 : ℝ)) := by
      rw [Real.exp_add]
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (B * (1 + R) ^ (3 / 2 : ℝ))).le
      rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
    refine h2.trans (Real.exp_le_exp.2 ?_)
    have hp1 : (1 + R) ≤ (1 + R) ^ (3 / 2 : ℝ) :=
      Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
    have hpos : 0 ≤ (1 + R) ^ (3 / 2 : ℝ) := by positivity
    have e1 : C * (1 + R) ≤ |C| * (1 + R) ^ (3 / 2 : ℝ) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)).trans
        (mul_le_mul_of_nonneg_left hp1 (abs_nonneg C))
    have e2 : B * (1 + R) ^ (3 / 2 : ℝ) ≤ |B| * (1 + R) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self B) hpos
    rw [hK]; linarith
  set K' := K * (1 + |D|) ^ (3 / 2 : ℝ) with hK'
  have hglob : ∀ w : ℂ, ‖G w‖ ≤ Real.exp (K' * (1 + ‖w‖) ^ (3 / 2 : ℝ)) := by
    intro w
    obtain ⟨R, hxR, hRD, hw⟩ := hcirc ‖w‖ (norm_nonneg w)
    have hR0 : 0 ≤ R := (norm_nonneg w).trans hxR
    have hGR : ‖G w‖ ≤ Real.exp (K * (1 + R) ^ (3 / 2 : ℝ)) := by
      rcases eq_or_lt_of_le hxR with hEq | hlt
      · exact hw w hEq
      · have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg w) hlt
        apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) R)
          Metric.isBounded_ball hG.diffContOnCl
        · intro y hy
          rw [frontier_ball (0 : ℂ) hRpos.ne'] at hy
          exact hw y (by simpa using hy)
        · rw [closure_ball (0 : ℂ) hRpos.ne']
          simpa using hxR
    refine hGR.trans (Real.exp_le_exp.2 ?_)
    have hK0 : 0 ≤ K := by positivity
    have hD : R ≤ ‖w‖ + |D| := hRD.trans (by linarith [le_abs_self D])
    have : (1 + R) ^ (3 / 2 : ℝ) ≤
        (1 + |D|) ^ (3 / 2 : ℝ) * (1 + ‖w‖) ^ (3 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      nlinarith [abs_nonneg D, norm_nonneg w]
    rw [hK', mul_assoc]
    exact mul_le_mul_of_nonneg_left this hK0
  obtain ⟨L, hL, hLG⟩ := hG.exists_log_of_ne_zero hGne
  have hre : ∀ z, (L z).re ≤ K' * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
    intro z
    have hz := hglob z
    rw [← hLG z, Complex.norm_exp] at hz
    exact Real.exp_le_exp.mp hz
  obtain ⟨a, b, hab⟩ := exists_affine_of_re_le_rpow hL hre
  have hG0 : G 0 = 1 := by
    have := hfG 0
    simpa [h0, hP0] using this.symm
  have hb : Complex.exp b = 1 := by
    rw [← hG0, ← hLG 0, hab 0]; simp
  refine ⟨a, fun w => ?_⟩
  rw [hfG w, ← hLG w, hab w, Complex.exp_add, hb, mul_one]

/-! ### Lower bound for the genus-one product -/

private theorem log_norm_weierstrassFactorOne_ge {u : ℂ} (hu : u ≠ 1) :
    -(2 * ‖u‖ ^ (3 / 2 : ℝ)) +
        (if 1 / 2 ≤ ‖u‖ then min 0 (Real.log ‖1 - u‖) else 0) ≤
      Real.log ‖weierstrassFactorOne u‖ := by
  by_cases hs : 1 / 2 ≤ ‖u‖
  · rw [ite_eq_left hs]
    have hne : 1 - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
    have e : Real.log ‖weierstrassFactorOne u‖ = Real.log ‖1 - u‖ + u.re := by
      unfold weierstrassFactorOne
      rw [norm_mul, Complex.norm_exp, Real.log_mul (norm_ne_zero_iff.2 hne) (Real.exp_pos _).ne',
        Real.log_exp]
    rw [e]
    have h1 : -‖u‖ ≤ u.re := by
      linarith [Complex.abs_re_le_norm u, neg_abs_le u.re]
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    have h2 : ‖u‖ ≤ 2 * ‖u‖ ^ (3 / 2 : ℝ) := by
      have e2 : ‖u‖ ^ (3 / 2 : ℝ) = ‖u‖ * ‖u‖ ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hu0 (by norm_num)]; norm_num
      have h3 : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) (by norm_num)
      have h4 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ ‖u‖ ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hs (by norm_num)
      rw [e2]; nlinarith
    have h5 := min_le_right 0 (Real.log ‖1 - u‖)
    linarith
  · rw [ite_eq_right hs]
    push Not at hs
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    have hle1 : ‖u‖ ≤ 1 := by linarith
    have hb := Complex.norm_weierstrassFactorOne_sub_one_le hle1
    have hsq : ‖u‖ ^ 2 ≤ 1 / 4 := by nlinarith
    have hlow : 1 - ‖u‖ ^ 2 ≤ ‖weierstrassFactorOne u‖ := by
      have := norm_sub_norm_le (1 : ℂ) (weierstrassFactorOne u)
      rw [norm_one, norm_sub_rev] at this
      linarith
    have hpos : 0 < 1 - ‖u‖ ^ 2 := by linarith
    have hlog : -(2 * ‖u‖ ^ 2) ≤ Real.log (1 - ‖u‖ ^ 2) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      have h6 : -(2 * ‖u‖ ^ 2) ≤ 1 - (1 - ‖u‖ ^ 2)⁻¹ := by
        have h7 : 1 / (1 - ‖u‖ ^ 2) ≤ 1 + 2 * ‖u‖ ^ 2 := by
          rw [div_le_iff₀ hpos]; nlinarith
        rw [one_div] at h7
        linarith
      linarith
    have hmono := Real.log_le_log hpos hlow
    have hpow : ‖u‖ ^ 2 ≤ ‖u‖ ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hu0 hle1 (by norm_num) (by norm_num)
    linarith

private theorem exists_gap (M : Finset ℝ) (a : ℝ) :
    ∃ R ∈ Set.Icc a (a + 1), ∀ m ∈ M, 1 / (4 * ((M.card : ℝ) + 1)) ≤ |R - m| := by
  set ε := 1 / (4 * ((M.card : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  by_contra hcon
  push Not at hcon
  have hsub : Set.Icc a (a + 1) ⊆ ⋃ m ∈ M, Set.Ioo (m - ε) (m + ε) := by
    intro R hR
    obtain ⟨m, hm, hlt⟩ := hcon R hR
    simp only [Set.mem_iUnion]
    rw [abs_lt] at hlt
    exact ⟨m, hm, by constructor <;> linarith⟩
  have h1 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
  have h2 := MeasureTheory.measure_biUnion_finset_le (μ := MeasureTheory.volume) M
    (fun m => Set.Ioo (m - ε) (m + ε))
  have h3 : ∑ m ∈ M, MeasureTheory.volume (Set.Ioo (m - ε) (m + ε)) =
      ENNReal.ofReal ((M.card : ℝ) * (2 * ε)) := by
    simp only [Real.volume_Ioo]
    rw [Finset.sum_congr rfl (g := fun _ => ENNReal.ofReal (2 * ε)) (fun m _ => by ring_nf),
      Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
  have h4 := h1.trans (h2.trans h3.le)
  rw [Real.volume_Icc, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h4
  have h5 : (M.card : ℝ) * (2 * ε) < 1 := by
    rw [hε]
    field_simp
    linarith [show (0 : ℝ) < (M.card : ℝ) + 1 by positivity]
  linarith

private theorem finite_of_count {z : ℕ → ℂ} {A : ℝ}
    (hcount : ∀ s : Finset ℕ, ∀ r : ℝ, 1 ≤ r →
      ((s.filter (fun k => ‖z k‖ ≤ r)).card : ℝ) ≤ A * r) (r : ℝ) :
    {k | ‖z k‖ ≤ r}.Finite := by
  classical
  by_contra hinf
  set r' := max r 1 with hr'
  obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈A * r'⌉₊ + 1)
  have h1 := hcount t r' (le_max_right _ _)
  have hfilt : t.filter (fun k => ‖z k‖ ≤ r') = t :=
    Finset.filter_true_of_mem fun k hk =>
      (show ‖z k‖ ≤ r from ht hk).trans (le_max_left _ _)
  rw [hfilt, hcard] at h1
  push_cast at h1
  linarith [Nat.le_ceil (A * r')]

private theorem weierstrassFactorOne_ne_zero {u : ℂ} (hu : u ≠ 1) :
    weierstrassFactorOne u ≠ 0 :=
  mul_ne_zero (sub_ne_zero.2 (Ne.symm hu)) (Complex.exp_ne_zero u)

private theorem log_norm_partial_prod_ge {z : ℕ → ℂ} (hz : ∀ k, z k ≠ 0)
    (hS : Summable fun k => ‖z k‖ ^ (-(3 / 2 : ℝ))) {T : Finset ℕ} {R ε : ℝ} (hR : 0 < R)
    (hε : 0 < ε) (hε1 : ε ≤ 2 * R)
    (hT : ∀ k, ‖z k‖ ≤ 2 * R → k ∈ T) (hgap : ∀ k, ε ≤ |R - ‖z k‖|)
    {w : ℂ} (hw : ‖w‖ = R)
    (s : Finset ℕ) :
    -(2 * R ^ (3 / 2 : ℝ) * ∑' k, ‖z k‖ ^ (-(3 / 2 : ℝ))) +
        T.card * Real.log (ε / (2 * R)) ≤
      Real.log ‖∏ k ∈ s, weierstrassFactorOne (w / z k)‖ := by
  classical
  have hne1 : ∀ k, w / z k ≠ 1 := by
    intro k hk
    rw [div_eq_one_iff_eq (hz k)] at hk
    have := hgap k
    rw [← hk, hw, sub_self, abs_zero] at this
    linarith
  set c := Real.log (ε / (2 * R)) with hc
  have hc0 : c ≤ 0 := Real.log_nonpos (by positivity) (by rw [div_le_one (by positivity)]; exact
    hε1)
  rw [norm_prod, Real.log_prod (fun k _ => norm_ne_zero_iff.2 (weierstrassFactorOne_ne_zero
    (hne1 k)))]
  have hterm : ∀ k ∈ s, -(2 * (R ^ (3 / 2 : ℝ) * ‖z k‖ ^ (-(3 / 2 : ℝ)))) +
      (if k ∈ T then c else 0) ≤ Real.log ‖weierstrassFactorOne (w / z k)‖ := by
    intro k _
    have hzk : 0 < ‖z k‖ := norm_pos_iff.2 (hz k)
    have hb := log_norm_weierstrassFactorOne_ge (hne1 k)
    have hnorm : ‖w / z k‖ = R / ‖z k‖ := by rw [norm_div, hw]
    have hpow : ‖w / z k‖ ^ (3 / 2 : ℝ) =
        R ^ (3 / 2 : ℝ) * ‖z k‖ ^ (-(3 / 2 : ℝ)) := by
      rw [hnorm, Real.div_rpow hR.le hzk.le, Real.rpow_neg hzk.le, div_eq_mul_inv]
    rw [hpow] at hb
    refine le_trans ?_ hb
    apply add_le_add_right
    by_cases hh : 1 / 2 ≤ ‖w / z k‖
    · rw [ite_eq_left hh]
      have hk2 : ‖z k‖ ≤ 2 * R := by
        rw [hnorm, le_div_iff₀ hzk] at hh; linarith
      rw [ite_eq_left (hT k hk2)]
      apply le_min hc0
      have hlow : ε / (2 * R) ≤ ‖1 - w / z k‖ := by
        have e : 1 - w / z k = (z k - w) / z k := by rw [sub_div, div_self (hz k)]
        rw [e, norm_div]
        have h1 : ε ≤ ‖z k - w‖ := by
          have := hgap k
          have h2 : |R - ‖z k‖| ≤ ‖z k - w‖ := by
            rw [← hw, abs_sub_comm]; exact abs_norm_sub_norm_le _ _
          linarith
        calc ε / (2 * R) ≤ ε / ‖z k‖ := div_le_div_of_nonneg_left hε.le hzk hk2
          _ ≤ ‖z k - w‖ / ‖z k‖ := div_le_div_of_nonneg_right h1 hzk.le
      exact Real.log_le_log (by positivity) hlow
    · rw [ite_eq_right hh]
      split_ifs <;> linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hS1 : ∑ k ∈ s, ‖z k‖ ^ (-(3 / 2 : ℝ)) ≤ ∑' k, ‖z k‖ ^ (-(3 / 2 : ℝ)) :=
    hS.sum_le_tsum s (fun k _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hcard : ((s ∩ T).card : ℝ) ≤ T.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hRp : 0 ≤ R ^ (3 / 2 : ℝ) := by positivity
  have h1 : (T.card : ℝ) * c ≤ (s ∩ T).card * c := mul_le_mul_of_nonpos_right hcard hc0
  have h2 : R ^ (3 / 2 : ℝ) * ∑ k ∈ s, ‖z k‖ ^ (-(3 / 2 : ℝ)) ≤
      R ^ (3 / 2 : ℝ) * ∑' k, ‖z k‖ ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hS1 hRp
  linarith

private theorem numeric_bound {A t R N : ℝ} (hA : 0 ≤ A) (ht : 1 ≤ t)
    (hR : 0 < R) (hRt : R ≤ t)
    (hN0 : 0 ≤ N) (hN : N ≤ 3 * A * t) :
    N * Real.log (8 * R * (N + 1)) ≤
      3 * A * (Real.log (8 * (3 * A + 1)) + 4) * t ^ (3 / 2 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hy : 8 * R * (N + 1) ≤ 8 * (3 * A + 1) * t ^ 2 := by
    have h1 : N + 1 ≤ (3 * A + 1) * t := by nlinarith
    calc 8 * R * (N + 1) ≤ 8 * t * ((3 * A + 1) * t) := by
          apply mul_le_mul (by linarith) h1 (by linarith) (by positivity)
      _ = 8 * (3 * A + 1) * t ^ 2 := by ring
  have hlog1 : Real.log (8 * R * (N + 1)) ≤ Real.log (8 * (3 * A + 1)) + 2 * Real.log t := by
    have := Real.log_le_log (by positivity) hy
    rwa [Real.log_mul (show (8 * (3 * A + 1) : ℝ) ≠ 0 by positivity)
      (show t ^ 2 ≠ 0 by positivity), Real.log_pow] at this
  have hlogt : Real.log t ≤ 2 * t ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith [show t ^ (1 / 2 : ℝ) / (1 / 2) = 2 * t ^ (1 / 2 : ℝ) by ring]
  have hc1 : 0 ≤ Real.log (8 * (3 * A + 1)) := Real.log_nonneg (by nlinarith)
  have hsq : 1 ≤ t ^ (1 / 2 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hlog2 : Real.log (8 * R * (N + 1)) ≤
      (Real.log (8 * (3 * A + 1)) + 4) * t ^ (1 / 2 : ℝ) := by
    nlinarith
  have hpos : 0 ≤ (Real.log (8 * (3 * A + 1)) + 4) * t ^ (1 / 2 : ℝ) := by positivity
  have e : t ^ (3 / 2 : ℝ) = t * t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' ht0.le (by norm_num)]; norm_num
  calc N * Real.log (8 * R * (N + 1))
      ≤ N * ((Real.log (8 * (3 * A + 1)) + 4) * t ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2 hN0
    _ ≤ (3 * A * t) * ((Real.log (8 * (3 * A + 1)) + 4) * t ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hN hpos
    _ = 3 * A * (Real.log (8 * (3 * A + 1)) + 4) * t ^ (3 / 2 : ℝ) := by rw [e]; ring

private theorem lower_bound_prod {z : ℕ → ℂ} (hz : ∀ k, z k ≠ 0) {A : ℝ}
    (hcount : ∀ s : Finset ℕ, ∀ r : ℝ, 1 ≤ r →
      ((s.filter (fun k => ‖z k‖ ≤ r)).card : ℝ) ≤ A * r)
    (hS : Summable fun k => ‖z k‖ ^ (-(3 / 2 : ℝ))) {F : ℂ → ℂ}
    (hF : ∀ w, HasProd (fun k => weierstrassFactorOne (w / z k)) (F w)) :
    ∃ B D : ℝ, ∀ x : ℝ, 0 ≤ x → ∃ R, x ≤ R ∧ R ≤ x + D ∧
      ∀ w : ℂ, ‖w‖ = R → Real.exp (-(B * (1 + R) ^ (3 / 2 : ℝ))) ≤ ‖F w‖ := by
  classical
  have hA : 0 ≤ A := by simpa using hcount ∅ 1 le_rfl
  set S := ∑' k, ‖z k‖ ^ (-(3 / 2 : ℝ)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun k => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨2 * S + 3 * A * (Real.log (8 * (3 * A + 1)) + 4), 2, fun x hx => ?_⟩
  set T := (finite_of_count hcount (2 * x + 5)).toFinset with hTdef
  have hmemT : ∀ k, k ∈ T ↔ ‖z k‖ ≤ 2 * x + 5 := fun k => by simp [hTdef]
  set N := T.card with hNdef
  set M := T.image (fun k => ‖z k‖) with hMdef
  obtain ⟨R, ⟨hR1, hR2⟩, hgapM⟩ := exists_gap M (x + 1)
  have hMN : (M.card : ℝ) ≤ N := by exact_mod_cast Finset.card_image_le
  set ε := 1 / (4 * ((N : ℝ) + 1)) with hε
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hε0 : 0 < ε := by positivity
  have hεle : ε ≤ 1 / (4 * ((M.card : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hε14 : ε ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have hR0 : 0 < R := by linarith
  have hgap : ∀ k, ε ≤ |R - ‖z k‖| := by
    intro k
    by_cases hk : ‖z k‖ ≤ 2 * x + 5
    · exact hεle.trans (hgapM _ (Finset.mem_image_of_mem _ ((hmemT k).2 hk)))
    · push Not at hk
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
  have hT : ∀ k, ‖z k‖ ≤ 2 * R → k ∈ T := fun k hk => (hmemT k).2 (by linarith)
  refine ⟨R, by linarith, by linarith, fun w hw => ?_⟩
  have hpp := log_norm_partial_prod_ge hz hS hR0 hε0 (by linarith) hT hgap hw
  have hne1 : ∀ k, w / z k ≠ 1 := by
    intro k hk
    rw [div_eq_one_iff_eq (hz k)] at hk
    have := hgap k
    rw [← hk, hw, sub_self, abs_zero] at this
    linarith
  have hlim := ((hF w).tendsto_prod_nat).norm
  have hbd : ∀ n, Real.exp (-(2 * R ^ (3 / 2 : ℝ) * S) + N * Real.log (ε / (2 * R))) ≤
      ‖∏ i ∈ Finset.range n, weierstrassFactorOne (w / z i)‖ := by
    intro n
    have hne : ∏ i ∈ Finset.range n, weierstrassFactorOne (w / z i) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun k _ => weierstrassFactorOne_ne_zero (hne1 k))
    rw [← Real.exp_log (norm_pos_iff.2 hne)]
    exact Real.exp_le_exp.2 (hpp _)
  have hF' := ge_of_tendsto' hlim hbd
  refine le_trans (Real.exp_le_exp.2 ?_) hF'
  have hN : (N : ℝ) ≤ 3 * A * (1 + R) := by
    have := hcount T (2 * x + 5) (by linarith)
    rw [Finset.filter_true_of_mem (fun k hk => (hmemT k).1 hk)] at this
    nlinarith
  have hlog : Real.log (ε / (2 * R)) = -Real.log (8 * R * (N + 1)) := by
    rw [← Real.log_inv]
    congr 1
    rw [hε]
    field_simp
    ring
  have hD := numeric_bound hA (t := 1 + R) (by linarith) hR0 (by linarith) hN0 hN
  have hRp : R ^ (3 / 2 : ℝ) ≤ (1 + R) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hR0.le (by linarith) (by norm_num)
  have h1 : R ^ (3 / 2 : ℝ) * S ≤ (1 + R) ^ (3 / 2 : ℝ) * S :=
    mul_le_mul_of_nonneg_right hRp hS0
  rw [hlog]
  have e : (2 * S + 3 * A * (Real.log (8 * (3 * A + 1)) + 4)) * (1 + R) ^ (3 / 2 : ℝ) =
      2 * ((1 + R) ^ (3 / 2 : ℝ) * S) +
        3 * A * (Real.log (8 * (3 * A + 1)) + 4) * (1 + R) ^ (3 / 2 : ℝ) := by ring
  rw [e]
  nlinarith

private lemma analyticOrderAt_one_sub_div {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, z i ≠ 0) (i : ι) {w : ℂ} (hzi : z i = w) :
    analyticOrderAt (fun x => 1 - x / z i) w = 1 := by
  have hq : AnalyticAt ℂ (fun _ : ℂ => -(z i)⁻¹) w := analyticAt_const
  have hq_ne : (-(z i)⁻¹ : ℂ) ≠ 0 := by simp [hz i]
  have heq : ∀ x : ℂ, 1 - x / z i = (x - w) * (-(z i)⁻¹) := by
    intro x
    rw [← hzi]
    field_simp [hz i]
    ring
  have ha : AnalyticAt ℂ (fun x => 1 - x / z i) w := by fun_prop
  exact (ha.analyticOrderAt_eq_natCast (n := 1)).2
    ⟨fun _ => -(z i)⁻¹, hq, hq_ne, Eventually.of_forall fun x => by simp [heq]⟩

/-! ### Finite products -/

private theorem analyticOrderAt_finset_prod_one_sub {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, z i ≠ 0)
    (s : Finset ι) (w : ℂ) [DecidablePred (fun i => z i = w)] :
    analyticOrderAt (fun x => ∏ i ∈ s, (1 - x / z i)) w =
      ((s.filter (fun i => z i = w)).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero
  | insert i s hi ih =>
    have hfac : AnalyticAt ℂ (fun x => 1 - x / z i) w := by fun_prop
    have hrest : AnalyticAt ℂ (fun x => ∏ j ∈ s, (1 - x / z j)) w := by fun_prop
    have e : (fun x => ∏ j ∈ insert i s, (1 - x / z j)) =
        (fun x => 1 - x / z i) * (fun x => ∏ j ∈ s, (1 - x / z j)) := by
      ext x; simp [Finset.prod_insert hi]
    rw [e, analyticOrderAt_mul hfac hrest, ih, Finset.filter_insert]
    by_cases hzi : z i = w
    · rw [ite_eq_left hzi, Finset.card_insert_of_notMem (by simp [hi])]
      rw [analyticOrderAt_one_sub_div z hz i hzi]
      push_cast
      ring
    · rw [ite_eq_right hzi]
      rw [hfac.analyticOrderAt_eq_zero.mpr (by
        intro h
        apply hzi
        have : w / z i = 1 := by linear_combination -h
        rw [div_eq_one_iff_eq (hz i)] at this
        exact this.symm), zero_add]

private lemma zero_enumeration_ne_zero {ι : Type*} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {z : ι → ℂ}
    (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) : ∀ k, z k ≠ 0 := by
  intro k hk
  have h1 := hz 0
  rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0, eq_comm, Set.encard_eq_zero] at h1
  have : k ∉ {j | z j = 0} := by simp [h1]
  exact this hk

/-- **Hadamard factorization for entire functions of exponential type (genus ≤ 1), infinitely
many zeros.**  Let `f` be entire with `f 0 = 1` and `‖f z‖ ≤ exp (C (1 + ‖z‖))`, and let
`z : ℕ → ℂ` enumerate its zeros with multiplicity
(`analyticOrderAt f w = #{k | z k = w}`).  Then there is `a : ℂ` with
`f w = exp (a w) * ∏' k, E₁ (w / z k)`, the product being multipliable. -/
theorem exists_eq_exp_mul_tprod_of_norm_le_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) {C : ℝ}
    (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖))) {z : ℕ → ℂ}
    (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) :
    ∃ a : ℂ, ∀ w : ℂ, Multipliable (fun k => weierstrassFactorOne (w / z k)) ∧
      f w = Complex.exp (a * w) * ∏' k, weierstrassFactorOne (w / z k) := by
  classical
  have hf0 : f 0 ≠ 0 := by rw [h0]; exact one_ne_zero
  have hz0 := zero_enumeration_ne_zero hf hf0 hz
  obtain ⟨A, hA⟩ := hf.zero_count_le hf0 h
  have hcount : ∀ s : Finset ℕ, ∀ r : ℝ, 1 ≤ r →
      ((s.filter (fun k => ‖z k‖ ≤ r)).card : ℝ) ≤ A * r := by
    intro s r hr
    have h1 := count_le_divisor hf hf0 hz s r
    have h2 : ((s.filter (fun k => ‖z k‖ ≤ r)).card : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall 0 r) u : ℤ) : ℝ) := by
      exact_mod_cast h1
    exact h2.trans (hA r hr)
  have hs2 : Summable fun k => ‖z k‖⁻¹ ^ 2 := by
    have := hf.summable_zeros_rpow hf0 h hz (ε := 1) one_pos
    refine this.congr fun k => ?_
    rw [Real.rpow_neg (norm_nonneg _), inv_pow]
    norm_num
  have hS : Summable fun k => ‖z k‖ ^ (-(3 / 2 : ℝ)) := by
    have := hf.summable_zeros_rpow hf0 h hz (ε := 1 / 2) (by norm_num)
    refine this.congr fun k => ?_
    norm_num
  obtain ⟨P, hPd, hPprod, hP0, hPord⟩ := Complex.exists_entire_prod_genus_one hz0 hs2
  have hlow := lower_bound_prod hz0 hcount hS (fun w => hPprod.hasProd (Set.mem_univ w))
  obtain ⟨a, ha⟩ := eq_exp_mul_of_lower_bound hf hPd h0 hP0 h
    (fun w => by rw [hz, hPord]) hlow
  refine ⟨a, fun w => ⟨(hPprod.hasProd (Set.mem_univ w)).multipliable, ?_⟩⟩
  rw [ha w, (hPprod.hasProd (Set.mem_univ w)).tprod_eq]

/-- The same for finitely many zeros: `f w = exp (a w) * ∏ i, (1 - w / z i)`. -/
theorem exists_eq_exp_mul_prod_of_norm_le_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) {C : ℝ}
    (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖))) {n : ℕ} {z : Fin n → ℂ}
    (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) :
    ∃ a : ℂ, ∀ w : ℂ, f w = Complex.exp (a * w) * ∏ i, (1 - w / z i) := by
  classical
  have hf0 : f 0 ≠ 0 := by rw [h0]; exact one_ne_zero
  have hz0 := zero_enumeration_ne_zero hf hf0 hz
  have hPd : Differentiable ℂ (fun x => ∏ i, (1 - x / z i)) := by fun_prop
  have hord : ∀ w, analyticOrderAt f w = analyticOrderAt (fun x => ∏ i, (1 - x / z i)) w := by
    intro w
    rw [hz, analyticOrderAt_finset_prod_one_sub z hz0, ← Set.encard_coe_eq_coe_finsetCard]
    simp
  have hlow : ∃ B D : ℝ, ∀ x : ℝ, 0 ≤ x → ∃ R, x ≤ R ∧ R ≤ x + D ∧
      ∀ w : ℂ, ‖w‖ = R → Real.exp (-(B * (1 + R) ^ (3 / 2 : ℝ))) ≤
        ‖∏ i, (1 - w / z i)‖ := by
    refine ⟨0, 2 * ∑ i, ‖z i‖, fun x hx =>
      ⟨x + 2 * ∑ i, ‖z i‖, ?_, le_rfl, fun w hw => ?_⟩⟩
    · have : 0 ≤ ∑ i, ‖z i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
      linarith
    · simp only [zero_mul, neg_zero, Real.exp_zero, norm_prod]
      calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => ?_)
      have hzi : 0 < ‖z i‖ := norm_pos_iff.2 (hz0 i)
      have hle : ‖z i‖ ≤ ∑ j, ‖z j‖ :=
        Finset.single_le_sum (f := fun j => ‖z j‖) (fun j _ => norm_nonneg _)
          (Finset.mem_univ i)
      have h1 : 2 * ‖z i‖ ≤ ‖w‖ := by rw [hw]; linarith
      have h2 : ‖w / z i‖ - ‖(1 : ℂ)‖ ≤ ‖1 - w / z i‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le _ _
      rw [norm_div, norm_one] at h2
      have h3 : 2 ≤ ‖w‖ / ‖z i‖ := by rw [le_div_iff₀ hzi]; linarith
      linarith
  obtain ⟨a, ha⟩ := eq_exp_mul_of_lower_bound hf hPd h0 (by simp) h hord hlow
  exact ⟨a, ha⟩
end Differentiable
