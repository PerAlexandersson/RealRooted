/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib

/-!
# Zeros of entire functions of exponential type

For an entire function `f` with `f 0 ≠ 0` and `‖f z‖ ≤ exp (C * (1 + ‖z‖))`, Jensen's formula
(`MeromorphicOn.circleAverage_log_norm`) bounds the number of zeros, counted with multiplicity, in
the closed disc of radius `r ≥ 1` by `A * r`. A dyadic decomposition of the zeros then shows that
the convergence exponent of the zero sequence is at most one.

## Main statements

* `Differentiable.zero_count_le`: there is `A` such that the sum of `divisor f (closedBall 0 r)`
  over all points is at most `A * r` for every `r ≥ 1`.
* `Differentiable.summable_zeros_rpow`: if `z : ι → ℂ` enumerates the zeros of `f` with
  multiplicity (`analyticOrderAt f w = #{k | z k = w}` for all `w`), then
  `∑ k, ‖z k‖ ^ (-(1 + ε))` converges for every `ε > 0`.
-/

public section

open Complex Filter Metric Topology
/- `divisor` in the statements below refers to `MeromorphicOn.divisor`. -/
open MeromorphicOn

noncomputable section

namespace Differentiable

private lemma divisor_eq_of_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r R : ℝ}
    (hrR : r ≤ R) {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) r) :
    divisor f (closedBall 0 r) u = divisor f (closedBall 0 R) u := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  rw [divisor_apply (ha.mono (Set.subset_univ _)).meromorphicOn hu,
    divisor_apply (ha.mono (Set.subset_univ _)).meromorphicOn (closedBall_subset_closedBall hrR hu)]

private lemma jensen_count {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    ((∑ᶠ u, divisor f (closedBall 0 r) u : ℤ) : ℝ) * Real.log 2 ≤
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 (2 * r) - Real.log ‖f 0‖ := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  set R := 2 * r
  have hR : 0 < R := by positivity
  have hJ := MeromorphicOn.circleAverage_log_norm (c := 0) (f := f) hR.ne'
    (ha.mono (Set.subset_univ _)).meromorphicOn
  rw [abs_of_pos hR] at hJ
  rw [(hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero h0] at hJ
  set D := divisor f (closedBall (0 : ℂ) r)
  set E := divisor f (closedBall (0 : ℂ) R)
  have hE0 : E 0 = 0 := by
    have : (0:ℂ) ∈ closedBall (0:ℂ) R := by simp [hR.le]
    simp only [E, divisor_apply (ha.mono (Set.subset_univ _)).meromorphicOn this]
    rw [(hf.analyticAt 0).meromorphicOrderAt_eq]
    rw [(analyticOrderAt_eq_zero).2 (Or.inr h0)]
    simp
  have hEfin := E.finiteSupport (isCompact_closedBall 0 R)
  have hEnn : ∀ u, 0 ≤ E u := fun u => (ha.mono (Set.subset_univ _)).divisor_nonneg u
  have hDE : ∀ u, ‖u‖ ≤ r → D u = E u := fun u hu =>
    divisor_eq_of_le hf (by linarith) (by simpa using hu)
  have hsub : D.support ⊆ E.support := by
    intro u hu
    have hu' : u ∈ closedBall (0:ℂ) r := D.supportWithinDomain hu
    simp only [Function.mem_support] at hu ⊢
    rwa [← hDE u (by simpa using hu')]
  rw [hJ, hE0]
  simp only [Int.cast_zero, zero_mul, add_zero, add_sub_cancel_right]
  rw [finsum_eq_sum_of_support_subset (s := hEfin.toFinset) _ (by simpa using hsub)]
  rw [finsum_eq_sum_of_support_subset (s := hEfin.toFinset) _ (by
    intro u hu
    simp only [Function.mem_support, Set.Finite.coe_toFinset] at hu ⊢
    intro h; apply hu; simp [h])]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u hu
  simp only [Set.Finite.mem_toFinset, Function.mem_support] at hu
  have hu0 : u ≠ 0 := by rintro rfl; exact hu hE0
  have huR : ‖u‖ ≤ R := by simpa using E.supportWithinDomain hu
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hEu : (0:ℝ) ≤ E u := by exact_mod_cast hEnn u
  rw [zero_sub, norm_neg]
  by_cases hur : ‖u‖ ≤ r
  · rw [hDE u hur]
    apply mul_le_mul_of_nonneg_left _ hEu
    apply Real.log_le_log (by norm_num)
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  · have : D u = 0 := D.apply_eq_zero_of_notMem (by simpa using hur)
    rw [this]
    simp only [Int.cast_zero, zero_mul]
    apply mul_nonneg hEu
    apply Real.log_nonneg
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith

/-- **Jensen zero count for exponential type.**  An entire function `f` with `f 0 ≠ 0` and
`‖f z‖ ≤ exp (C (1 + ‖z‖))` has at most `A * r` zeros, counted with multiplicity,
in the closed
disc of radius `r ≥ 1`, where `A` depends only on `C` and `f 0`. -/
theorem zero_count_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {C : ℝ}
    (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ A : ℝ, ∀ r : ℝ, 1 ≤ r →
      ((∑ᶠ u, divisor f (Metric.closedBall 0 r) u : ℤ) : ℝ) ≤ A * r := by
  refine ⟨(3 * |C| + |Real.log ‖f 0‖|) / Real.log 2, fun r hr => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ := jensen_count hf h0 (by linarith : 0 < r)
  have havg : Real.circleAverage (fun z => Real.log ‖f z‖) 0 (2 * r) ≤ |C| * (1 + 2 * r) := by
    apply Real.circleAverage_mono_on_of_le_circle
    · apply MeromorphicOn.circleIntegrable_log_norm
      exact fun z _ => (hf.analyticAt z).meromorphicAt
    · intro x hx
      have hxn : ‖x‖ = 2 * r := by
        rw [mem_sphere_zero_iff_norm] at hx; rw [hx, abs_of_pos (by linarith)]
      by_cases hfx : f x = 0
      · simp only [hfx, norm_zero, Real.log_zero]; positivity
      · calc Real.log ‖f x‖ ≤ Real.log (Real.exp (C * (1 + ‖x‖))) :=
              Real.log_le_log (norm_pos_iff.2 hfx) (h x)
          _ = C * (1 + 2 * r) := by rw [Real.log_exp, hxn]
          _ ≤ |C| * (1 + 2 * r) := by
              apply mul_le_mul_of_nonneg_right (le_abs_self C); linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  have h1 := neg_abs_le (Real.log ‖f 0‖)
  have h2 : |C| * (1 + 2 * r) ≤ 3 * |C| * r := by nlinarith [abs_nonneg C]
  have h3 : |Real.log ‖f 0‖| ≤ |Real.log ‖f 0‖| * r := by
    nlinarith [abs_nonneg (Real.log ‖f 0‖)]
  nlinarith


private lemma summable_rpow_of_count {ι : Type*} (x : ι → ℝ) {δ A p : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : ∀ k, δ ≤ x k) (hp : 1 < p)
    (hcount : ∀ s : Finset ι, ∀ r : ℝ, 1 ≤ r →
      ((s.filter (fun k => x k ≤ r)).card : ℝ) ≤ A * r) :
    Summable fun k => x k ^ (-p) := by
  classical
  have hA : 0 ≤ A := by simpa using hcount ∅ 1 le_rfl
  have hxpos : ∀ k, 0 < x k := fun k => hδ.trans_le (hx k)
  set g : ι → ℕ := fun k => ⌈Real.logb 2 (x k)⌉₊
  -- shell bound
  set b : ℕ → ℝ := fun j => A * 2 ^ j * (δ * (2:ℝ) ^ ((j:ℝ) - 1)) ^ (-p) with hb
  have hupper : ∀ k, x k ≤ 2 ^ g k := by
    intro k
    calc
      x k = (2 : ℝ) ^ Real.logb 2 (x k) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (hxpos k)).symm
      _ ≤ (2:ℝ) ^ ((g k : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ g k := Real.rpow_natCast _ _
  have hlower : ∀ k, δ * (2:ℝ) ^ ((g k : ℝ) - 1) ≤ x k := by
    intro k
    rcases Nat.eq_zero_or_pos (g k) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, zero_sub]
      have : (2 : ℝ) ^ (-1 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      nlinarith [hx k]
    · have h1 : ((g k - 1 : ℕ) : ℝ) < Real.logb 2 (x k) :=
        Nat.lt_ceil.1 (show g k - 1 < g k by lia)
      have h2 : ((g k - 1 : ℕ) : ℝ) = (g k : ℝ) - 1 := by
        rw [Nat.cast_sub (by lia)]; simp
      rw [h2] at h1
      have h3 : (2:ℝ) ^ ((g k : ℝ) - 1) ≤ x k := by
        calc (2:ℝ) ^ ((g k : ℝ) - 1) ≤ (2:ℝ) ^ Real.logb 2 (x k) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
          _ = x k := Real.rpow_logb (by norm_num) (by norm_num) (hxpos k)
      have h4 : 0 ≤ (2:ℝ) ^ ((g k : ℝ) - 1) := by positivity
      nlinarith
  have hshell : ∀ s : Finset ι, ∀ j : ℕ,
      ∑ k ∈ s with g k = j, x k ^ (-p) ≤ b j := by
    intro s j
    have hterm : ∀ k ∈ s.filter (fun k => g k = j),
        x k ^ (-p) ≤ (δ * (2 : ℝ) ^ ((j : ℝ) - 1)) ^ (-p) := by
      intro k hk
      simp only [Finset.mem_filter] at hk
      have := hlower k
      rw [hk.2] at this
      exact Real.rpow_le_rpow_of_nonpos (by positivity) this (by linarith)
    have hcard : (((s.filter (fun k => g k = j))).card : ℝ) ≤ A * 2 ^ j := by
      calc (((s.filter (fun k => g k = j))).card : ℝ)
          ≤ ((s.filter (fun k => x k ≤ (2:ℝ) ^ j)).card : ℝ) := by
            exact Nat.cast_le.2 (Finset.card_le_card (by
              intro k hk
              simp only [Finset.mem_filter] at hk ⊢
              exact ⟨hk.1, hk.2 ▸ hupper k⟩))
        _ ≤ A * 2 ^ j := hcount s _ (one_le_pow₀ (by norm_num))
    calc ∑ k ∈ s with g k = j, x k ^ (-p)
        ≤ ∑ k ∈ s with g k = j, (δ * (2 : ℝ) ^ ((j : ℝ) - 1)) ^ (-p) :=
          Finset.sum_le_sum hterm
      _ = ((s.filter (fun k => g k = j)).card : ℝ) * (δ * (2:ℝ) ^ ((j:ℝ) - 1)) ^ (-p) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ b j := mul_le_mul_of_nonneg_right hcard (by positivity)
  -- geometric
  have hbeq : ∀ j : ℕ, b j = (A * δ ^ (-p) * 2 ^ p) * ((2:ℝ) ^ (1 - p)) ^ j := by
    intro j
    simp only [hb]
    rw [Real.mul_rpow hδ.le (by positivity), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast ((2:ℝ) ^ (1 - p)), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2:ℝ) j]
    have e : (2:ℝ) ^ ((j:ℝ) * 1) * (2:ℝ) ^ ((j - 1) * -p) = 2 ^ p * 2 ^ ((1 - p) * j) := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; ring_nf
    rw [mul_one] at e
    calc A * 2 ^ (j:ℝ) * (δ ^ (-p) * 2 ^ ((j - 1) * -p))
        = A * δ ^ (-p) * (2 ^ (j:ℝ) * 2 ^ ((j - 1) * -p)) := by ring
      _ = _ := by rw [e]; ring
  have hq0 : 0 ≤ (2:ℝ) ^ (1 - p) := by positivity
  have hq1 : (2:ℝ) ^ (1 - p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbsum : Summable b := by
    have : b = fun j => (A * δ ^ (-p) * 2 ^ p) * ((2:ℝ) ^ (1 - p)) ^ j := funext hbeq
    rw [this]; exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hbnn : ∀ j, 0 ≤ b j := fun j => by simp only [hb]; positivity
  refine summable_of_sum_le (c := ∑' j, b j) (fun k => Real.rpow_nonneg (hxpos k).le _)
    (fun s => ?_)
  rw [← Finset.sum_fiberwise_of_maps_to (t := s.image g) (g := g)
    (fun i hi => Finset.mem_image_of_mem g hi)]
  calc ∑ j ∈ s.image g, ∑ k ∈ s with g k = j, x k ^ (-p)
      ≤ ∑ j ∈ s.image g, b j := Finset.sum_le_sum fun j _ => hshell s j
    _ ≤ ∑' j, b j := hbsum.sum_le_tsum _ (fun j _ => hbnn j)

/-- An entire function that does not vanish at `0` has finite order at every point. -/
theorem analyticOrderAt_ne_top_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (w : ℂ) :
    analyticOrderAt f w ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr h0)]; simp)

/-- Points of a zero enumeration `z` (listing each zero with its multiplicity) that equal `u`
are counted by the divisor at `u`. -/
theorem card_filter_eq_le_divisor {ι : Type*} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {z : ι → ℂ}
    (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) (s : Finset ι) {r : ℝ}
    {u : ℂ} (hu : ‖u‖ ≤ r) [DecidablePred (fun k => z k = u)] :
    ((s.filter (fun k => z k = u)).card : ℤ) ≤ divisor f (Metric.closedBall 0 r) u := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  rw [divisor_apply (ha.mono (Set.subset_univ _)).meromorphicOn (by simpa using hu),
    (hf.analyticAt u).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_ne_top_of_ne_zero hf h0 u)
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
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
        have hkr : ‖z k‖ ≤ r := (Finset.mem_filter.1 hk).2
        refine le_trans ?_ (card_filter_eq_le_divisor hf h0 hz s hkr)
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    _ ≤ ∑ b ∈ T ∪ hfin.toFinset, D b :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hDnn i)
    _ = ∑ᶠ u, D u := by
        rw [finsum_eq_sum_of_support_subset (s := T ∪ hfin.toFinset)]
        intro u hu
        simp only [Finset.coe_union, Set.Finite.coe_toFinset]
        exact Or.inr hu

private lemma norm_lower_bound {ι : Type*} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0)
    {z : ι → ℂ} (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ k, δ ≤ ‖z k‖ := by
  obtain ⟨e, he, hfe⟩ :=
    Metric.eventually_nhds_iff.1 (hf.continuous.continuousAt.eventually_ne h0)
  refine ⟨min e 1, lt_min he one_pos, min_le_right _ _, fun k => ?_⟩
  by_contra hk
  push Not at hk
  have hne : f (z k) ≠ 0 := hfe (by simpa using hk.trans_le (min_le_left _ _))
  have h1 := hz (z k)
  rw [analyticOrderAt_eq_zero.2 (Or.inr hne), eq_comm, Set.encard_eq_zero] at h1
  simpa [h1] using (show k ∈ {j | z j = z k} from rfl)


/-- **Convergence exponent ≤ 1.** For an enumeration `z : ι → ℂ` of the zeros of `f` above,
with multiplicity (that is, `analyticOrderAt f w = #{k | z k = w}` for all `w`), and any
`ε > 0`, `∑ ‖z k‖^{-(1+ε)} < ∞`. -/
theorem summable_zeros_rpow {ι : Type*} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0)
    {C : ℝ} (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖))) {z : ι → ℂ}
    (hz : ∀ w : ℂ, analyticOrderAt f w = Set.encard {k | z k = w}) {ε : ℝ} (hε : 0 < ε) :
    Summable fun k => ‖z k‖ ^ (-(1 + ε)) := by
  obtain ⟨A, hA⟩ := zero_count_le hf h0 h
  obtain ⟨δ, hδ, hδ1, hδz⟩ := norm_lower_bound hf h0 hz
  refine summable_rpow_of_count (fun k => ‖z k‖) hδ hδ1 hδz (by linarith) (A := A) ?_
  intro s r hr
  classical
  have hcount : ((s.filter (fun k => ‖z k‖ ≤ r)).card : ℝ) ≤
      ((∑ᶠ u, divisor f (Metric.closedBall 0 r) u : ℤ) : ℝ) := by
    exact_mod_cast count_le_divisor hf h0 hz s r
  exact hcount.trans (hA r hr)

end Differentiable
