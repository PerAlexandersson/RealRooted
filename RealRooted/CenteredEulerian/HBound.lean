/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.ArcsinBound
public import RealRooted.CenteredEulerian.Majorants

/-!
# The coefficient sum of `h = (s/f)²`: `∑_{n ≥ 1} |h_n| ≤ 1 - 1/a`
Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.
-/

@[expose] public section

open PowerSeries Real Filter Topology

namespace RealRooted.CenteredEulerian

lemma nonnegPS_fT : NonnegPS fT := fun n => by
  rw [fT, coeff_mk]; have := coeff_fS_nonneg (n + 1); rwa [fS, coeff_mk] at this

lemma sum_coeff_fT_le (K : ℕ) : ∑ n ∈ Finset.range K, coeff n fT ≤ π / 2 := by
  have h := sum_coeff_fS_le (K + 1)
  rw [Finset.sum_range_succ', coeff_fS_zero, add_zero] at h
  convert h using 1
  apply Finset.sum_congr rfl; intro n _; rw [fT, coeff_mk, fS, coeff_mk]

lemma aConst_eq : aConst = (π / 2) ^ 2 := by rw [aConst]; ring

lemma sum_coeff_AtS_le (K : ℕ) : ∑ n ∈ Finset.range K, coeff n AtS ≤ aConst := by
  have h := sum_coeff_mul_le nonnegPS_fT nonnegPS_fT (zero_le_one) K
  simp only [one_pow, mul_one] at h
  rw [AtS, pow_two]
  refine h.trans ?_
  rw [← pow_two, aConst_eq]
  have h0 : 0 ≤ ∑ n ∈ Finset.range K, coeff n fT :=
    Finset.sum_nonneg (fun n _ => nonnegPS_fT n)
  exact pow_le_pow_left₀ h0 (sum_coeff_fT_le K) 2

lemma one_lt_aConst : 1 < aConst := by
  rw [aConst]; have := Real.pi_gt_three; nlinarith

lemma sum_abs_coeff_hS_le (K : ℕ) :
    ∑ n ∈ Finset.range K, |coeff (n + 1) hS| ≤ 1 - 1 / aConst := by
  have ha := one_lt_aConst
  -- the generating-function inequality on `[0, 1)`
  have hgen : ∀ s : ℝ, 0 ≤ s → s < 1 →
      ∑ n ∈ Finset.range K, |coeff (n + 1) hS| * s ^ (n + 1) ≤ 1 - 1 / aConst := by
    intro s hs0 hs1
    have hgeo : Summable (fun n : ℕ => s ^ n) := summable_geometric_of_lt_one hs0 hs1
    have hA : Summable (fun n => ‖coeff n AtS * s ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeo
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (coeff_AtS_nonneg n), abs_pow,
        abs_of_nonneg hs0]
      exact mul_le_of_le_one_left (pow_nonneg hs0 _) (coeff_AtS_le_one n)
    have hH : Summable (fun n => ‖coeff n hS * s ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeo
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs0]
      exact mul_le_of_le_one_left (pow_nonneg hs0 _) (abs_coeff_hS_le_one n)
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA hH
    have hterm : ∀ n, ∑ kl ∈ Finset.antidiagonal n, coeff kl.1 AtS * s ^ kl.1 *
        (coeff kl.2 hS * s ^ kl.2) = if n = 0 then 1 else 0 := by
      intro n
      have : ∑ kl ∈ Finset.antidiagonal n, coeff kl.1 AtS * s ^ kl.1 *
          (coeff kl.2 hS * s ^ kl.2) = coeff n (AtS * hS) * s ^ n := by
        rw [coeff_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro kl hkl
        rw [Finset.mem_antidiagonal] at hkl
        rw [← hkl, pow_add]; ring
      rw [this, AtS_mul_hS, coeff_one]
      split_ifs with h
      · subst h; simp
      · simp
    simp_rw [hterm] at hprod
    rw [tsum_ite_eq] at hprod
    -- bounds on the `Ã` sum
    set SA := ∑' n, coeff n AtS * s ^ n with hSA
    set SH := ∑' n, coeff n hS * s ^ n with hSH
    have hSA_le : SA ≤ aConst := by
      apply Real.tsum_le_of_sum_range_le
      · intro n; exact mul_nonneg (coeff_AtS_nonneg n) (pow_nonneg hs0 _)
      · intro K
        refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (sum_coeff_AtS_le K)
        exact mul_le_of_le_one_right (coeff_AtS_nonneg n) (pow_le_one₀ hs0 hs1.le)
    have hSA_ge : 1 ≤ SA := by
      have hs := (Summable.of_norm hA)
      rw [hSA, hs.tsum_eq_zero_add]
      simp only [pow_zero, mul_one]
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_AtS]
      have : 0 ≤ ∑' n, coeff (n + 1) AtS * s ^ (n + 1) :=
        tsum_nonneg (fun n => mul_nonneg (coeff_AtS_nonneg _) (pow_nonneg hs0 _))
      linarith
    have hSHeq : SH = 1 / SA := by
      rw [eq_div_iff (by linarith)]; linarith
    have hSH_ge : 1 / aConst ≤ SH := by
      rw [hSHeq]; exact one_div_le_one_div_of_le (by linarith) hSA_le
    -- `SH = 1 - ∑ |h_{n+1}| s^{n+1}`
    have hsH := Summable.of_norm hH
    have hsplit : SH = 1 - ∑' n, |coeff (n + 1) hS| * s ^ (n + 1) := by
      rw [hSH, hsH.tsum_eq_zero_add, pow_zero, mul_one, coeff_hS_zero]
      rw [sub_eq_add_neg, ← tsum_neg]
      congr 1
      apply tsum_congr; intro n
      rw [abs_of_nonpos (coeff_hS_le_zero (by lia))]; ring
    have hsum2 : Summable (fun n => |coeff (n + 1) hS| * s ^ (n + 1)) := by
      have := (summable_nat_add_iff 1).mpr hH
      simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs0] using this
    have hpart : ∑ n ∈ Finset.range K, |coeff (n + 1) hS| * s ^ (n + 1) ≤
        ∑' n, |coeff (n + 1) hS| * s ^ (n + 1) :=
      hsum2.sum_le_tsum _ (fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hs0 _))
    linarith
  -- pass to the limit `s → 1⁻`
  have hcont : Tendsto (fun s : ℝ => ∑ n ∈ Finset.range K, |coeff (n + 1) hS| * s ^ (n + 1))
      (𝓝[<] 1) (𝓝 (∑ n ∈ Finset.range K, |coeff (n + 1) hS| * 1 ^ (n + 1))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Continuous.tendsto
    fun_prop
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      ∑ n ∈ Finset.range K, |coeff (n + 1) hS| * s ^ (n + 1) ≤ 1 - 1 / aConst := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hgen s hs.1.le hs.2
  have := le_of_tendsto hcont hev
  simpa using this

end RealRooted.CenteredEulerian
