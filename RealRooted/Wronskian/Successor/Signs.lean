import RealRooted.Wronskian.Successor.Gap

/-!
# Successor-degree Wronskian signs

These sign and root-location lemmas supply the lower-to-higher splitness
transfer for a strict successor-degree Wronskian sign.
-/

open Polynomial

namespace RealRooted

/-- A negative Wronskian determines the alternating signs of the
higher-degree polynomial at the simple, ordered roots of its companion. -/
lemma wronskian_sign_at_roots_of_neg_succ {n : ℕ}
    {f g : ℝ[X]} (hf_pos : HasPosLeadingCoeff f)
    (hf_deg : f.natDegree = n + 1)
    (hW : ∀ t : ℝ, f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t < 0)
    (s : Fin (n + 1) → ℝ) (hs_mono : StrictMono s)
    (hs_roots : ∀ k, f.IsRoot (s k)) :
    ∀ k : Fin (n + 1), g.eval (s k) * (-1) ^ (n - k.val) < 0 := by
  have hf_ne : f ≠ 0 := leadingCoeff_ne_zero.mp hf_pos.ne'
  have h_eval_deriv : ∀ k : Fin (n + 1),
      f.derivative.eval (s k) =
        f.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (s k - s j) := by
    intro k
    have h_eq : f = Polynomial.C f.leadingCoeff * ∏ j : Fin (n + 1),
        (Polynomial.X - Polynomial.C (s j)) := by
      convert Polynomial.splits_eq_C_mul_prod _ _ _ _ _
      · simp_all
      · simp_all
      · simp_all
      · exact hs_mono.injective
    conv_lhs => rw [h_eq]
    exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
      f.leadingCoeff s k
  have h_prod_sign : ∀ k : Fin (n + 1),
      f.derivative.eval (s k) * (-1) ^ (n - k.val) > 0 := by
    intro k
    rw [h_eval_deriv k]
    have h_prod_sign : ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
        (s k - s j) = (-1) ^ (n - k.val) *
          (∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
            |s k - s j|) := by
      have h_prod_sign_abs : ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
          (s k - s j) = ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
            (-1) ^ (if k < j then 1 else 0) * |s k - s j| := by
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        split_ifs with hjk
        · simp_all only [pow_one, neg_mul, one_mul]
          rw [abs_of_neg] <;> linarith [hs_mono hjk]
        · simp_all only [pow_zero, one_mul]
          rw [abs_of_nonneg (sub_nonneg.mpr (hs_mono.monotone (not_lt.mp hjk)))]
      rw [h_prod_sign_abs, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp only [Finset.sum_boole, Nat.cast_id, mul_eq_mul_right_iff]
      have hfilter : (Finset.univ.erase k).filter (fun x ↦ k < x) = Finset.Ioi k := by
        grind
      simp_all
    rw [h_prod_sign, mul_comm f.leadingCoeff, mul_assoc]
    have habs : 0 < ∏ j ∈ Finset.univ.erase k, |s k - s j| :=
      Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
        hs_mono.injective.ne (Finset.ne_of_mem_erase hj).symm
    have hpow : (0 : ℝ) < ((-1) ^ (n - k.val)) ^ 2 := by
      positivity
    nlinarith [mul_pos habs hf_pos, sq_nonneg ((-1 : ℝ) ^ (n - k.val))]
  intro k
  have hWk := hW (s k)
  have hfr : f.eval (s k) = 0 := hs_roots k
  rw [hfr, zero_mul, sub_zero] at hWk
  have hpe := h_prod_sign k
  have hane : f.derivative.eval (s k) ≠ 0 := by
    intro hzero
    simp_all
  nlinarith [mul_pos hpe (neg_pos.mpr hWk), mul_self_pos.mpr hane]

/-- A positive-leading polynomial of degree `n + 2` has a root below `s₀`
when its signed value there is negative. -/
lemma exists_root_lt_of_posLeadingCoeff_eval_mul_negOnePow_neg {n : ℕ} {g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g) (hg_deg : g.natDegree = n + 2)
    (s0 : ℝ) (hsign : g.eval s0 * (-1 : ℝ) ^ n < 0) :
    ∃ x, x < s0 ∧ g.IsRoot x := by
  have h_tendsto_bot :
      Filter.Tendsto (fun t ↦ g.eval t * (-1) ^ n) Filter.atBot Filter.atTop := by
    have h_tendsto_neg :
        Filter.Tendsto (fun t ↦ g.eval (-t) * (-1) ^ n) Filter.atTop Filter.atTop := by
      have h_leading :
          0 < Polynomial.leadingCoeff (g.comp (-Polynomial.X)) * (-1) ^ n := by
        rw [Polynomial.comp_neg_X_leadingCoeff_eq, hg_deg]
        have hpow : ((-1 : ℝ)) ^ (n + 2) = (-1) ^ n := by ring
        rw [hpow]
        rcases Nat.even_or_odd n with h | h <;>
          rw [h.neg_one_pow] <;> norm_num <;> exact hg_pos
      have hcomp_deg : (g.comp (-Polynomial.X)).natDegree = n + 2 := by
        rw [Polynomial.natDegree_comp]
        simp [hg_deg]
      have hCne : ((-1 : ℝ) ^ n) ≠ 0 := by positivity
      have h_tendsto_comp :
          Filter.Tendsto
            (fun t ↦ Polynomial.eval t (g.comp (-Polynomial.X) * Polynomial.C ((-1) ^ n)))
            Filter.atTop Filter.atTop := by
        rw [Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg]
        have hmul_nd : (g.comp (-Polynomial.X) * Polynomial.C ((-1) ^ n)).natDegree = n + 2 := by
          rw [Polynomial.natDegree_mul (by intro h; simp_all)
            (Polynomial.C_ne_zero.mpr hCne), Polynomial.natDegree_C, add_zero, hcomp_deg]
        refine ⟨Polynomial.natDegree_pos_iff_degree_pos.mp (by simp_all), ?_⟩
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
        grind
      simpa using h_tendsto_comp
    convert h_tendsto_neg.comp Filter.tendsto_neg_atBot_atTop using 2
    simp
  have h_ex : ∃ x : ℝ, x < s0 ∧ 0 < g.eval x * (-1) ^ n :=
    (Filter.Eventually.and (Filter.eventually_lt_atBot s0)
      (h_tendsto_bot.eventually_gt_atTop 0)).exists
  obtain ⟨x, hx_lt, hx_pos⟩ := h_ex
  have h_cont : ContinuousOn (fun t ↦ g.eval t) (Set.Icc x s0) :=
    g.continuous.continuousOn
  have h_ends : g.eval x * g.eval s0 < 0 := by
    have hpow : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rcases Nat.even_or_odd n with h | h <;> rw [h.neg_one_pow] <;> norm_num
    nlinarith [hx_pos, hsign, hpow]
  rw [mul_neg_iff] at h_ends
  have h_ivt : ∃ c ∈ Set.Ioo x s0, g.eval c = 0 := by
    rcases h_ends with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact intermediate_value_Ioo' hx_lt.le h_cont ⟨hb, ha⟩
    · exact intermediate_value_Ioo hx_lt.le h_cont ⟨ha, hb⟩
  obtain ⟨c, hc, hc0⟩ := h_ivt
  exact ⟨c, hc.2, hc0⟩

/-- A positive-leading polynomial with a negative value has a root above that
point. -/
lemma exists_root_gt_of_posLeadingCoeff_eval_neg {n : ℕ} {g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g) (hg_deg : g.natDegree = n + 2)
    (s : ℝ) (hsign : g.eval s < 0) :
    ∃ x, s < x ∧ g.IsRoot x := by
  have hnd_pos : 0 < g.natDegree := by simp_all
  have h_tendsto_top : Filter.Tendsto (fun t ↦ g.eval t) Filter.atTop Filter.atTop := by
    rw [Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg]
    exact ⟨Polynomial.natDegree_pos_iff_degree_pos.mp hnd_pos, hg_pos.le⟩
  have h_ex : ∃ x : ℝ, s < x ∧ 0 < g.eval x :=
    (Filter.Eventually.and (Filter.eventually_gt_atTop s)
      (h_tendsto_top.eventually_gt_atTop 0)).exists
  obtain ⟨x, hx_gt, hx_pos⟩ := h_ex
  have h_cont : ContinuousOn (fun t ↦ g.eval t) (Set.Icc s x) :=
    g.continuous.continuousOn
  have h_ivt : ∃ c ∈ Set.Ioo s x, g.eval c = 0 :=
    intermediate_value_Ioo hx_gt.le h_cont ⟨hsign, hx_pos⟩
  obtain ⟨c, hc, hc0⟩ := h_ivt
  exact ⟨c, hc.1, hc0⟩

/-- Opposite negative-to-positive endpoint evaluations force a polynomial
root strictly between the endpoints. -/
lemma exists_root_between_of_eval_neg_pos {g : ℝ[X]}
    (a b : ℝ) (hab : a < b) (hga : g.eval a < 0) (hgb : 0 < g.eval b) :
    ∃ x, a < x ∧ x < b ∧ g.IsRoot x := by
  have h_cont : ContinuousOn (fun t ↦ g.eval t) (Set.Icc a b) :=
    g.continuous.continuousOn
  obtain ⟨c, hc, hc0⟩ : ∃ c ∈ Set.Ioo a b, g.eval c = 0 :=
    intermediate_value_Ioo hab.le h_cont ⟨hga, hgb⟩
  exact ⟨c, hc.1, hc.2, hc0⟩

/-- Opposite positive-to-negative endpoint evaluations force a polynomial
root strictly between the endpoints. -/
lemma exists_root_between_of_eval_pos_neg {g : ℝ[X]}
    (a b : ℝ) (hab : a < b) (hga : 0 < g.eval a) (hgb : g.eval b < 0) :
    ∃ x, a < x ∧ x < b ∧ g.IsRoot x := by
  have h_cont : ContinuousOn (fun t ↦ g.eval t) (Set.Icc a b) :=
    g.continuous.continuousOn
  obtain ⟨c, hc, hc0⟩ : ∃ c ∈ Set.Ioo a b, g.eval c = 0 :=
    intermediate_value_Ioo' hab.le h_cont ⟨hgb, hga⟩
  exact ⟨c, hc.1, hc.2, hc0⟩

end RealRooted
