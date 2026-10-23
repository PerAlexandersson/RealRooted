/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.ChangeBasis

/-!
# Rational majorants for `φ_{jk}` (B.8)–(B.9)

Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.

We bound `∑_k |φ_{jk}| x^k` at `x = π/6`.
-/

@[expose] public section

open PowerSeries Real

namespace RealRooted.CenteredEulerian

lemma sum_range_two_mul (f : ℕ → ℝ) (R : ℕ) :
    ∑ k ∈ Finset.range (2 * R), f k = ∑ r ∈ Finset.range R, (f (2 * r) + f (2 * r + 1)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [show 2 * (R + 1) = 2 * R + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

lemma sum_le_sum_two_mul {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (K : ℕ) :
    ∑ k ∈ Finset.range K, f k ≤ ∑ r ∈ Finset.range K, (f (2 * r) + f (2 * r + 1)) := by
  rw [← sum_range_two_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by intro k; simp; lia) (fun k _ _ => hf k)

lemma geom_partial_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (K : ℕ) :
    ∑ r ∈ Finset.range K, y ^ r ≤ 1 / (1 - y) := by
  rw [one_div, ← tsum_geometric_of_lt_one hy0 hy1]
  exact (summable_geometric_of_lt_one hy0 hy1).sum_le_tsum _ (fun r _ => pow_nonneg hy0 r)

/-! ### The majorant of `sin` -/

/-- `U(z) = z / (1 - z²/6)`. -/
noncomputable def uM : ℝ⟦X⟧ := mk (fun k => if Even k then 0 else (1 / 6 : ℝ) ^ (k / 2))

lemma six_pow_le_factorial (r : ℕ) : (6 : ℝ) ^ r ≤ ((2 * r + 1).factorial : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [pow_succ]
    have h0 : (0 : ℝ) ≤ 6 ^ r := by positivity
    have h1 : (6 : ℝ) ≤ ((2 * r + 1 : ℕ) + 1 + 1 : ℝ) * ((2 * r + 1 : ℕ) + 1) := by
      push_cast; nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    calc (6 : ℝ) ^ r * 6 ≤ ((2 * r + 1).factorial : ℝ) * (((2 * r + 1 : ℕ) + 1 + 1 : ℝ) *
          ((2 * r + 1 : ℕ) + 1)) := mul_le_mul ih h1 (by norm_num) (by positivity)
      _ = _ := by push_cast; ring

lemma domPS_sinS_uM : DomPS sinS uM := fun k => by
  rw [coeff_sinS, uM, coeff_mk]
  split_ifs with hk
  · simp
  · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast,
      show (2 * r + 1) / 2 = r by lia, one_div_pow, one_div]
    rw [one_div]; exact inv_anti₀ (by positivity) (six_pow_le_factorial r)

lemma sum_uM_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ^ 2 < 6) (K : ℕ) :
    ∑ k ∈ Finset.range K, coeff k uM * x ^ k ≤ x / (1 - x ^ 2 / 6) := by
  have hnn : NonnegPS uM := domPS_sinS_uM.nonneg
  refine (sum_le_sum_two_mul (fun k => mul_nonneg (hnn k) (pow_nonneg hx0 k)) K).trans ?_
  have : ∀ r, coeff (2 * r) uM * x ^ (2 * r) + coeff (2 * r + 1) uM * x ^ (2 * r + 1) =
      x * (x ^ 2 / 6) ^ r := by
    intro r
    rw [uM, coeff_mk, coeff_mk, ite_eq_left (even_two_mul r), ite_eq_right (by simp [parity_simps]),
      show (2 * r + 1) / 2 = r by lia]
    rw [pow_succ, pow_mul, div_pow, div_pow, one_pow]; ring
  simp_rw [this]
  have hg := geom_partial_le (y := x ^ 2 / 6) (by positivity) (by linarith) K
  rw [← Finset.mul_sum, div_eq_mul_one_div x]
  exact mul_le_mul_of_nonneg_left hg hx0

/-! ### The majorant of `w` -/

lemma secS_sub_cosS : secS - cosS = X ^ 2 * wS := by
  rw [← secS_mul_sinS_sq]
  have h := sinS_sq_add_cosS_sq
  have h2 : secS * cosS = 1 := by rw [mul_comm]; exact cosS_mul_secS
  linear_combination (-secS) * h + cosS * h2

lemma coeff_wS (k : ℕ) : coeff k wS = coeff (k + 2) secS - coeff (k + 2) cosS := by
  rw [← map_sub, secS_sub_cosS, coeff_X_pow_mul', ite_eq_left (by lia), Nat.add_sub_cancel]

lemma coeff_secS_even {m : ℕ} (hm : Even m) : coeff m secS = eulerCoeff m := by
  rw [eulerCoeff_eq_beta, beta_parity (j := 1) (by simp [hm]), add_zero, beta, pow_zero, mul_one]

/-- `1/(k+2)! ≤ (41/100)(2/π)^{k+3}` for `k ≥ 2`. -/
lemma inv_factorial_le (k : ℕ) (hk : 2 ≤ k) :
    1 / ((k + 2).factorial : ℝ) ≤ 41 / 100 * (2 / π) ^ (k + 3) := by
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  induction k, hk using Nat.le_induction with
  | base =>
    norm_num [Nat.factorial]
    have hp5 : π ^ 5 ≤ 3.1416 ^ 5 := pow_le_pow_left₀ (by positivity) hpi'.le 5
    have hpos : 0 < π ^ 5 := by positivity
    rw [div_pow, show (41 / 100 : ℝ) * (2 ^ 5 / π ^ 5) = (41 / 100 * 2 ^ 5) / π ^ 5 by ring,
      le_div_iff₀ hpos]
    norm_num at hp5 ⊢; linarith
  | succ k hk ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    push_cast
    have hf : (0 : ℝ) < ((k + 2).factorial : ℝ) := by positivity
    have hk' : (5 : ℝ) ≤ (k : ℝ) + 2 + 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h2pi : 1 / ((k : ℝ) + 2 + 1) ≤ 2 / π := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    calc 1 / (((k : ℝ) + 2 + 1) * ((k + 2).factorial : ℝ))
        = 1 / ((k + 2).factorial : ℝ) * (1 / ((k : ℝ) + 2 + 1)) := by
          field_simp
      _ ≤ 41 / 100 * (2 / π) ^ (k + 3) * (2 / π) :=
          mul_le_mul ih h2pi (by positivity) (by positivity)
      _ = _ := by ring

/-- The constant in the majorant of `w`. -/
noncomputable def cW : ℝ := 63 / 25

noncomputable def wM : ℝ⟦X⟧ :=
  mk (fun k => if k = 0 then 1 else if Even k then cW * (2 / π) ^ (k + 3) else 0)

lemma domPS_wS_wM : DomPS wS wM := fun k => by
  rw [wM, coeff_mk]
  split_ifs with h0 hk
  · subst h0; rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_wS, abs_one]
  · have hk2 : 2 ≤ k := by obtain ⟨r, rfl⟩ := hk; lia
    have hke : Even (k + 2) := by simpa [Nat.even_add] using hk
    rw [coeff_wS, coeff_secS_even hke]
    have he := eulerCoeff_le (k := k + 2) (by lia)
    have hS := Ssum_le_of_three_le (s := k + 2 + 1) (by lia)
    have hpos := eulerCoeff_pos (k + 2)
    have hc := abs_coeff_cosS_le (k + 2)
    have hfac := inv_factorial_le k hk2
    have hp : (0 : ℝ) ≤ (2 / π) ^ (k + 3) := by have := Real.pi_pos; positivity
    rw [show k + 2 + 1 = k + 3 by ring] at he
    calc |eulerCoeff (k + 2) - coeff (k + 2) cosS| ≤ |eulerCoeff (k + 2)| + |coeff (k + 2) cosS| :=
          abs_sub _ _
      _ ≤ 2 * (2 / π) ^ (k + 3) * (1 + 29 / 540) + 41 / 100 * (2 / π) ^ (k + 3) := by
          rw [abs_of_pos hpos]
          refine add_le_add (he.trans ?_) (hc.trans hfac)
          apply mul_le_mul_of_nonneg_left (by linarith); positivity
      _ ≤ cW * (2 / π) ^ (k + 3) := by rw [cW]; nlinarith
  · rw [isEvenPS_wS.coeff_odd (Nat.not_even_iff_odd.mp hk), abs_zero]

lemma sum_wM_le (K : ℕ) :
    ∑ k ∈ Finset.range K, coeff k wM * (π / 6) ^ k ≤ 1 + cW / π ^ 3 := by
  have hpi := Real.pi_pos
  have hnn : NonnegPS wM := domPS_wS_wM.nonneg
  refine (sum_le_sum_two_mul
    (fun k => mul_nonneg (hnn k) (pow_nonneg (by positivity) k)) K).trans ?_
  have hterm : ∀ r, coeff (2 * r) wM * (π / 6) ^ (2 * r) +
      coeff (2 * r + 1) wM * (π / 6) ^ (2 * r + 1) =
      (if r = 0 then 1 else 0) + (if r = 0 then 0 else cW * (8 / π ^ 3) * (1 / 9) ^ r) := by
    intro r
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp [wM]
    · have h1 : ¬ Even (2 * r + 1) := by simp [parity_simps]
      have h2 : 2 * r ≠ 0 := by lia
      have h3 : 2 * r + 1 ≠ 0 := by lia
      have h4 : r ≠ 0 := by lia
      simp only [wM, coeff_mk, h1, h2, h3, h4, even_two_mul, ite_false, ite_true, zero_mul,
        add_zero, zero_add]
      rw [show 2 * r + 3 = 3 + 2 * r by ring, pow_add, pow_mul, pow_mul]
      have h9 : (2 / π) ^ 2 * (π / 6) ^ 2 = 1 / 9 := by field_simp; ring
      calc cW * ((2 / π) ^ 3 * ((2 / π) ^ 2) ^ r) * ((π / 6) ^ 2) ^ r
          = cW * (2 / π) ^ 3 * ((2 / π) ^ 2 * (π / 6) ^ 2) ^ r := by rw [mul_pow]; ring
        _ = _ := by rw [h9, div_pow]; ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ r ∈ Finset.range K, (if r = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
  have h2 : ∑ r ∈ Finset.range K, (if r = 0 then (0 : ℝ) else cW * (8 / π ^ 3) * (1 / 9) ^ r) ≤
      cW / π ^ 3 := by
    have hc : 0 ≤ cW * (8 / π ^ 3) := by rw [cW]; positivity
    calc ∑ r ∈ Finset.range K, (if r = 0 then (0 : ℝ) else cW * (8 / π ^ 3) * (1 / 9) ^ r)
        ≤ ∑ r ∈ Finset.range (K + 1),
            (if r = 0 then (0 : ℝ) else cW * (8 / π ^ 3) * (1 / 9) ^ r) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          intro r _ _; split_ifs <;> positivity
      _ = ∑ r ∈ Finset.range K, cW * (8 / π ^ 3) * (1 / 9) ^ (r + 1) := by
          rw [Finset.sum_range_succ']; simp
      _ = cW * (8 / π ^ 3) * (1 / 9) * ∑ r ∈ Finset.range K, (1 / 9 : ℝ) ^ r := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
      _ ≤ cW * (8 / π ^ 3) * (1 / 9) * (1 / (1 - 1 / 9)) :=
          mul_le_mul_of_nonneg_left (geom_partial_le (by norm_num) (by norm_num) K)
            (by positivity)
      _ = cW / π ^ 3 := by field_simp; ring
  linarith

/-! ### Bounds for `∑ |φ_{jk}| x^k` at `x = π/6` -/

lemma pi_div_six_sq_lt : (π / 6) ^ 2 < 6 := by
  have := Real.pi_lt_d4; nlinarith [Real.pi_pos]

lemma abs_phi_le (j k : ℕ) : |phi j k| ≤ coeff k (wM * uM ^ j) := by
  rw [phi_eq]; exact (domPS_wS_wM.mul (domPS_sinS_uM.pow j)) k

lemma sum_abs_phi_le (j K : ℕ) :
    ∑ k ∈ Finset.range K, |phi j k| * (π / 6) ^ k ≤
      (1 + cW / π ^ 3) * ((π / 6) / (1 - (π / 6) ^ 2 / 6)) ^ j := by
  have hpi := Real.pi_pos
  have hx : (0 : ℝ) ≤ π / 6 := by positivity
  have hW : NonnegPS wM := domPS_wS_wM.nonneg
  have hU : NonnegPS uM := domPS_sinS_uM.nonneg
  calc ∑ k ∈ Finset.range K, |phi j k| * (π / 6) ^ k
      ≤ ∑ k ∈ Finset.range K, coeff k (wM * uM ^ j) * (π / 6) ^ k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (abs_phi_le j k)
          (pow_nonneg hx k))
    _ ≤ (∑ k ∈ Finset.range K, coeff k wM * (π / 6) ^ k) *
          (∑ k ∈ Finset.range K, coeff k (uM ^ j) * (π / 6) ^ k) :=
        sum_coeff_mul_le hW (hU.pow j) hx K
    _ ≤ (1 + cW / π ^ 3) * ((π / 6) / (1 - (π / 6) ^ 2 / 6)) ^ j := by
        apply mul_le_mul (sum_wM_le K) _ (Finset.sum_nonneg (fun k _ =>
          mul_nonneg ((hU.pow j) k) (pow_nonneg hx k))) (by rw [cW]; positivity)
        refine (sum_coeff_pow_le hU hx K j).trans ?_
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => mul_nonneg (hU k)
          (pow_nonneg hx k))) (sum_uM_le hx pi_div_six_sq_lt K) j

lemma sum_range_add_two (f : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 2), f k = f 0 + f 1 + ∑ k ∈ Finset.range K, f (k + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']; ring

lemma sum_abs_phi_tail_le (j K : ℕ) :
    ∑ k ∈ Finset.range K, |phi j (k + 2)| * (π / 6) ^ (k + 2) ≤
      (1 + cW / π ^ 3) * ((π / 6) / (1 - (π / 6) ^ 2 / 6)) ^ j := by
  refine le_trans ?_ (sum_abs_phi_le j (K + 2))
  rw [sum_range_add_two]
  have := Real.pi_pos
  have : 0 ≤ |phi j 0| * (π / 6) ^ 0 + |phi j 1| * (π / 6) ^ 1 := by positivity
  linarith

lemma sum_abs_phi_tail_zero_le (K : ℕ) :
    ∑ k ∈ Finset.range K, |phi 0 (k + 2)| * (π / 6) ^ (k + 2) ≤ cW / π ^ 3 := by
  have h := sum_abs_phi_le 0 (K + 2)
  rw [sum_range_add_two, phi_zero, phi_one, pow_zero, mul_one] at h
  simp at h
  linarith

lemma sum_abs_phi_tail_one_le (K : ℕ) :
    ∑ k ∈ Finset.range K, |phi 1 (k + 2)| * (π / 6) ^ (k + 2) ≤
      (1 + cW / π ^ 3) * ((π / 6) / (1 - (π / 6) ^ 2 / 6)) - π / 6 := by
  have h := sum_abs_phi_le 1 (K + 2)
  rw [sum_range_add_two, phi_zero, phi_one, pow_one] at h
  have := Real.pi_pos
  simp at h
  linarith

end RealRooted.CenteredEulerian
