/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.PhiBound
public import RealRooted.CenteredEulerian.RootCriterion
import RealRooted.CenteredEulerian.HBound
import RealRooted.CenteredEulerian.ArcsinBound

/-!
# The weighted column bound (B.1)

Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.

We combine the change-of-basis formula (B.6) with the coefficient estimates to prove
`ColumnBound`, and hence the centered root disk for the polynomials `p_n`.
-/

@[expose] public section

open PowerSeries Real

namespace RealRooted.CenteredEulerian

lemma weighted_sum_le {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * y i ≤
      2 * ∑ i ∈ Finset.range (N + 2), y i - y 0 - y 1 := by
  have h1 : ∑ i ∈ Finset.range N, columnWeight i * y i ≤
      ∑ i ∈ Finset.range (N + 2), columnWeight i * y i :=
    Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      (fun i _ _ => mul_nonneg (columnWeight_pos i).le (hy i))
  have h2 : ∑ i ∈ Finset.range (N + 2), columnWeight i * y i =
      y 0 + y 1 + 2 * ∑ i ∈ Finset.range N, y (i + 2) := by
    rw [sum_range_add_two, Finset.mul_sum]; simp [columnWeight]
  have h3 := sum_range_add_two y N
  linarith

/-! ### Sums of the three main series -/

lemma sum_abs_hS_succ_le (M : ℕ) :
    ∑ i ∈ Finset.range M, |coeff (i + 1) hS| ≤ 1 - 1 / aConst := sum_abs_coeff_hS_le M

lemma coeff_hS_one : coeff 1 hS = 0 := isEvenPS_hS.coeff_odd (by decide)

lemma coeff_hS_three : coeff 3 hS = 0 := isEvenPS_hS.coeff_odd (by decide)

lemma sum_abs_hS_succ_succ_le (M : ℕ) :
    ∑ i ∈ Finset.range M, |coeff (i + 2) hS| ≤ 1 - 1 / aConst := by
  have h := sum_abs_coeff_hS_le (M + 1)
  rw [Finset.sum_range_succ', coeff_hS_one, abs_zero, add_zero] at h
  exact h

lemma sum_abs_qS_succ_succ_le (M : ℕ) :
    ∑ i ∈ Finset.range M, |coeff (i + 2) qS| ≤ 1 := by
  have h := sum_abs_coeff_qS_le (M + 1)
  rw [Finset.sum_range_succ', isEvenPS_qS.coeff_odd (by decide), abs_zero, add_zero] at h
  exact h

lemma coeff_qS_three : coeff 3 qS = 0 := isEvenPS_qS.coeff_odd (by decide)

/-- Weighted column norm of the `h`-part. -/
lemma weighted_h_col0_le (N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ 0)| ≤ 5 / 3 - 2 / aConst := by
  simp only [pow_zero, mul_one]
  refine (weighted_sum_le (fun i => abs_nonneg _) N).trans ?_
  have := sum_abs_hS_succ_succ_le (N + 2)
  rw [coeff_hS_two, coeff_hS_three]
  have : 2 / aConst = 2 * (1 / aConst) := by ring
  rw [abs_zero, show |(-1 / 3 : ℝ)| = 1 / 3 by norm_num [abs_div]]
  linarith

lemma weighted_h_col1_le (N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ 1)| ≤ 5 / 3 - 2 / aConst := by
  have hc : ∀ i, coeff (i + 2) (hS * X ^ 1) = coeff (i + 1) hS := fun i => by
    rw [coeff_mul_X_pow', ite_eq_left (by lia), show i + 2 - 1 = i + 1 by lia]
  simp only [hc]
  refine (weighted_sum_le (fun i => abs_nonneg (coeff (i + 1) hS)) N).trans ?_
  have := sum_abs_hS_succ_le (N + 2)
  rw [zero_add, coeff_hS_one, show (1 : ℕ) + 1 = 2 from rfl, coeff_hS_two]
  have : 2 / aConst = 2 * (1 / aConst) := by ring
  rw [abs_zero, show |(-1 / 3 : ℝ)| = 1 / 3 by norm_num [abs_div]]
  linarith

lemma weighted_h_col_ge2_le (j N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ (j + 2))| ≤
      columnWeight j + 2 * (1 - 1 / aConst) := by
  have ha := one_lt_aConst
  have hc : ∀ i, coeff (i + 2) (hS * X ^ (j + 2)) = coeff i (hS * X ^ j) := fun i => by
    rw [coeff_mul_X_pow', coeff_mul_X_pow']
    split_ifs <;> lia
  simp only [hc]
  have hpos : 0 ≤ columnWeight j + 2 * (1 - 1 / aConst) := by
    have := columnWeight_pos j
    have : 1 / aConst < 1 := by rw [div_lt_one (by linarith)]; exact ha
    linarith
  rcases Nat.lt_or_ge j N with hN | hN
  · obtain ⟨M, rfl⟩ : ∃ M, N = j + (M + 1) := ⟨N - j - 1, by lia⟩
    rw [Finset.sum_range_add, Finset.sum_eq_zero (fun i hi => by
      rw [coeff_mul_X_pow', ite_eq_right (by simp at hi; lia), abs_zero, mul_zero]), zero_add,
      Finset.sum_range_succ']
    simp only [add_zero, coeff_mul_X_pow', le_refl, ite_true, Nat.sub_self, coeff_hS_zero,
      abs_one, mul_one]
    have hsum : ∑ i ∈ Finset.range M, columnWeight (j + (i + 1)) *
        |if j ≤ j + (i + 1) then coeff (j + (i + 1) - j) hS else 0| ≤
        2 * ∑ i ∈ Finset.range M, |coeff (i + 1) hS| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      rw [ite_eq_left (by lia), show j + (i + 1) - j = i + 1 by lia]
      exact mul_le_mul_of_nonneg_right (columnWeight_le_two _) (abs_nonneg _)
    have := sum_abs_hS_succ_le M
    linarith
  · rw [Finset.sum_eq_zero (fun i hi => by
      rw [coeff_mul_X_pow', ite_eq_right (by simp at hi; lia), abs_zero, mul_zero])]
    exact hpos

lemma weighted_qS_le (N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) qS| ≤ 3 / 2 := by
  refine (weighted_sum_le (fun i => abs_nonneg (coeff (i + 2) qS)) N).trans ?_
  have := sum_abs_qS_succ_succ_le (N + 2)
  rw [coeff_qS_two, coeff_qS_three]
  norm_num
  linarith

lemma weighted_qf_le (N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (qS * fS)| ≤ 5 / 3 := by
  refine (weighted_sum_le (fun i => abs_nonneg (coeff (i + 2) (qS * fS))) N).trans ?_
  have := sum_abs_coeff_qf_le (N + 2)
  rw [coeff_qf_two, coeff_qf_three]
  norm_num
  linarith

/-! ### The tail -/

lemma sum_abs_qS_le (M : ℕ) : ∑ n ∈ Finset.range M, |coeff n qS| ≤ 2 := by
  rcases M with _ | M
  · simp
  rw [Finset.sum_range_succ', coeff_zero_eq_constantCoeff_apply, constantCoeff_qS, abs_one]
  have := sum_abs_coeff_qS_le M
  linarith

lemma nonnegPS_fS : NonnegPS fS := coeff_fS_nonneg

lemma sum_abs_alpha_le (M m : ℕ) :
    ∑ n ∈ Finset.range M, |alpha n m| ≤ 2 * (π / 2) ^ m := by
  have hdom : DomPS (qS * fS ^ m) (absPS qS * fS ^ m) :=
    DomPS.mul (fun n => by rw [coeff_absPS]) (fun n => by
      rw [abs_of_nonneg ((nonnegPS_fS.pow m) n)])
  calc ∑ n ∈ Finset.range M, |alpha n m|
      ≤ ∑ n ∈ Finset.range M, coeff n (absPS qS * fS ^ m) * 1 ^ n :=
        Finset.sum_le_sum (fun n _ => by rw [one_pow, mul_one]; exact hdom n)
    _ ≤ (∑ n ∈ Finset.range M, coeff n (absPS qS) * 1 ^ n) *
          (∑ n ∈ Finset.range M, coeff n (fS ^ m) * 1 ^ n) :=
        sum_coeff_mul_le (nonnegPS_absPS qS) (nonnegPS_fS.pow m) zero_le_one M
    _ ≤ 2 * (π / 2) ^ m := by
        have h1 : ∑ n ∈ Finset.range M, coeff n (absPS qS) * 1 ^ n ≤ 2 := by
          simp only [one_pow, mul_one, coeff_absPS]; exact sum_abs_qS_le M
        have h2 : ∑ n ∈ Finset.range M, coeff n (fS ^ m) * 1 ^ n ≤ (π / 2) ^ m := by
          refine (sum_coeff_pow_le nonnegPS_fS zero_le_one M m).trans ?_
          simp only [one_pow, mul_one]
          exact pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => nonnegPS_fS n))
            (sum_coeff_fS_le M) m
        apply mul_le_mul h1 h2 (Finset.sum_nonneg (fun n _ =>
          mul_nonneg ((nonnegPS_fS.pow m) n) (by norm_num))) (by norm_num)

/-- The residual (tail) term of `R_{ij}`. -/
noncomputable def tailR (j i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 1), (eulerRatio (k + 2) - aConst) * alpha (i + 2) (k + 2) *
    phi j (k + 2)

lemma abs_eulerRatio_sub_le' (k : ℕ) :
    |eulerRatio (k + 2) - aConst| ≤ aConst * Ssum 3 * (1 / 3) ^ k := by
  have h1 := abs_eulerRatio_sub_le (k := k + 2) (by lia)
  have h2 := Ssum_shift_le k
  have ha : 0 ≤ aConst := by rw [aConst]; positivity
  rw [show k + 2 + 1 = k + 3 by ring] at h1
  calc _ ≤ aConst * Ssum (k + 3) := h1
    _ ≤ aConst * ((1 / 3) ^ k * Ssum 3) := mul_le_mul_of_nonneg_left h2 ha
    _ = _ := by ring

lemma sum_tailR_le (j N : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |tailR j i| ≤
      36 * aConst * Ssum 3 * ∑ k ∈ Finset.range N, |phi j (k + 2)| * (π / 6) ^ (k + 2) := by
  have ha : 0 ≤ aConst := by rw [aConst]; positivity
  have hS := Ssum_nonneg 3
  set t : ℕ → ℕ → ℝ := fun i k =>
    |eulerRatio (k + 2) - aConst| * |alpha (i + 2) (k + 2)| * |phi j (k + 2)| with ht
  have htn : ∀ i k, 0 ≤ t i k := fun i k => by simp only [ht]; positivity
  have step1 : ∀ i ∈ Finset.range N, columnWeight i * |tailR j i| ≤
      2 * ∑ k ∈ Finset.range N, t i k := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e1 : |tailR j i| ≤ ∑ k ∈ Finset.range (i + 1), t i k := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro k _; simp only [ht, abs_mul]
    have e2 : ∑ k ∈ Finset.range (i + 1), t i k ≤ ∑ k ∈ Finset.range N, t i k :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro k; simp; lia) (fun k _ _ => htn i k)
    exact mul_le_mul (columnWeight_le_two i) (e1.trans e2) (abs_nonneg _) (by norm_num)
  refine (Finset.sum_le_sum step1).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have step2 : ∀ k ∈ Finset.range N, ∑ i ∈ Finset.range N, t i k ≤
      18 * aConst * Ssum 3 * (|phi j (k + 2)| * (π / 6) ^ (k + 2)) := by
    intro k _
    have hal : ∑ i ∈ Finset.range N, |alpha (i + 2) (k + 2)| ≤ 2 * (π / 2) ^ (k + 2) := by
      refine le_trans ?_ (sum_abs_alpha_le (N + 2) (k + 2))
      rw [sum_range_add_two]
      have : 0 ≤ |alpha 0 (k + 2)| + |alpha 1 (k + 2)| := by positivity
      linarith
    have hb := abs_eulerRatio_sub_le' k
    calc ∑ i ∈ Finset.range N, t i k
        = |eulerRatio (k + 2) - aConst| * |phi j (k + 2)| *
            ∑ i ∈ Finset.range N, |alpha (i + 2) (k + 2)| := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; simp only [ht]; ring
      _ ≤ aConst * Ssum 3 * (1 / 3) ^ k * |phi j (k + 2)| * (2 * (π / 2) ^ (k + 2)) := by
          apply mul_le_mul _ hal (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (by positivity)
          exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = 18 * aConst * Ssum 3 * (|phi j (k + 2)| * (π / 6) ^ (k + 2)) := by
          rw [show (π / 6) ^ (k + 2) = (π / 2) ^ (k + 2) * (1 / 3) ^ k * (1 / 9) by
            rw [show π / 6 = π / 2 * (1 / 3) by ring, mul_pow, pow_add]; ring]
          ring
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum step2) (by norm_num)).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]; ring

/-! ### Combination -/

lemma abs_rMat_le (i j : ℕ) :
    |rMat i j| ≤ aConst * |coeff (i + 2) (hS * X ^ j)|
      + (if j = 0 then |2 - aConst| * |coeff (i + 2) qS| else 0)
      + (if j = 1 then |3 - aConst| * |coeff (i + 2) (qS * fS)| else 0)
      + |tailR j i| := by
  have ha : 0 ≤ aConst := by rw [aConst]; positivity
  rw [rMat_decomp, tailR]
  have h4 : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := fun a b c d => by
    have := abs_add_le (a + b + c) d; have := abs_add_le (a + b) c; have := abs_add_le a b
    linarith
  refine (h4 _ _ _ _).trans (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl)
  · rw [abs_mul, abs_of_nonneg ha]
  · split_ifs <;> simp [abs_mul]
  · split_ifs <;> simp [abs_mul]

lemma column_le (N j : ℕ) :
    ∑ i ∈ Finset.range N, columnWeight i * |rMat i j| ≤
      aConst * ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ j)|
      + (if j = 0 then |2 - aConst| * (3 / 2) else 0)
      + (if j = 1 then |3 - aConst| * (5 / 3) else 0)
      + 36 * aConst * Ssum 3 * ∑ k ∈ Finset.range N, |phi j (k + 2)| * (π / 6) ^ (k + 2) := by
  have h1 : ∑ i ∈ Finset.range N, columnWeight i * |rMat i j| ≤
      ∑ i ∈ Finset.range N, (aConst * (columnWeight i * |coeff (i + 2) (hS * X ^ j)|)
        + (if j = 0 then |2 - aConst| * (columnWeight i * |coeff (i + 2) qS|) else 0)
        + (if j = 1 then |3 - aConst| * (columnWeight i * |coeff (i + 2) (qS * fS)|) else 0)
        + columnWeight i * |tailR j i|) := by
    apply Finset.sum_le_sum; intro i _
    have := mul_le_mul_of_nonneg_left (abs_rMat_le i j) (columnWeight_pos i).le
    refine this.trans (le_of_eq ?_)
    split_ifs <;> ring
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add (add_le_add (add_le_add le_rfl ?_) ?_) (sum_tailR_le j N)
  · split_ifs
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (weighted_qS_le N) (abs_nonneg _)
    · simp
  · split_ifs
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (weighted_qf_le N) (abs_nonneg _)
    · simp

/-! ### Numerical constants -/

lemma aConst_bounds : 2.4672 < aConst ∧ aConst < 2.4675 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  rw [aConst]; constructor <;> nlinarith

lemma tail_const_le : 36 * aConst * Ssum 3 ≤ 4.771 := by
  have := aConst_bounds; have := Ssum_three_le; have := Ssum_nonneg 3
  nlinarith

lemma tail_const_nonneg : 0 ≤ 36 * aConst * Ssum 3 := by
  obtain ⟨h1, _⟩ := aConst_bounds
  have := Ssum_nonneg 3
  have : 0 ≤ aConst := by linarith
  positivity

lemma wb_le : 1 + cW / π ^ 3 ≤ 1.0813 := by
  have h1 := Real.pi_gt_d4
  have h3 : (3.1415 : ℝ) ^ 3 ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
  have hp : 0 < π ^ 3 := by positivity
  have : (63 / 25 : ℝ) / π ^ 3 ≤ 0.0813 := by
    rw [div_le_iff₀ hp]; norm_num at h3 ⊢; linarith
  rw [cW]; linarith

lemma ub_bounds : 0 ≤ (π / 6) / (1 - (π / 6) ^ 2 / 6) ∧
    (π / 6) / (1 - (π / 6) ^ 2 / 6) ≤ 0.5487 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  have hd : 0.9543 ≤ 1 - (π / 6) ^ 2 / 6 := by nlinarith
  constructor
  · apply div_nonneg (by linarith) (by linarith)
  · rw [div_le_iff₀ (by linarith)]; nlinarith

lemma wb_ub_sub_le : (1 + cW / π ^ 3) * ((π / 6) / (1 - (π / 6) ^ 2 / 6)) - π / 6 ≤ 0.07 := by
  have h1 := Real.pi_gt_d4
  have hw := wb_le
  have hu := ub_bounds
  have hw0 : 0 ≤ 1 + cW / π ^ 3 := by rw [cW]; positivity
  have : (1 + cW / π ^ 3) * ((π / 6) / (1 - (π / 6) ^ 2 / 6)) ≤ 1.0813 * 0.5487 :=
    mul_le_mul hw hu.2 hu.1 (by norm_num)
  linarith

/-! ### The column bound -/

theorem columnBound : ColumnBound := by
  intro N j
  have hc := column_le N j
  have ha := aConst_bounds
  have hT := tail_const_le
  have hT0 := tail_const_nonneg
  have hw := wb_le
  have hu := ub_bounds
  have hw0 : 0 ≤ 1 + cW / π ^ 3 := by rw [cW]; positivity
  have hpi := Real.pi_pos
  have hdiv : 2 / aConst * aConst = 2 := div_mul_cancel₀ _ (by linarith)
  rcases j with _ | _ | j
  · -- column 0
    have hA := weighted_h_col0_le N
    have hP := sum_abs_phi_tail_zero_le N
    simp only [ite_true, show (0 : ℕ) ≠ 1 by decide, ite_false, add_zero] at hc
    rw [abs_of_neg (by linarith : 2 - aConst < 0)] at hc
    have e1 : aConst * ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ 0)| ≤
        aConst * (5 / 3 - 2 / aConst) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have e2 : 36 * aConst * Ssum 3 * ∑ k ∈ Finset.range N, |phi 0 (k + 2)| * (π / 6) ^ (k + 2) ≤
        4.771 * (cW / π ^ 3) := mul_le_mul hT hP (Finset.sum_nonneg (fun k _ => by positivity))
          (by norm_num)
    have e3 : cW / π ^ 3 ≤ 0.0813 := by linarith
    have e4 : aConst * (5 / 3 - 2 / aConst) = 5 / 3 * aConst - 2 := by
      rw [mul_sub, mul_comm aConst (2 / aConst), hdiv]; ring
    rw [show columnWeight 0 = 1 by simp [columnWeight]]
    linarith
  · -- column 1
    have hA := weighted_h_col1_le N
    have hP := sum_abs_phi_tail_one_le N
    simp only [ite_true, show (0 + 1 : ℕ) ≠ 0 by decide, ite_false, add_zero, zero_add] at hc
    rw [abs_of_pos (by linarith : 0 < 3 - aConst)] at hc
    have e1 : aConst * ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ 1)| ≤
        aConst * (5 / 3 - 2 / aConst) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have hP' := hP.trans wb_ub_sub_le
    have e2 : 36 * aConst * Ssum 3 * ∑ k ∈ Finset.range N, |phi 1 (k + 2)| * (π / 6) ^ (k + 2) ≤
        4.771 * 0.07 := mul_le_mul hT hP' (Finset.sum_nonneg (fun k _ => by positivity))
          (by norm_num)
    have e4 : aConst * (5 / 3 - 2 / aConst) = 5 / 3 * aConst - 2 := by
      rw [mul_sub, mul_comm aConst (2 / aConst), hdiv]; ring
    rw [show columnWeight (0 + 1) = 1 by simp [columnWeight]]
    linarith
  · -- columns `j + 2`
    have hA := weighted_h_col_ge2_le j N
    have hP := sum_abs_phi_tail_le (j + 2) N
    simp only [show j + 1 + 1 ≠ 0 by lia, show j + 1 + 1 ≠ 1 by lia, ite_false,
      add_zero] at hc
    have hom : columnWeight (j + 1 + 1) = 2 := by simp [columnWeight]
    rw [hom]
    set U := (π / 6) / (1 - (π / 6) ^ 2 / 6) with hU
    set W := 1 + cW / π ^ 3 with hW
    have e1 : aConst * ∑ i ∈ Finset.range N, columnWeight i * |coeff (i + 2) (hS * X ^ (j + 2))| ≤
        aConst * (columnWeight j + 2 * (1 - 1 / aConst)) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have e5 : aConst * (columnWeight j + 2 * (1 - 1 / aConst)) =
        aConst * columnWeight j + 2 * aConst - 2 := by
      have : aConst * (1 / aConst) = 1 := by rw [mul_one_div]; exact div_self (by linarith)
      linear_combination (-2) * this
    have hU2 : U ^ (j + 2) ≤ U ^ 2 := pow_le_pow_of_le_one hu.1 (by linarith) (by lia)
    have hU2' : U ^ 2 ≤ 0.5487 ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range N, |phi (j + 2) (k + 2)| * (π / 6) ^ (k + 2) :=
      Finset.sum_nonneg (fun k _ => by positivity)
    rcases Nat.lt_or_ge j 2 with hj | hj
    · have hom' : columnWeight j = 1 := by simp [columnWeight, hj]
      have e2 : 36 * aConst * Ssum 3 *
          ∑ k ∈ Finset.range N, |phi (j + 2) (k + 2)| * (π / 6) ^ (k + 2) ≤
          4.771 * (1.0813 * 0.5487 ^ 2) := by
        refine mul_le_mul hT (hP.trans ?_) hsum0 (by norm_num)
        exact mul_le_mul hw (hU2.trans hU2') (pow_nonneg hu.1 _) (by norm_num)
      rw [hom'] at e5
      norm_num at e2 ⊢
      nlinarith
    · have hom' : columnWeight j = 2 := by simp [columnWeight]; lia
      have hU4 : U ^ (j + 2) ≤ U ^ 4 := pow_le_pow_of_le_one hu.1 (by linarith) (by lia)
      have hU4' : U ^ 4 ≤ 0.5487 ^ 4 := pow_le_pow_left₀ hu.1 hu.2 4
      have e2 : 36 * aConst * Ssum 3 *
          ∑ k ∈ Finset.range N, |phi (j + 2) (k + 2)| * (π / 6) ^ (k + 2) ≤
          4.771 * (1.0813 * 0.5487 ^ 4) := by
        refine mul_le_mul hT (hP.trans ?_) hsum0 (by norm_num)
        exact mul_le_mul hw (hU4.trans hU4') (pow_nonneg hu.1 _) (by norm_num)
      rw [hom'] at e5
      norm_num at e2 ⊢
      nlinarith

/-- **Centered root disk for `p_n`**: every complex zero `c` of `p_n` (`n ≥ 2`) satisfies
`|c|² < 13/3`. -/
theorem polynomial_root_normSq_lt {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : pC n c = 0) :
    Complex.normSq c < 13 / 3 :=
  root_bound_of_columnBound columnBound hn hc

end RealRooted.CenteredEulerian
