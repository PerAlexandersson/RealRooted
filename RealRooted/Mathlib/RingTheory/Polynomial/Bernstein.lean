/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Bernstein

import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.Polynomial

/-!
# Bernstein polynomial expansions

This file proves three identities and positivity criteria for the Bernstein basis, from
RealRooted issues #1933 and #1937. The proof was found by Aristotle (Harmonic).
-/

@[expose] public section

open Finset

noncomputable section

namespace Polynomial

/-- The coefficient of the degree-`n` Bernstein polynomial indexed by `i` in `p`. -/
def bernsteinCoeff (p : ℝ[X]) (n i : ℕ) : ℝ :=
  ∑ k ∈ range (i + 1), p.coeff k * ((i.choose k : ℝ) / (n.choose k : ℝ))

private lemma X_pow_eq_sum_bernsteinPolynomial (n k : ℕ) (hk : k ≤ n) :
    (X : ℝ[X]) ^ k = ∑ i ∈ range (n + 1),
      C ((i.choose k : ℝ) / (n.choose k : ℝ)) * bernsteinPolynomial ℝ n i := by
  have hnk : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have h1 : (X : ℝ[X]) ^ k = X ^ k * (X + (1 - X)) ^ (n - k) := by simp
  rw [h1, add_pow, mul_sum]
  have hr : n + 1 = k + (n - k + 1) := by lia
  conv_rhs => rw [hr, sum_range_add]
  have hz : ∑ x ∈ range k,
      C ((x.choose k : ℝ) / (n.choose k : ℝ)) * bernsteinPolynomial ℝ n x = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_range] at hx
    simp [Nat.choose_eq_zero_of_lt hx]
  rw [hz, zero_add]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hc := Nat.choose_mul (n := n) (k := k + j) (s := k) (by lia)
  rw [show k + j - k = j by lia] at hc
  have hc' : ((n.choose (k + j) : ℝ)) * ((k + j).choose k : ℝ) =
      (n.choose k : ℝ) * ((n - k).choose j : ℝ) := by
    exact_mod_cast hc
  rw [bernsteinPolynomial, show n - (k + j) = n - k - j by lia]
  have hC : C ((((k + j).choose k : ℕ) : ℝ) / (n.choose k : ℝ)) *
      (n.choose (k + j) : ℝ[X]) = ((n - k).choose j : ℝ[X]) := by
    rw [← C_eq_natCast, ← C_eq_natCast, ← C_mul]
    congr 1
    field_simp
    linarith [hc']
  calc
    X ^ k * (X ^ j * (1 - X) ^ (n - k - j) * ((n - k).choose j : ℝ[X])) =
        (C ((((k + j).choose k : ℕ) : ℝ) / (n.choose k : ℝ)) *
          (n.choose (k + j) : ℝ[X])) *
          (X ^ (k + j) * (1 - X) ^ (n - k - j)) := by rw [hC]; ring
    _ = _ := by ring

/-- A polynomial of degree at most `n` expanded in the degree-`n` Bernstein basis. -/
theorem eq_sum_bernsteinPolynomial_of_natDegree_le (p : ℝ[X]) (n : ℕ)
    (hn : p.natDegree ≤ n) :
    p = ∑ i ∈ range (n + 1),
      C (p.bernsteinCoeff n i) * bernsteinPolynomial ℝ n i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n := n + 1) (by lia)]
  have step : ∀ k ∈ range (n + 1), C (p.coeff k) * X ^ k =
      ∑ i ∈ range (n + 1),
        C (p.coeff k * ((i.choose k : ℝ) / (n.choose k : ℝ))) *
          bernsteinPolynomial ℝ n i := by
    intro k hk
    rw [mem_range] at hk
    rw [X_pow_eq_sum_bernsteinPolynomial n k (by lia), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [C_mul]
    ring
  rw [sum_congr rfl step, sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [← sum_mul, ← map_sum]
  congr 2
  symm
  apply sum_subset
  · intro x hx
    simp only [mem_range] at *
    lia
  · intro x _ hx
    simp only [mem_range, not_lt] at hx
    simp [Nat.choose_eq_zero_of_lt (show i < x by lia)]

private lemma choose_ratio_bound (n i k : ℕ) (hn : 0 < n) (hi : i ≤ n) (hk : k ≤ n) :
    |(i.choose k : ℝ) / (n.choose k) - ((i : ℝ) / n) ^ k| ≤ (k : ℝ) ^ 2 / n ∧
      0 ≤ (i.choose k : ℝ) / (n.choose k) ∧
      (i.choose k : ℝ) / (n.choose k) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k ≤ n := by lia
    obtain ⟨h1, h2, h3⟩ := ih hkn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have ht0 : (0 : ℝ) ≤ i / n := by positivity
    have ht1 : (i : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hi
    rcases Nat.lt_or_ge i (k + 1) with hik | hik
    · rw [Nat.choose_eq_zero_of_lt hik]
      simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg]
      refine ⟨?_, le_rfl, zero_le_one⟩
      rw [abs_of_nonneg (by positivity)]
      have hik' : (i : ℝ) ≤ k := by exact_mod_cast (by lia : i ≤ k)
      calc
        ((i : ℝ) / n) ^ (k + 1) ≤ (i : ℝ) / n :=
          pow_le_of_le_one ht0 ht1 (by lia)
        _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 / n := by
          apply div_le_div_of_nonneg_right _ hnpos.le
          push_cast
          nlinarith
    · set A := (i.choose k : ℝ) / (n.choose k) with hA
      set t := (i : ℝ) / n with ht
      have hkn' : k + 1 ≤ n := by lia
      have e1 : ((i.choose (k + 1) * (k + 1) : ℕ) : ℝ) =
          ((i.choose k * (i - k) : ℕ) : ℝ) := by
        rw [Nat.choose_succ_right_eq]
      have e2 : ((n.choose (k + 1) * (k + 1) : ℕ) : ℝ) =
          ((n.choose k * (n - k) : ℕ) : ℝ) := by
        rw [Nat.choose_succ_right_eq]
      push_cast [Nat.cast_sub (by lia : k ≤ i), Nat.cast_sub hkn] at e1 e2
      have hd : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
      have hb : (0 : ℝ) < n.choose (k + 1) := by
        exact_mod_cast Nat.choose_pos hkn'
      have hnk : (0 : ℝ) < (n : ℝ) - k := by
        have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn'
        linarith
      have hik1 : (k : ℝ) + 1 ≤ i := by exact_mod_cast hik
      have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
      have key : (i.choose (k + 1) : ℝ) * (n.choose k) * ((n : ℝ) - k) =
          (i.choose k) * ((i : ℝ) - k) * (n.choose (k + 1)) := by
        have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
        apply mul_right_cancel₀ hk1
        linear_combination ((n.choose k : ℝ) * ((n : ℝ) - k)) * e1 -
          ((i.choose k : ℝ) * ((i : ℝ) - k)) * e2
      set q := ((i : ℝ) - k) / ((n : ℝ) - k) with hq
      have hrat : (i.choose (k + 1) : ℝ) / (n.choose (k + 1)) = A * q := by
        rw [hA, hq, div_mul_div_comm, div_eq_div_iff hb.ne' (by positivity)]
        linear_combination key
      have hq0 : 0 ≤ q := div_nonneg (by linarith) hnk.le
      have hq1 : q ≤ 1 := by
        rw [div_le_one hnk]
        linarith
      have hqt : |q - t| ≤ k / n := by
        have : q - t = -((k : ℝ) * (n - i) / (n * (n - k))) := by
          rw [hq, ht]
          field_simp
          ring
        rw [this, abs_neg, abs_of_nonneg (by
          apply div_nonneg <;> [apply mul_nonneg; positivity] <;> linarith)]
        rw [div_le_div_iff₀ (by positivity) hnpos]
        have hk0 : (0 : ℝ) ≤ k := by positivity
        nlinarith [mul_nonneg hk0 hnpos.le]
      rw [hrat]
      have hprod : A * q ≤ 1 := calc
        A * q ≤ 1 * q := mul_le_mul_of_nonneg_right h3 hq0
        _ ≤ 1 := by simpa using hq1
      refine ⟨?_, mul_nonneg h2 hq0, hprod⟩
      have htk0 : 0 ≤ t ^ k := pow_nonneg ht0 k
      have htk1 : t ^ k ≤ 1 := pow_le_one₀ ht0 ht1
      calc
        |A * q - t ^ (k + 1)| = |(A - t ^ k) * q + t ^ k * (q - t)| := by ring_nf
        _ ≤ |(A - t ^ k) * q| + |t ^ k * (q - t)| := abs_add_le _ _
        _ = |A - t ^ k| * q + t ^ k * |q - t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg htk0]
        _ ≤ (k : ℝ) ^ 2 / n * 1 + 1 * (k / n) := by gcongr
        _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 / n := by
          rw [mul_one, one_mul, ← add_div]
          apply div_le_div_of_nonneg_right _ hnpos.le
          push_cast
          nlinarith

private lemma power_identity (n k : ℕ) (x : ℝ) (hk : k ≤ n) :
    ∑ i ∈ range (n + 1), (i.choose k : ℝ) / (n.choose k) *
      ((n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)) = x ^ k := by
  have hnk : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h : n + 1 = k + (n - k + 1) := by lia
  rw [h, sum_range_add]
  have h0 : ∑ i ∈ range k, (i.choose k : ℝ) / (n.choose k) *
      ((n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt hi]
    simp
  rw [h0, zero_add]
  have hx : x ^ k = x ^ k * (x + (1 - x)) ^ (n - k) := by simp
  rw [hx, add_pow, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hc : ((k + j).choose k : ℝ) * (n.choose (k + j)) =
      n.choose k * ((n - k).choose j) := by
    have hc' := Nat.choose_mul (n := n) (k := k + j) (s := k) (by lia)
    rw [show k + j - k = j by lia] at hc'
    rw [mul_comm]
    exact_mod_cast hc'
  have hexp : n - (k + j) = n - k - j := by lia
  rw [hexp, pow_add]
  field_simp
  linear_combination (x ^ k * x ^ j * (1 - x) ^ (n - k - j)) * hc

private lemma bernstein_eval_identity (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n)
    (x : ℝ) :
    p.eval x = ∑ i ∈ range (n + 1), p.bernsteinCoeff n i *
      ((n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)) := by
  have hext : ∀ i ∈ range (n + 1), p.bernsteinCoeff n i =
      ∑ k ∈ range (n + 1),
        p.coeff k * ((i.choose k : ℝ) / (n.choose k)) := by
    intro i hi
    apply sum_subset
    · intro k hk
      simp only [mem_range] at hk hi ⊢
      lia
    · intro k _ hk
      simp only [mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by lia)]
      simp
  rw [sum_congr rfl (fun i hi => by rw [hext i hi])]
  simp_rw [sum_mul]
  rw [sum_comm, eval_eq_sum_range' (by lia : p.natDegree < n + 1)]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [← power_identity n k x (by lia), mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- Strict positivity on `[0,1]` is equivalent to strict positivity of all coefficients in some
degree-elevated Bernstein expansion. -/
theorem pos_on_Icc_iff_exists_bernsteinCoeff_pos (p : ℝ[X]) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < p.eval x) ↔
      ∃ n : ℕ, p.natDegree ≤ n ∧ ∀ i ≤ n, 0 < p.bernsteinCoeff n i := by
  constructor
  · intro hp
    obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.2 zero_le_one) p.continuous.continuousOn
    have hm : 0 < p.eval x0 := hp x0 hx0
    set m := p.eval x0
    set d := p.natDegree
    set B := ∑ k ∈ range (d + 1), |p.coeff k| * (k : ℝ) ^ 2 with hBdef
    have hB : 0 ≤ B := sum_nonneg fun _ _ => by positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (B / m)
    refine ⟨d + 1 + N, by lia, ?_⟩
    intro i hi
    set n := d + 1 + N with hndef
    have hn : 0 < n := by lia
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hBn : B / n < m := by
      rw [div_lt_iff₀ hnpos]
      rw [div_lt_iff₀ hm] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast (by lia : N ≤ n)
      nlinarith
    have h1 : p.bernsteinCoeff n i =
        ∑ k ∈ range (n + 1),
          p.coeff k * ((i.choose k : ℝ) / (n.choose k : ℝ)) := by
      apply sum_subset
      · intro k hk
        simp only [mem_range] at hk ⊢
        lia
      · intro k _ hk
        simp only [mem_range] at hk
        rw [Nat.choose_eq_zero_of_lt (by lia)]
        simp
    have h2 : ∑ k ∈ range (d + 1),
        p.coeff k * ((i.choose k : ℝ) / (n.choose k : ℝ)) =
        ∑ k ∈ range (n + 1),
          p.coeff k * ((i.choose k : ℝ) / (n.choose k : ℝ)) := by
      apply sum_subset
      · intro k hk
        simp only [mem_range] at hk ⊢
        lia
      · intro k _ hk
        simp only [mem_range] at hk
        rw [coeff_eq_zero_of_natDegree_lt (by lia)]
        simp
    have ht : ((i : ℝ) / n) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hnpos]
      exact_mod_cast hi
    have hev : m ≤ p.eval ((i : ℝ) / n) := hmin ht
    rw [eval_eq_sum_range] at hev
    rw [h1, ← h2]
    have hdiff : |∑ k ∈ range (d + 1),
        p.coeff k * ((i.choose k : ℝ) / (n.choose k : ℝ)) -
        ∑ k ∈ range (d + 1), p.coeff k * ((i : ℝ) / n) ^ k| ≤ B / n := by
      rw [← sum_sub_distrib, hBdef, sum_div]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro k hk
      rw [mem_range] at hk
      rw [← mul_sub, abs_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (choose_ratio_bound n i k hn hi (by lia)).1 (abs_nonneg _)
    have := (abs_le.1 hdiff).1
    linarith
  · rintro ⟨n, hn, hpos⟩ x hx
    rw [bernstein_eval_identity p n hn x]
    have hb : ∀ i ∈ range (n + 1),
        0 ≤ (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) := by
      intro i _
      have : 0 ≤ 1 - x := by linarith [hx.2]
      have : 0 ≤ x := hx.1
      positivity
    have hsum : ∑ i ∈ range (n + 1),
        (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) = 1 := by
      have := power_identity n 0 x (Nat.zero_le _)
      simpa using this
    obtain ⟨j, hj, hjpos⟩ := exists_lt_of_sum_lt
      (s := range (n + 1)) (f := fun _ => (0 : ℝ))
      (g := fun i => (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i))
      (by simp [hsum])
    apply sum_pos'
    · intro i hi
      exact mul_nonneg (hpos i (by simpa [Nat.lt_succ_iff] using hi)).le (hb i hi)
    · exact ⟨j, hj, mul_pos (hpos j (by simpa [Nat.lt_succ_iff] using hj)) hjpos⟩

end Polynomial

namespace bernsteinPolynomial

private lemma choose_add_mul_descFactorial (N j m : ℕ) :
    N.choose (j + m) * (j + m).descFactorial j =
      N.descFactorial j * (N - j).choose m := by
  by_cases h : j + m ≤ N
  · rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    have hchoose := Nat.choose_mul (n := N) (k := j + m) (s := j) (by lia)
    rw [Nat.add_sub_cancel_left] at hchoose
    calc
      N.choose (j + m) * (j.factorial * (j + m).choose j) =
          j.factorial * (N.choose (j + m) * (j + m).choose j) := by ring
      _ = j.factorial * (N.choose j * (N - j).choose m) := by rw [hchoose]
      _ = _ := by ring
  · rw [Nat.choose_eq_zero_of_lt (by lia : N < j + m), zero_mul]
    rcases Nat.lt_or_ge N j with hNj | hNj
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hNj, zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (by lia : N - j < m), mul_zero]

private lemma sum_descFactorial_mul_bernstein {R : Type*} [CommRing R]
    (N j : ℕ) (hj : j ≤ N) (z : R) :
    ∑ k ∈ range (N + 1), (N.choose k : R) * (k.descFactorial j : R) * z ^ k *
      (1 - z) ^ (N - k) = (N.descFactorial j : R) * z ^ j := by
  have hN : N + 1 = j + (N - j + 1) := by lia
  rw [hN, sum_range_add]
  rw [sum_eq_zero (s := range j), zero_add]
  · have h1 : ∀ m ∈ range (N - j + 1),
        (N.choose (j + m) : R) * ((j + m).descFactorial j : R) * z ^ (j + m) *
          (1 - z) ^ (N - (j + m)) =
        (N.descFactorial j : R) * z ^ j *
          (z ^ m * (1 - z) ^ (N - j - m) * ((N - j).choose m : R)) := by
      intro m _
      have hcast := congrArg (fun n : ℕ => (n : R))
        (choose_add_mul_descFactorial N j m)
      push_cast at hcast
      rw [pow_add, Nat.sub_sub]
      linear_combination (z ^ j * z ^ m * (1 - z) ^ (N - (j + m))) * hcast
    rw [sum_congr rfl h1, ← mul_sum, ← add_pow]
    simp
  · intro k hk
    rw [mem_range] at hk
    rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hk]
    simp

/-- A falling-factorial sum written in the degree-`N` Bernstein basis. -/
theorem sum_descFactorial_mul_pow (c : ℕ → R) (N : ℕ) (z : R) [CommRing R] :
    ∑ j ∈ range (N + 1), c j * (N.descFactorial j : R) * z ^ j =
      ∑ k ∈ range (N + 1), (N.choose k : R) *
        (∑ j ∈ range (N + 1), c j * (k.descFactorial j : R)) * z ^ k *
          (1 - z) ^ (N - k) := by
  have h : ∀ k ∈ range (N + 1), (N.choose k : R) *
        (∑ j ∈ range (N + 1), c j * (k.descFactorial j : R)) * z ^ k *
          (1 - z) ^ (N - k) =
      ∑ j ∈ range (N + 1), c j *
        ((N.choose k : R) * (k.descFactorial j : R) * z ^ k *
          (1 - z) ^ (N - k)) := by
    intro k _
    rw [mul_sum, sum_mul, sum_mul]
    refine sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← mul_sum, sum_descFactorial_mul_bernstein N j
    (Nat.lt_succ_iff.mp (mem_range.mp hj)) z]
  ring

end bernsteinPolynomial
