/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Restricted-exponential recurrence

This file proves positivity and log-concavity for the restricted-exponential recurrence from
RealRooted issue #1982. The proof was found by Aristotle (Harmonic).
-/

public section

open Finset

namespace RealRooted

/-- A symmetrization inequality for two sequences satisfying the inner-versus-outer
log-concavity inequalities. -/
private lemma restrictedExp_core (e t : ℕ → ℝ) (N : ℕ)
    (he : ∀ i j, i ≤ j → e i * e (j + 1) ≤ e (i + 1) * e j)
    (ht : ∀ i j, i ≤ j → t i * t (j + 1) ≤ t (i + 1) * t j) :
    0 ≤ (∑ i ∈ range N, e (i + 1) * t (i + 1)) *
        (∑ i ∈ range N, e i * t i) -
      (∑ i ∈ range N, e (i + 1) * t i) *
        (∑ i ∈ range N, e i * t (i + 1)) := by
  have key : ∀ i j, 0 ≤
      (e i * e (j + 1) - e (i + 1) * e j) *
        (t i * t (j + 1) - t j * t (i + 1)) := by
    intro i j
    rcases le_total i j with h | h
    · have h1 := he i j h
      have h2 := ht i j h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h1 := he j i h
      have h2 := ht j i h
      exact mul_nonneg (by linarith) (by linarith)
  have hexp :
      (∑ i ∈ range N, e (i + 1) * t (i + 1)) * (∑ i ∈ range N, e i * t i) -
          (∑ i ∈ range N, e (i + 1) * t i) *
            (∑ i ∈ range N, e i * t (i + 1)) =
        ∑ i ∈ range N, ∑ j ∈ range N,
          (e (i + 1) * t (i + 1) * (e j * t j) -
            e (i + 1) * t i * (e j * t (j + 1))) := by
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
  rw [hexp]
  have hsym :
      (∑ i ∈ range N, ∑ j ∈ range N,
          (e (i + 1) * t (i + 1) * (e j * t j) -
            e (i + 1) * t i * (e j * t (j + 1)))) =
        ∑ i ∈ range N, ∑ j ∈ range N,
          (e (j + 1) * t (j + 1) * (e i * t i) -
            e (j + 1) * t j * (e i * t (i + 1))) :=
    sum_comm
  have hpos : 0 ≤ ∑ i ∈ range N, ∑ j ∈ range N,
      ((e (i + 1) * t (i + 1) * (e j * t j) -
          e (i + 1) * t i * (e j * t (j + 1))) +
        (e (j + 1) * t (j + 1) * (e i * t i) -
          e (j + 1) * t j * (e i * t (i + 1)))) := by
    refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
    have := key i j
    linarith
  rw [show
      (∑ i ∈ range N, ∑ j ∈ range N,
        ((e (i + 1) * t (i + 1) * (e j * t j) -
            e (i + 1) * t i * (e j * t (j + 1))) +
          (e (j + 1) * t (j + 1) * (e i * t i) -
            e (j + 1) * t j * (e i * t (i + 1))))) =
        (∑ i ∈ range N, ∑ j ∈ range N,
          (e (i + 1) * t (i + 1) * (e j * t j) -
            e (i + 1) * t i * (e j * t (j + 1)))) +
        ∑ i ∈ range N, ∑ j ∈ range N,
          (e (j + 1) * t (j + 1) * (e i * t i) -
            e (j + 1) * t j * (e i * t (i + 1))) by
      simp only [sum_add_distrib]] at hpos
  linarith

/-- Earlier log-concavity inequalities for a positive sequence imply all inner-versus-outer
inequalities in the same range. -/
private lemma restrictedExp_lc_gen (a : ℕ → ℝ) (n : ℕ) (hpos : ∀ k, 0 < a k)
    (hlc : ∀ k, k + 2 ≤ n → a k * a (k + 2) ≤ a (k + 1) ^ 2) :
    ∀ u v, u ≤ v → v + 1 ≤ n → a u * a (v + 1) ≤ a (u + 1) * a v := by
  intro u v huv
  induction v, huv using Nat.le_induction with
  | base =>
      intro _
      exact le_of_eq (by ring)
  | succ v hv ih =>
      intro hv2
      have h1 := ih (by lia)
      have h2 := hlc v (by lia)
      have h3 : a u * a (v + 1 + 1) * a (v + 1) ≤
          a (u + 1) * a (v + 1) * a (v + 1) := by
        nlinarith [mul_le_mul_of_nonneg_right h1 (hpos (v + 2)).le,
          mul_le_mul_of_nonneg_left h2 (hpos (u + 1)).le]
      exact le_of_mul_le_mul_right h3 (hpos _)

/-- Positivity and log-concavity for a convolution recurrence with a nonnegative,
nonincreasing, log-concave kernel whose initial term is one. -/
private lemma restrictedExp_general (r a : ℕ → ℝ) (hr0 : r 0 = 1)
    (hrnn : ∀ l, 0 ≤ r l) (hranti : ∀ l, r (l + 1) ≤ r l)
    (hrlc : ∀ i j, i ≤ j → r i * r (j + 1) ≤ r (i + 1) * r j)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 1) * a (n + 1) =
      ∑ l ∈ range (n + 1), r l * a (n - l)) :
    (∀ n, 0 < a n) ∧ ∀ n, a n * a (n + 2) ≤ a (n + 1) ^ 2 := by
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero =>
          rw [ha0]
          norm_num
      | succ m =>
          have h := hrec m
          rw [sum_range_succ'] at h
          have h1 : 0 ≤ ∑ i ∈ range m, r (i + 1) * a (m - (i + 1)) :=
            sum_nonneg fun i _ => mul_nonneg (hrnn _) (ih _ (by lia)).le
          have h2 : 0 < r 0 * a (m - 0) := by
            rw [hr0, Nat.sub_zero, one_mul]
            exact ih m (by lia)
          have h3 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          by_contra hc
          push Not at hc
          nlinarith
  have hDgen : ∀ n : ℕ, ∑ i ∈ range n, r i * a (n - (i + 1)) = (n : ℝ) * a n := by
    intro n
    cases n with
    | zero => simp
    | succ m =>
        push_cast
        rw [hrec m]
  refine ⟨hpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    set t : ℕ → ℝ := fun i => if i ≤ n then a (n - i) else 0 with ht_def
    have tnn : ∀ i, 0 ≤ t i := by
      intro i
      simp only [ht_def]
      split_ifs
      · exact (hpos _).le
      · exact le_rfl
    have tin : ∀ i, i ≤ n → t i = a (n - i) := by
      intro i hi
      simp [ht_def, hi]
    have tout : t (n + 1) = 0 := by
      simp [ht_def]
    have hlc : ∀ k, k + 2 ≤ n → a k * a (k + 2) ≤ a (k + 1) ^ 2 :=
      fun k hk => ih k (by lia)
    have hgen := restrictedExp_lc_gen a n hpos hlc
    have htlc : ∀ i j, i ≤ j → t i * t (j + 1) ≤ t (i + 1) * t j := by
      intro i j hij
      by_cases hj : j + 1 ≤ n
      · rw [tin i (by lia), tin (j + 1) hj, tin (i + 1) (by lia), tin j (by lia)]
        have hinner := hgen (n - (j + 1)) (n - (i + 1)) (by lia) (by lia)
        rw [show n - (i + 1) + 1 = n - i by lia,
          show n - (j + 1) + 1 = n - j by lia] at hinner
        linarith
      · rw [show t (j + 1) = 0 by
          simp [ht_def, hj], mul_zero]
        exact mul_nonneg (tnn _) (tnn _)
    have hcore := restrictedExp_core r t (n + 1) hrlc htlc
    have hB : ∑ i ∈ range (n + 1), r i * t i = ((n : ℝ) + 1) * a (n + 1) := by
      rw [hrec n]
      refine sum_congr rfl fun i hi => ?_
      rw [tin i (by simp at hi; lia)]
    have hC : ∑ i ∈ range (n + 1), r (i + 1) * t i =
        ((n : ℝ) + 2) * a (n + 2) - a (n + 1) := by
      have h := hrec (n + 1)
      rw [sum_range_succ', hr0, Nat.sub_zero] at h
      simp only [Nat.add_sub_add_right] at h
      have h' : ∑ i ∈ range (n + 1), r (i + 1) * t i =
          ∑ i ∈ range (n + 1), r (i + 1) * a (n - i) := by
        refine sum_congr rfl fun i hi => ?_
        rw [tin i (by simp at hi; lia)]
      rw [h']
      have e : a (n + 1 + 1) = a (n + 2) := rfl
      rw [e] at h
      push_cast at h
      linarith
    have hD : ∑ i ∈ range (n + 1), r i * t (i + 1) = (n : ℝ) * a n := by
      rw [sum_range_succ, tout, mul_zero, add_zero, ← hDgen n]
      refine sum_congr rfl fun i hi => ?_
      rw [tin (i + 1) (by simp at hi; lia)]
    have hA : ∑ i ∈ range (n + 1), r (i + 1) * t (i + 1) =
        ((n : ℝ) + 1) * a (n + 1) - a n := by
      have h := hrec n
      rw [sum_range_succ', hr0, Nat.sub_zero] at h
      rw [sum_range_succ, tout, mul_zero, add_zero]
      have h' : ∑ i ∈ range n, r (i + 1) * t (i + 1) =
          ∑ i ∈ range n, r (i + 1) * a (n - (i + 1)) := by
        refine sum_congr rfl fun i hi => ?_
        rw [tin (i + 1) (by simp at hi; lia)]
      rw [h']
      linarith
    have hmono : a (n + 2) ≤ a (n + 1) := by
      have h0 : 0 ≤ ∑ i ∈ range (n + 1), (r i - r (i + 1)) * t i :=
        sum_nonneg fun i _ => mul_nonneg (by linarith [hranti i]) (tnn i)
      have hsplit : ∑ i ∈ range (n + 1), (r i - r (i + 1)) * t i =
          ∑ i ∈ range (n + 1), r i * t i -
            ∑ i ∈ range (n + 1), r (i + 1) * t i := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun i _ => by ring
      rw [hsplit, hB, hC] at h0
      have h2 : 0 ≤ ((n : ℝ) + 2) * (a (n + 1) - a (n + 2)) := by linarith
      have hnonneg :=
        (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mp h2
      linarith
    rw [hA, hB, hC, hD] at hcore
    have h2 := mul_nonneg (hpos n).le (sub_nonneg.mpr hmono)
    have key : 0 ≤ ((n : ℝ) + 1) ^ 2 *
        (a (n + 1) ^ 2 - a n * a (n + 2)) := by
      nlinarith [hcore, h2]
    have hnonneg :=
      (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)).mp key
    linarith

/-- A sequence satisfying the restricted-exponential recurrence with cutoff `d > 0` is positive
and log-concave. -/
theorem restrictedExp_pos_logConcave (d : ℕ) (hd : d ≠ 0) (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 1) * a (n + 1) =
      ∑ l ∈ range (n + 1),
        (if l < d then 1 / (l.factorial : ℝ) else 0) * a (n - l)) :
    (∀ n, 0 < a n) ∧ ∀ n, a n * a (n + 2) ≤ a (n + 1) ^ 2 := by
  refine restrictedExp_general (fun l => if l < d then 1 / (l.factorial : ℝ) else 0) a
    ?_ ?_ ?_ ?_ ha0 hrec
  · simp [Nat.pos_of_ne_zero hd]
  · intro l
    split_ifs <;> positivity
  · intro l
    split_ifs with h1 h2
    · rw [Nat.factorial_succ]
      push_cast
      have hf : (0 : ℝ) < (l.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos l
      rw [div_le_div_iff₀ (by positivity) hf]
      nlinarith
    · lia
    · positivity
    · exact le_rfl
  · intro i j hij
    by_cases hj : j + 1 < d
    · rw [ite_eq_left (by lia), ite_eq_left hj, ite_eq_left (by lia),
        ite_eq_left (by lia)]
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have hfi : (0 : ℝ) < (i.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos i
      have hfj : (0 : ℝ) < (j.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos j
      rw [div_mul_div_comm, div_mul_div_comm,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      nlinarith [mul_pos hfi hfj]
    · rw [ite_eq_right hj, mul_zero]
      apply mul_nonneg <;> split_ifs <;> positivity

end RealRooted
