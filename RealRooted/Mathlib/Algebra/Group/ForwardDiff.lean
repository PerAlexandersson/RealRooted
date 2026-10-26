/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Polynomial.Basic

/-!
# Forward differences

This file records the forward-difference convention for sequences indexed by
natural numbers which retains the initial value, and Newton's forward-difference test for the
nonnegativity of a real polynomial at every natural number,
`Polynomial.forall_nat_eval_nonneg_iff_fwdDiff_iter` (RealRooted issue #1955; the proof was found
by Aristotle (Harmonic)).
-/

@[expose] public section

namespace Function

/-- The forward difference with its initial value retained. This is the
causal difference convention for sequences indexed by `ℕ`. -/
def causalFwdDiff {R : Type*} [Sub R] (a : ℕ → R) : ℕ → R
  | 0 => a 0
  | n + 1 => a (n + 1) - a n

/-- Causal forward difference commutes with inserting a finite prefix of
zeroes. -/
theorem causalFwdDiff_prefix {R : Type*} [AddGroup R] (a : ℕ → R) (s : ℕ) :
    causalFwdDiff (fun n => if s ≤ n then a (n - s) else 0) =
      fun n => if s ≤ n then causalFwdDiff a (n - s) else 0 := by
  funext n
  cases n with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simp [causalFwdDiff]
      · have hsn : ¬ s ≤ 0 := by lia
        simp [causalFwdDiff, hsn]
  | succ n =>
      by_cases hsn : s ≤ n + 1
      · by_cases hsn0 : s ≤ n
        · have hshift : n + 1 - s = (n - s) + 1 := by lia
          simp [causalFwdDiff, hsn, hsn0, hshift]
        · have hzero_succ : n + 1 - s = 0 := by lia
          simp [causalFwdDiff, hsn, hsn0, hzero_succ]
      · have hsn0 : ¬ s ≤ n := by lia
        simp [causalFwdDiff, hsn, hsn0]

end Function

namespace Polynomial

open Finset

private lemma eval_iterate_comp_X_add_one_sub (q : ℝ[X]) (j : ℕ) :
    ((fun r : ℝ[X] => r.comp (X + 1) - r)^[j] q).eval = (fwdDiff (1 : ℝ))^[j] q.eval := by
  induction j generalizing q with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    funext x
    simp [fwdDiff]

private lemma exists_eval_pos_of_leadingCoeff_pos (p : ℝ[X]) (hp : 0 < p.leadingCoeff) :
    ∃ N : ℝ, ∀ x ≥ N, 0 < p.eval x := by
  by_cases hd : p.degree ≤ 0
  · refine ⟨0, fun x _ => ?_⟩
    rw [eq_C_of_degree_le_zero hd] at hp ⊢
    simpa using hp
  · push Not at hd
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      ((p.tendsto_atTop_of_leadingCoeff_nonneg hd hp.le).eventually_gt_atTop 0)
    exact ⟨N, hN⟩

private lemma leadingCoeff_iterate_comp_X_add_one_sub (q : ℝ[X]) (hq : q ≠ 0) (j : ℕ)
    (hj : j ≤ q.natDegree) :
    let p := (fun r : ℝ[X] => r.comp (X + 1) - r)^[j] q
    p.leadingCoeff * (p.natDegree.factorial : ℝ) =
      q.leadingCoeff * (q.natDegree.factorial : ℝ) := by
  intro p
  have hev : p.eval = (fwdDiff (1 : ℝ))^[j] q.eval := eval_iterate_comp_X_add_one_sub q j
  have hq' : (fwdDiff (1 : ℝ))^[q.natDegree] q.eval =
      q.leadingCoeff • (q.natDegree.factorial : ℝ → ℝ) :=
    q.fwdDiff_iter_degree_eq_factorial
  have hlq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq
  have key : ∀ m, (fwdDiff (1 : ℝ))^[m] p.eval = (fwdDiff (1 : ℝ))^[m + j] q.eval := by
    intro m; rw [hev, Function.iterate_add]; rfl
  have hp := p.fwdDiff_iter_degree_eq_factorial
  rcases lt_trichotomy p.natDegree (q.natDegree - j) with h | h | h
  · exfalso
    have h0 := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h
    rw [key, Nat.sub_add_cancel hj, hq'] at h0
    have := congr_fun h0 0
    simp [hlq, Nat.factorial_ne_zero] at this
  · have := congr_fun hp 0
    rw [key, h, Nat.sub_add_cancel hj, hq'] at this
    simp at this
    rw [h]; linarith
  · exfalso
    have h0 := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
      (show q.natDegree < p.natDegree + j by lia)
    rw [← key, hp] at h0
    have hp0 : p = 0 := by simpa [Nat.factorial_ne_zero] using congr_fun h0 0
    simp [hp0] at h

/-- Newton's forward-difference test: a real polynomial is nonnegative at every natural number
iff it is nonnegative below some `K` and its forward differences of order at most its degree are
nonnegative at `K`.  Sufficiency is `q (K + r) = ∑ j, r.choose j * Δ^j q K`
(`shift_eq_sum_fwdDiff_iter`); for necessity every `Δ^j q` has a positive leading coefficient. -/
theorem forall_nat_eval_nonneg_iff_fwdDiff_iter (q : ℝ[X]) :
    (∀ n : ℕ, 0 ≤ q.eval (n : ℝ)) ↔
      ∃ K : ℕ, (∀ n < K, 0 ≤ q.eval (n : ℝ)) ∧
        ∀ j ≤ q.natDegree, 0 ≤ (fwdDiff (1 : ℝ))^[j] q.eval (K : ℝ) := by
  simp_rw [← eval_iterate_comp_X_add_one_sub]
  constructor
  · intro H
    by_cases hq : q = 0
    · subst hq
      refine ⟨0, fun n hn => absurd hn (Nat.not_lt_zero _), fun j hj => ?_⟩
      obtain rfl : j = 0 := by simpa using hj
      simp
    have hlq : 0 < q.leadingCoeff := by
      rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.2 hq) with h | h
      · exfalso
        obtain ⟨N, hN⟩ := exists_eval_pos_of_leadingCoeff_pos (-q) (by simpa using h)
        have := hN (⌈N⌉₊ : ℕ) (Nat.le_ceil N)
        have := H ⌈N⌉₊
        simp at *; linarith
      · exact h
    have hj : ∀ j ≤ q.natDegree, ∃ N : ℕ, ∀ n ≥ N,
        0 ≤ ((fun r : ℝ[X] => r.comp (X + 1) - r)^[j] q).eval (n : ℝ) := by
      intro j hj
      have hc := leadingCoeff_iterate_comp_X_add_one_sub q hq j hj
      set p := (fun r : ℝ[X] => r.comp (X + 1) - r)^[j] q
      have hpos : 0 < p.leadingCoeff := by
        have h1 : (0 : ℝ) < q.leadingCoeff * (q.natDegree.factorial : ℝ) := by
          have := Nat.factorial_pos q.natDegree; positivity
        rw [← hc] at h1
        have := Nat.factorial_pos p.natDegree
        exact pos_of_mul_pos_left h1 (by positivity)
      obtain ⟨N, hN⟩ := exists_eval_pos_of_leadingCoeff_pos p hpos
      exact ⟨⌈N⌉₊, fun n hn => (hN n (Nat.ceil_le.1 hn)).le⟩
    choose! Nf hNf using hj
    refine ⟨∑ j ∈ range (q.natDegree + 1), Nf j, fun n _ => H n, fun j hj' => hNf j hj' _ ?_⟩
    exact Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj'))
  · rintro ⟨K, hK, hD⟩ n
    rcases lt_or_ge n K with h | h
    · exact hK n h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
    have := shift_eq_sum_fwdDiff_iter (1 : ℝ) q.eval r (K : ℝ)
    simp only [nsmul_eq_mul, mul_one] at this
    push_cast
    rw [this]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) ?_
    rcases le_or_gt k q.natDegree with hk | hk
    · exact (congr_fun (eval_iterate_comp_X_add_one_sub q k) (K : ℝ)) ▸ hD k hk
    · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hk]; simp

end Polynomial
