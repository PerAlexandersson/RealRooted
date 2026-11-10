/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.ChebyshevExpansion
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# The inverse Bernstein inequality

This file develops the critical-point structure used in the inverse Bernstein inequality for
real polynomials with simple roots in `(-1, 1)`.
-/

public section

noncomputable section

open Set

namespace Polynomial

/-- If `p` has degree `n > 0`, then `n - 1` distinct zeros of `p'` exhaust all zeros of `p'`. -/
theorem eq_of_derivative_eval_eq_zero {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (hdeg : p.natDegree = n)
    {c : Fin (n - 1) → ℝ} (hc : StrictMono c) (hc0 : ∀ j, p.derivative.eval (c j) = 0)
    {z : ℝ} (hz : p.derivative.eval z = 0) : ∃ j, z = c j := by
  by_contra hzc
  push Not at hzc
  have hd : p.derivative ≠ 0 := by
    intro h
    have := derivative_eq_zero.mp h
    lia
  let S : Finset ℝ := insert z (Finset.univ.image c)
  have hzS : z ∉ Finset.univ.image c := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun j h ↦ hzc j h.symm
  have hcard : S.card = n := by
    rw [Finset.card_insert_of_notMem hzS, Finset.card_image_of_injective _ hc.injective,
      Finset.card_univ, Fintype.card_fin]
    lia
  have hsub : S ⊆ p.derivative.roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, mem_roots hd, IsRoot.def]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hz
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
      exact hc0 j
  have h1 := Finset.card_le_card hsub
  have h2 := Multiset.toFinset_card_le p.derivative.roots
  have h3 := card_roots' p.derivative
  have h4 := natDegree_derivative_le p
  lia

/-- Root and critical-point structure of a degree-`n` polynomial with `n` simple roots in
`(-1, 1)`: roots `r 0 < ⋯ < r (n - 1)` in `(-1, 1)`, zeros `c j ∈ (r j, r (j + 1))` of `p'`, and
these `c j` are all the zeros of `p'`. -/
theorem exists_roots_critical_points {p : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hdeg : p.natDegree = n)
    (hroots : (p.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = n)
    (hsimple : p.roots.Nodup) :
    ∃ r c : ℕ → ℝ, (∀ i < n, r i ∈ Ioo (-1 : ℝ) 1 ∧ p.IsRoot (r i)) ∧
      (∀ j, j + 1 < n → r j < c j ∧ c j < r (j + 1) ∧ p.derivative.eval (c j) = 0) ∧
      (∀ z, p.derivative.eval z = 0 → ∃ j, j + 1 < n ∧ z = c j) := by
  have hp_ne : p ≠ 0 := by
    intro hp
    rw [hp, natDegree_zero] at hdeg
    lia
  have hcard : p.roots.card = n := by
    have hfilter_le := Multiset.card_le_card
      (Multiset.filter_le (· ∈ Ioo (-1 : ℝ) 1) p.roots)
    have hroots_le := card_roots' p
    lia
  have hfilter_eq : p.roots.filter (· ∈ Ioo (-1 : ℝ) 1) = p.roots := by
    refine Multiset.eq_of_le_of_card_le
      (s := p.roots.filter (· ∈ Ioo (-1 : ℝ) 1)) (t := p.roots)
      (Multiset.filter_le _ _) ?_
    exact hcard.le.trans_eq hroots.symm
  have hall (x : ℝ) (hx : x ∈ p.roots) : x ∈ Ioo (-1 : ℝ) 1 := by
    have hx' : x ∈ p.roots.filter (· ∈ Ioo (-1 : ℝ) 1) := by
      rwa [hfilter_eq]
    exact (Multiset.mem_filter.mp hx').2
  have hcard_finset : p.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hsimple, hcard]
  let r : Fin n → ℝ := p.roots.toFinset.orderEmbOfFin hcard_finset
  have hr_mono : StrictMono r :=
    (p.roots.toFinset.orderEmbOfFin hcard_finset).strictMono
  have hr_mem (j : Fin n) : r j ∈ p.roots := by
    exact Multiset.mem_toFinset.mp
      (Finset.orderEmbOfFin_mem p.roots.toFinset hcard_finset j)
  have hr_root (j : Fin n) : p.IsRoot (r j) := isRoot_of_mem_roots (hr_mem j)
  let lo : Fin (n - 1) → Fin n := fun j ↦
    ⟨j.val, j.isLt.trans_le (Nat.sub_le n 1)⟩
  let hi : Fin (n - 1) → Fin n := fun j ↦ ⟨j.val + 1, by lia⟩
  have hgap (j : Fin (n - 1)) :
      ∃ z ∈ Ioo (r (lo j)) (r (hi j)), p.derivative.eval z = 0 := by
    have hlohi : lo j < hi j := by simp [lo, hi]
    have hlt : r (lo j) < r (hi j) := hr_mono hlohi
    exact exists_hasDerivAt_eq_zero hlt p.continuousOn
      ((hr_root (lo j)).eq_zero.trans (hr_root (hi j)).eq_zero.symm)
      (fun x _ ↦ p.hasDerivAt x)
  let c : Fin (n - 1) → ℝ := fun j ↦ (hgap j).choose
  have hc_gap (j : Fin (n - 1)) : c j ∈ Ioo (r (lo j)) (r (hi j)) :=
    (hgap j).choose_spec.1
  have hc_zero (j : Fin (n - 1)) : p.derivative.eval (c j) = 0 :=
    (hgap j).choose_spec.2
  have hc_mono : StrictMono c := by
    intro i j hij
    have hle : hi i ≤ lo j := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij
    exact (hc_gap i).2.trans_le (hr_mono.monotone hle) |>.trans (hc_gap j).1
  refine ⟨fun k ↦ if h : k < n then r ⟨k, h⟩ else 0,
    fun j ↦ if h : j < n - 1 then c ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
  · intro i hi
    simp only [hi, ↓reduceDIte]
    exact ⟨hall _ (hr_mem _), hr_root _⟩
  · intro j hj
    have hj' : j < n - 1 := by lia
    simp only [hj', show j < n by lia, hj, ↓reduceDIte]
    exact ⟨(hc_gap ⟨j, hj'⟩).1, (hc_gap ⟨j, hj'⟩).2, hc_zero _⟩
  · intro z hz
    obtain ⟨j, rfl⟩ := eq_of_derivative_eval_eq_zero hn hdeg hc_mono hc_zero hz
    refine ⟨j.val, by have := j.isLt; lia, ?_⟩
    simp only [j.isLt, ↓reduceDIte]

/-- The inverse Bernstein inequality is immediate at a point where the polynomial has absolute
value at least one. -/
theorem sq_mul_one_sub_sq_le_of_one_le_abs_eval {p : ℝ[X]} {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hpx : 1 ≤ |p.eval x|) :
    (n : ℝ) ^ 2 * (1 - p.eval x ^ 2) ≤
      (1 - x ^ 2) * p.derivative.eval x ^ 2 := by
  have hx_sq : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
  have hp_sq : 1 ≤ p.eval x ^ 2 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|p.eval x| - 1)]
  have hleft : (n : ℝ) ^ 2 * (1 - p.eval x ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hp_sq)
  have hright : 0 ≤ (1 - x ^ 2) * p.derivative.eval x ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hx_sq) (sq_nonneg _)
  exact hleft.trans hright

/-- On an open interval where `p'` has no zero, `p'` has constant sign. -/
theorem derivative_pos_or_neg_of_ne_zero {p : ℝ[X]} {u v : ℝ}
    (hne : ∀ x ∈ Ioo u v, p.derivative.eval x ≠ 0) :
    (∀ x ∈ Ioo u v, 0 < p.derivative.eval x) ∨ (∀ x ∈ Ioo u v, p.derivative.eval x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩ := h
  have hpa' : p.derivative.eval a < 0 := lt_of_le_of_ne hpa (hne a ha)
  have hpb' : 0 < p.derivative.eval b := lt_of_le_of_ne hpb (hne b hb).symm
  obtain ⟨z, hz, hz0⟩ := isPreconnected_Ioo.intermediate_value ha hb
    p.derivative.continuous.continuousOn ⟨hpa'.le, hpb'.le⟩
  exact hne z hz hz0

/-- If `p'` has no zero in `(u, v)`, then `p` is strictly monotone or strictly antitone on
`[u, v]`. -/
theorem strictMonoOn_or_strictAntiOn_of_derivative_ne_zero {p : ℝ[X]} {u v : ℝ}
    (hne : ∀ x ∈ Ioo u v, p.derivative.eval x ≠ 0) :
    StrictMonoOn (fun x ↦ p.eval x) (Icc u v) ∨
      StrictAntiOn (fun x ↦ p.eval x) (Icc u v) := by
  rcases derivative_pos_or_neg_of_ne_zero hne with h | h
  · left
    refine strictMonoOn_of_deriv_pos (convex_Icc u v) p.continuous.continuousOn fun x hx ↦ ?_
    rw [interior_Icc] at hx
    simpa [Polynomial.deriv] using h x hx
  · right
    refine strictAntiOn_of_deriv_neg (convex_Icc u v) p.continuous.continuousOn fun x hx ↦ ?_
    rw [interior_Icc] at hx
    simpa [Polynomial.deriv] using h x hx

/-- Sign alternation points: `-1 = C 0 < C 1 < ⋯ < C n = 1`, where the interior points are the
critical points of `p`, consecutive values of `p` have opposite signs, and no zero of `p'` lies
strictly between consecutive points. -/
theorem exists_sign_alternation_points {p : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hdeg : p.natDegree = n)
    (hroots : (p.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = n)
    (hsimple : p.roots.Nodup) :
    ∃ C : ℕ → ℝ, C 0 = -1 ∧ C n = 1 ∧ (∀ k < n, C k < C (k + 1)) ∧
      (∀ k, 0 < k → k < n → C k ∈ Ioo (-1 : ℝ) 1 ∧ p.derivative.eval (C k) = 0) ∧
      (∀ k < n, p.eval (C k) * p.eval (C (k + 1)) < 0) ∧
      (∀ k < n, ∀ x ∈ Ioo (C k) (C (k + 1)), p.derivative.eval x ≠ 0) := by
  obtain ⟨r, c, hr, hrc, hcz⟩ := exists_roots_critical_points hn hdeg hroots hsimple
  let C : ℕ → ℝ := fun k ↦ if k = 0 then -1 else if k < n then c (k - 1) else 1
  have hC0 : C 0 = -1 := by simp [C]
  have hCn : C n = 1 := by simp [C, hn.ne']
  have hCmid : ∀ k, 0 < k → k < n → C k = c (k - 1) := by
    intro k hk hkn
    simp [C, hk.ne', hkn]
  have hC_lt_r : ∀ k < n, C k < r k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hC0]; exact (hr 0 hk).1.1
    · rw [hCmid k hk0 hk]
      have := (hrc (k - 1) (by lia)).2.1
      rwa [show k - 1 + 1 = k by lia] at this
  have hr_lt_C : ∀ k < n, r k < C (k + 1) := by
    intro k hk
    by_cases hk1 : k + 1 < n
    · rw [hCmid (k + 1) (by lia) hk1, show k + 1 - 1 = k by lia]
      exact (hrc k hk1).1
    · rw [show k + 1 = n by lia, hCn]; exact (hr k hk).1.2
  have hstep : ∀ k < n, C k < C (k + 1) := fun k hk ↦ (hC_lt_r k hk).trans (hr_lt_C k hk)
  have hmono : ∀ a b, a ≤ b → b ≤ n → C a ≤ C b := by
    intro a b hab hbn
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hstep b (by lia)).le
  have hmid : ∀ k, 0 < k → k < n → C k ∈ Ioo (-1 : ℝ) 1 ∧ p.derivative.eval (C k) = 0 := by
    intro k hk0 hkn
    rw [hCmid k hk0 hkn]
    have hj := hrc (k - 1) (by lia)
    rw [show k - 1 + 1 = k by lia] at hj
    exact ⟨⟨(hr (k - 1) (by lia)).1.1.trans hj.1, hj.2.1.trans (hr k hkn).1.2⟩, hj.2.2⟩
  have hnoz : ∀ k < n, ∀ x ∈ Ioo (C k) (C (k + 1)), p.derivative.eval x ≠ 0 := by
    intro k hk x hx hx0
    obtain ⟨j, hj, rfl⟩ := hcz x hx0
    rw [← show C (j + 1) = c j by rw [hCmid (j + 1) (by lia) hj]; rfl] at hx
    rcases Nat.lt_or_ge (j + 1) (k + 1) with h | h
    · exact (hx.1.trans_le' (hmono _ _ (by lia) (by lia))).false
    · exact (hx.2.trans_le (hmono _ _ h (by lia))).false
  refine ⟨C, hC0, hCn, hstep, hmid, fun k hk ↦ ?_, hnoz⟩
  have hroot : p.eval (r k) = 0 := (hr k hk).2
  have hlo := hC_lt_r k hk
  have hhi := hr_lt_C k hk
  have hmem : ∀ x ∈ ({C k, r k, C (k + 1)} : Set ℝ), x ∈ Icc (C k) (C (k + 1)) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨le_rfl, (hstep k hk).le⟩
    · exact ⟨hlo.le, hhi.le⟩
    · exact ⟨(hstep k hk).le, le_rfl⟩
  rcases strictMonoOn_or_strictAntiOn_of_derivative_ne_zero (hnoz k hk) with h | h
  · have h1 := h (hmem _ (by simp)) (hmem _ (by simp)) hlo
    have h2 := h (hmem _ (by simp)) (hmem _ (by simp)) hhi
    simp only [hroot] at h1 h2
    nlinarith
  · have h1 := h (hmem _ (by simp)) (hmem _ (by simp)) hlo
    have h2 := h (hmem _ (by simp)) (hmem _ (by simp)) hhi
    simp only [hroot] at h1 h2
    nlinarith


/-- Alternation points: `-1 = C 0 < C 1 < ⋯ < C n = 1` with `|p (C k)| ≥ 1`, consecutive values of
opposite sign, and no zero of `p'` strictly between consecutive points. -/
theorem exists_alternation_points {p : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hdeg : p.natDegree = n)
    (hroots : (p.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = n)
    (hsimple : p.roots.Nodup)
    (hone : p.eval 1 = 1) (hmone : p.eval (-1) = (-1) ^ n)
    (hcrit : ∀ c ∈ Ioo (-1 : ℝ) 1, p.derivative.eval c = 0 → 1 ≤ |p.eval c|) :
    ∃ C : ℕ → ℝ, C 0 = -1 ∧ C n = 1 ∧ (∀ k < n, C k < C (k + 1)) ∧
      (∀ k ≤ n, 1 ≤ |p.eval (C k)|) ∧ (∀ k < n, p.eval (C k) * p.eval (C (k + 1)) < 0) ∧
      (∀ k < n, ∀ x ∈ Ioo (C k) (C (k + 1)), p.derivative.eval x ≠ 0) := by
  obtain ⟨C, hC0, hCn, hstep, hmid, hprod, hnoz⟩ :=
    exists_sign_alternation_points hn hdeg hroots hsimple
  refine ⟨C, hC0, hCn, hstep, fun k hk ↦ ?_, hprod, hnoz⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hC0, hmone, abs_pow, abs_neg, abs_one, one_pow]
  by_cases hkn : k < n
  · exact hcrit _ (hmid k hk0 hkn).1 (hmid k hk0 hkn).2
  · rw [show k = n by lia, hCn, hone, abs_one]
/-- A negative derivative at `x` gives a larger value somewhere in any interval `(a, x)`. -/
theorem _root_.HasDerivAt.exists_Ioo_lt_of_neg {f : ℝ → ℝ} {f' x a : ℝ} (hf : HasDerivAt f f' x)
    (hf' : f' < 0) (ha : a < x) : ∃ y ∈ Ioo a x, f x < f y := by
  have h := hf.hasDerivWithinAt.limsup_slope_le' (s := Iio x) (by simp) hf'
  obtain ⟨y, hy, hya⟩ := (h.and (Ioo_mem_nhdsLT ha)).exists
  refine ⟨y, hya, ?_⟩
  rw [slope_def_field, div_neg_iff] at hy
  rcases hy with ⟨h1, -⟩ | ⟨-, hyx⟩
  · linarith
  · linarith [hya.2]

/-- A negative derivative at `x` gives a smaller value somewhere in any interval `(x, b)`. -/
theorem _root_.HasDerivAt.exists_Ioo_gt_of_neg {f : ℝ → ℝ} {f' x b : ℝ} (hf : HasDerivAt f f' x)
    (hf' : f' < 0) (hb : x < b) : ∃ y ∈ Ioo x b, f y < f x := by
  have h := hf.hasDerivWithinAt.limsup_slope_le' (s := Ioi x) (by simp) hf'
  obtain ⟨y, hy, hyb⟩ := (h.and (Ioo_mem_nhdsGT hb)).exists
  refine ⟨y, hyb, ?_⟩
  rw [slope_def_field, div_neg_iff] at hy
  rcases hy with ⟨-, hyx⟩ | ⟨h1, -⟩
  · linarith [hyb.1]
  · linarith

/-- A continuous function with values of opposite signs at `a < b` vanishes in `(a, b)`. -/
theorem _root_.exists_Ioo_eq_zero_of_mul_neg {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : a < b) (hsign : f a * f b < 0) : ∃ y ∈ Ioo a b, f y = 0 := by
  rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' hab.le hf.continuousOn ⟨hb, ha⟩
    exact ⟨y, hy, hy0⟩
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo hab.le hf.continuousOn ⟨ha, hb⟩
    exact ⟨y, hy, hy0⟩

/-- The value at the unique critical point between two roots dominates every value between
the roots in absolute value. -/
private theorem abs_eval_le_abs_eval_critical_of_unique {p : ℝ[X]} {a b c x : ℝ}
    (ha : p.eval a = 0) (hb : p.eval b = 0) (hc : c ∈ Ioo a b) (hx : x ∈ Icc a b)
    (hunique : ∀ y ∈ Ioo a b, p.derivative.eval y = 0 → y = c) :
    |p.eval x| ≤ |p.eval c| := by
  rcases lt_trichotomy x c with hxc | rfl | hcx
  · by_cases hxa : x = a
    · simp [hxa, ha]
    have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
    have hne : ∀ y ∈ Ioo a c, p.derivative.eval y ≠ 0 := by
      intro y hy hy0
      exact hy.2.ne (hunique y ⟨hy.1, hy.2.trans hc.2⟩ hy0)
    have ha_mem : a ∈ Icc a c := ⟨le_rfl, hc.1.le⟩
    have hx_mem : x ∈ Icc a c := ⟨hax.le, hxc.le⟩
    have hc_mem : c ∈ Icc a c := ⟨hc.1.le, le_rfl⟩
    rcases strictMonoOn_or_strictAntiOn_of_derivative_ne_zero hne with hmono | hanti
    · have hpx : 0 < p.eval x := by simpa [ha] using hmono ha_mem hx_mem hax
      have hpc : p.eval x < p.eval c := hmono hx_mem hc_mem hxc
      rw [abs_of_pos hpx, abs_of_pos (hpx.trans hpc)]
      exact hpc.le
    · have hpx : p.eval x < 0 := by simpa [ha] using hanti ha_mem hx_mem hax
      have hpc : p.eval c < p.eval x := hanti hx_mem hc_mem hxc
      rw [abs_of_neg hpx, abs_of_neg (hpc.trans hpx)]
      linarith
  · exact le_rfl
  · by_cases hxb : x = b
    · simp [hxb, hb]
    have hxb' : x < b := lt_of_le_of_ne hx.2 hxb
    have hne : ∀ y ∈ Ioo c b, p.derivative.eval y ≠ 0 := by
      intro y hy hy0
      exact hy.1.ne' (hunique y ⟨hc.1.trans hy.1, hy.2⟩ hy0)
    have hc_mem : c ∈ Icc c b := ⟨le_rfl, hc.2.le⟩
    have hx_mem : x ∈ Icc c b := ⟨hcx.le, hxb'.le⟩
    have hb_mem : b ∈ Icc c b := ⟨hc.2.le, le_rfl⟩
    rcases strictMonoOn_or_strictAntiOn_of_derivative_ne_zero hne with hmono | hanti
    · have hpx : p.eval x < 0 := by simpa [hb] using hmono hx_mem hb_mem hxb'
      have hpc : p.eval c < p.eval x := hmono hc_mem hx_mem hcx
      rw [abs_of_neg hpx, abs_of_neg (hpc.trans hpx)]
      linarith
    · have hpx : 0 < p.eval x := by simpa [hb] using hanti hx_mem hb_mem hxb'
      have hpc : p.eval x < p.eval c := hanti hc_mem hx_mem hcx
      rw [abs_of_pos hpx, abs_of_pos (hpx.trans hpc)]
      exact hpc.le

/-- Alternating values of size at least one force every interior critical value to have size at
least one. -/
theorem one_le_abs_eval_critical_of_alternation {q : ℝ[X]} {N : ℕ} (hN : 0 < N)
    (hdeg : q.natDegree = N) (hroots : (q.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = N)
    (hsimple : q.roots.Nodup) {ξ : ℕ → ℝ} (hξ0 : ξ 0 = -1) (hξN : ξ N = 1)
    (hξinc : ∀ i < N, ξ i < ξ (i + 1)) (halt : ∀ i ≤ N, 1 ≤ |q.eval (ξ i)|)
    (hprod : ∀ i < N, q.eval (ξ i) * q.eval (ξ (i + 1)) < 0) :
    ∀ c ∈ Ioo (-1 : ℝ) 1, q.derivative.eval c = 0 → 1 ≤ |q.eval c| := by
  have hN_endpoints : 0 < N := by
    by_contra h
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos h
    have heq : ξ 0 = ξ N := by rw [hN0]
    rw [hξ0, hξN] at heq
    norm_num at heq
  have hξmono : ∀ a b, a ≤ b → b ≤ N → ξ a ≤ ξ b := by
    intro a b hab hbN
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hξinc b (by lia)).le
  have hex : ∀ i < N, ∃ y ∈ Ioo (ξ i) (ξ (i + 1)), q.eval y = 0 :=
    fun i hi ↦ exists_Ioo_eq_zero_of_mul_neg q.continuous (hξinc i hi) (hprod i hi)
  choose! z hz hz0 using hex
  let zF : Fin N → ℝ := fun i ↦ z i
  have hzF_gap (i : Fin N) : zF i ∈ Ioo (ξ i) (ξ (i + 1)) := by
    simpa only [zF] using hz i i.isLt
  have hzF_zero (i : Fin N) : q.eval (zF i) = 0 := by
    simpa only [zF] using hz0 i i.isLt
  have hzF_mono : StrictMono zF := by
    intro i j hij
    have hmid : ξ (i.val + 1) ≤ ξ j.val :=
      hξmono _ _ (Nat.succ_le_of_lt hij) j.isLt.le
    exact (hzF_gap i).2.trans_le hmid |>.trans (hzF_gap j).1
  let lo : Fin (N - 1) → Fin N := fun j ↦
    ⟨j.val, j.isLt.trans_le (Nat.sub_le N 1)⟩
  let hi : Fin (N - 1) → Fin N := fun j ↦ ⟨j.val + 1, by lia⟩
  have hgap (j : Fin (N - 1)) :
      ∃ c ∈ Ioo (zF (lo j)) (zF (hi j)), q.derivative.eval c = 0 := by
    have hlohi : lo j < hi j := by simp [lo, hi]
    have hlt : zF (lo j) < zF (hi j) := hzF_mono hlohi
    exact exists_hasDerivAt_eq_zero hlt q.continuousOn
      ((hzF_zero (lo j)).trans (hzF_zero (hi j)).symm)
      (fun x _ ↦ q.hasDerivAt x)
  let d : Fin (N - 1) → ℝ := fun j ↦ (hgap j).choose
  have hd_gap (j : Fin (N - 1)) : d j ∈ Ioo (zF (lo j)) (zF (hi j)) :=
    (hgap j).choose_spec.1
  have hd_zero (j : Fin (N - 1)) : q.derivative.eval (d j) = 0 :=
    (hgap j).choose_spec.2
  have hd_mono : StrictMono d := by
    intro i j hij
    have hle : hi i ≤ lo j := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij
    exact (hd_gap i).2.trans_le (hzF_mono.monotone hle) |>.trans (hd_gap j).1
  have hd_unique (j : Fin (N - 1)) :
      ∀ y ∈ Ioo (zF (lo j)) (zF (hi j)), q.derivative.eval y = 0 → y = d j := by
    intro y hy hy0
    obtain ⟨k, rfl⟩ := eq_of_derivative_eval_eq_zero hN hdeg hd_mono hd_zero hy0
    have hkj : k = j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hle : hi k ≤ lo j := by
          change k.val + 1 ≤ j.val
          exact Nat.succ_le_of_lt h
        exact ((hd_gap k).2.trans_le (hzF_mono.monotone hle)).asymm hy.1
      · have hle : hi j ≤ lo k := by
          change j.val + 1 ≤ k.val
          exact Nat.succ_le_of_lt h
        exact ((hzF_mono.monotone hle).trans_lt (hd_gap k).1).asymm hy.2
    exact congrArg d hkj
  obtain ⟨_, e, _, he_gap, he_zero⟩ :=
    exists_roots_critical_points hN_endpoints hdeg hroots hsimple
  intro c _ hc0
  obtain ⟨k, hk, hce⟩ := he_zero c hc0
  obtain ⟨j, hej⟩ := eq_of_derivative_eval_eq_zero hN hdeg hd_mono hd_zero
    (he_gap k hk).2.2
  rw [hce, hej]
  have hξ_gap : ξ (j.val + 1) ∈ Ioo (zF (lo j)) (zF (hi j)) := by
    constructor
    · simpa only [lo, zF] using (hzF_gap (lo j)).2
    · simpa only [hi, zF] using (hzF_gap (hi j)).1
  have hbound : |q.eval (ξ (j.val + 1))| ≤ |q.eval (d j)| :=
    abs_eval_le_abs_eval_critical_of_unique (hzF_zero (lo j)) (hzF_zero (hi j))
      (hd_gap j) ⟨hξ_gap.1.le, hξ_gap.2.le⟩ (hd_unique j)
  exact (halt (j.val + 1) (by have := j.isLt; lia)).trans hbound

/-- Sign changes across `N` consecutive intervals give `N` zeros; if one interval carries three
zeros, the function has `N + 2` distinct zeros between the first and the last point. -/
theorem _root_.exists_finset_zeros_of_sign_changes {D : ℝ → ℝ} (hD : Continuous D) {τ : ℕ → ℝ}
    {N : ℕ} (hτ : ∀ i < N, τ i < τ (i + 1)) (hsign : ∀ i < N, D (τ i) * D (τ (i + 1)) < 0)
    {k : ℕ} (hk : k < N) {w₁ t w₂ : ℝ} (h₀ : τ k < w₁) (h₁ : w₁ < t) (h₂ : t < w₂)
    (h₃ : w₂ < τ (k + 1)) (hw₁ : D w₁ = 0) (ht : D t = 0) (hw₂ : D w₂ = 0) :
    ∃ Z : Finset ℝ, Z.card = N + 2 ∧ ∀ z ∈ Z, τ 0 < z ∧ z < τ N ∧ D z = 0 := by
  have hmono : ∀ a b, a ≤ b → b ≤ N → τ a ≤ τ b := by
    intro a b hab hbN
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hτ b (by lia)).le
  have hex : ∀ i < N, ∃ y ∈ Ioo (τ i) (τ (i + 1)), D y = 0 :=
    fun i hi ↦ exists_Ioo_eq_zero_of_mul_neg hD (hτ i hi) (hsign i hi)
  choose! z hz hz0 using hex
  let I := (Finset.range N).erase k
  have hinj : Set.InjOn z I := by
    intro i hi j hj hij
    have hi' : i < N := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hj' : j < N := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := (hz i hi').2.trans_le (hmono (i + 1) j h (by lia))
      linarith [(hz j hj').1]
    · have := (hz j hj').2.trans_le (hmono (j + 1) i h (by lia))
      linarith [(hz i hi').1]
  let W : Finset ℝ := {w₁, t, w₂}
  have hW : W.card = 3 := by
    simp only [W]
    rw [Finset.card_insert_of_notMem (by simp; constructor <;> linarith),
      Finset.card_pair (by linarith)]
  have hdisj : Disjoint (I.image z) W := by
    rw [Finset.disjoint_left]
    intro y hy hyW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hi' : i < N := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hwin : τ k < z i ∧ z i < τ (k + 1) := by
      simp only [W, Finset.mem_insert, Finset.mem_singleton] at hyW
      rcases hyW with h | h | h <;> rw [h] <;> constructor <;> linarith
    rcases Nat.lt_or_gt_of_ne hik with h | h
    · linarith [(hz i hi').2, hmono (i + 1) k h hk.le]
    · linarith [(hz i hi').1, hmono (k + 1) i h hi'.le]
  refine ⟨I.image z ∪ W, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, hW,
      Finset.card_erase_of_mem (Finset.mem_range.mpr hk), Finset.card_range]
    lia
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hi' : i < N := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
      exact ⟨(hmono 0 i (Nat.zero_le _) hi'.le).trans_lt (hz i hi').1,
        (hz i hi').2.trans_le (hmono (i + 1) N hi' le_rfl), hz0 i hi'⟩
    · have hk0 := hmono 0 k (Nat.zero_le _) hk.le
      have hkN := hmono (k + 1) N hk le_rfl
      simp only [W, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨by linarith, by linarith, hw₁⟩
      · exact ⟨by linarith, by linarith, ht⟩
      · exact ⟨by linarith, by linarith, hw₂⟩

/-- The alternation points in angle coordinates: `τ 0 = 0 < τ 1 < ⋯ < τ (2 n) = 2 π`, where
`τ i = arccos (C (n - i))` for `i ≤ n` and `τ i = 2 π - arccos (C (i - n))` otherwise; the values
`p (cos (τ i))` have absolute value at least one and alternate in sign. -/
theorem alternation_angles {p : ℝ[X]} {n : ℕ} (hn : 0 < n) {C : ℕ → ℝ} (hC0 : C 0 = -1)
    (hCn : C n = 1) (hstep : ∀ k < n, C k < C (k + 1)) (hcrit : ∀ k ≤ n, 1 ≤ |p.eval (C k)|)
    (hprod : ∀ k < n, p.eval (C k) * p.eval (C (k + 1)) < 0) {τ : ℕ → ℝ}
    (hτ : ∀ i, τ i = if i ≤ n then Real.arccos (C (n - i))
      else 2 * Real.pi - Real.arccos (C (i - n))) :
    τ 0 = 0 ∧ τ (2 * n) = 2 * Real.pi ∧ (∀ i < 2 * n, τ i < τ (i + 1)) ∧
      (∀ i ≤ 2 * n, 1 ≤ |p.eval (Real.cos (τ i))|) ∧
      (∀ i < 2 * n, p.eval (Real.cos (τ i)) * p.eval (Real.cos (τ (i + 1))) < 0) := by
  have hmono : ∀ a b, a ≤ b → b ≤ n → C a ≤ C b := by
    intro a b hab hbn
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hstep b (by lia)).le
  have hmem : ∀ k ≤ n, C k ∈ Icc (-1 : ℝ) 1 := fun k hk ↦
    ⟨hC0 ▸ hmono 0 k (Nat.zero_le _) hk, hCn ▸ hmono k n hk le_rfl⟩
  have hlo : ∀ i ≤ n, τ i = Real.arccos (C (n - i)) := by
    intro i hi
    rw [hτ i]
    simp only [hi, ↓reduceIte]
  have hhi : ∀ i, n ≤ i → τ i = 2 * Real.pi - Real.arccos (C (i - n)) := by
    intro i hi
    rw [hτ i]
    by_cases h : i ≤ n
    · simp only [h, ↓reduceIte]
      rw [show n - i = 0 by lia, show i - n = 0 by lia, hC0, Real.arccos_neg_one]
      ring
    · simp only [h, ↓reduceIte]
  have hvlo : ∀ i ≤ n, p.eval (Real.cos (τ i)) = p.eval (C (n - i)) := by
    intro i hi
    rw [hlo i hi, Real.cos_arccos (hmem _ (by lia)).1 (hmem _ (by lia)).2]
  have hvhi : ∀ i, n ≤ i → i ≤ 2 * n → p.eval (Real.cos (τ i)) = p.eval (C (i - n)) := by
    intro i hi hi'
    rw [hhi i hi, Real.cos_two_pi_sub, Real.cos_arccos (hmem _ (by lia)).1 (hmem _ (by lia)).2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hlo 0 (Nat.zero_le _), Nat.sub_zero, hCn, Real.arccos_one]
  · rw [hhi (2 * n) (by lia), show 2 * n - n = n by lia, hCn, Real.arccos_one]
    ring
  · intro i hi
    by_cases h1 : i + 1 ≤ n
    · rw [hlo i (by lia), hlo (i + 1) h1]
      have := hstep (n - (i + 1)) (by lia)
      rw [show n - (i + 1) + 1 = n - i by lia] at this
      exact Real.arccos_lt_arccos (hmem _ (by lia)).1 this (hmem _ (by lia)).2
    · rw [hhi i (by lia), hhi (i + 1) (by lia)]
      have := hstep (i - n) (by lia)
      rw [show i - n + 1 = i + 1 - n by lia] at this
      linarith [Real.arccos_lt_arccos (hmem _ (by lia)).1 this (hmem _ (by lia)).2]
  · intro i hi
    by_cases h1 : i ≤ n
    · rw [hvlo i h1]; exact hcrit _ (by lia)
    · rw [hvhi i (by lia) hi]; exact hcrit _ (by lia)
  · intro i hi
    by_cases h1 : i + 1 ≤ n
    · rw [hvlo i (by lia), hvlo (i + 1) h1]
      have := hprod (n - (i + 1)) (by lia)
      rw [show n - (i + 1) + 1 = n - i by lia] at this
      linarith [mul_comm (p.eval (C (n - i))) (p.eval (C (n - (i + 1))))]
    · rw [hvhi i (by lia) (by lia), hvhi (i + 1) (by lia) (by lia),
        show i + 1 - n = i - n + 1 by lia]
      exact hprod (i - n) (by lia)

/-- A value of absolute value at least one, perturbed by less than one, keeps its sign. -/
private theorem mul_sub_pos_of_one_le_abs {r s a : ℝ} (hr : 1 ≤ |r|) (hs : |s| ≤ a)
    (ha : a < 1) : 0 < (r - s) * r := by
  have h1 : s * r ≤ |s| * |r| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |s| * |r| ≤ a * |r| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have h3 : r * r = |r| * |r| := (abs_mul_abs_self r).symm
  nlinarith

/-- The comparison harmonic `a cos (n (t - t₀) + θ)` as `c cos (n t) + s sin (n t)`. -/
private theorem harmonic_eq (a θ t₀ t : ℝ) (n : ℕ) :
    a * Real.cos (n * (t - t₀) + θ) =
      a * Real.cos (θ - n * t₀) * Real.cos (n * t) +
        -a * Real.sin (θ - n * t₀) * Real.sin (n * t) := by
  rw [show (n : ℝ) * (t - t₀) + θ = n * t + (θ - n * t₀) by ring, Real.cos_add]
  ring

/-- The comparison harmonic: if `μ² < n² (1 - y²)` and `σ = ±1`, there is a harmonic
`c cos (n t) + s sin (n t)` bounded by some `a < 1`, equal to `y` at `t₀`, whose derivative `S'` at
`t₀` satisfies `σ (μ - S') < 0`. -/
private theorem exists_comparison_harmonic {n : ℕ} (hn : 0 < n) {y μ t₀ σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hlt : μ ^ 2 < n ^ 2 * (1 - y ^ 2)) :
    ∃ a c s S' : ℝ, a < 1 ∧ (∀ t, |c * Real.cos (n * t) + s * Real.sin (n * t)| ≤ a) ∧
      c * Real.cos (n * t₀) + s * Real.sin (n * t₀) = y ∧
      HasDerivAt (fun t ↦ c * Real.cos (n * t) + s * Real.sin (n * t)) S' t₀ ∧
      σ * (μ - S') < 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : y ^ 2 + μ ^ 2 / n ^ 2 < 1 := by
    have : μ ^ 2 / n ^ 2 < 1 - y ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  set a := Real.sqrt ((1 + (y ^ 2 + μ ^ 2 / n ^ 2)) / 2) with ha
  have ha2 : a ^ 2 = (1 + (y ^ 2 + μ ^ 2 / n ^ 2)) / 2 := Real.sq_sqrt (by positivity)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hμn : 0 ≤ μ ^ 2 / n ^ 2 := by positivity
  have ha1 : a < 1 := by nlinarith
  have hya : |y| < a := abs_lt_of_sq_lt_sq (by nlinarith) ha0.le
  have hyaI : y / a ∈ Icc (-1 : ℝ) 1 := by
    have := abs_lt.mp hya
    constructor
    · rw [le_div_iff₀ ha0]; linarith
    · rw [div_le_iff₀ ha0]; linarith
  set u := Real.arccos (y / a) with hu
  have hcosu : Real.cos u = y / a := Real.cos_arccos hyaI.1 hyaI.2
  have hsinu0 : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hsinu2 : Real.sin u ^ 2 = 1 - (y / a) ^ 2 := by
    rw [← hcosu]; linarith [Real.sin_sq_add_cos_sq u]
  set θ := -σ * u with hθ
  have hcosθ : Real.cos θ = y / a := by rcases hσ with rfl | rfl <;> simp [hθ, hcosu]
  have hsinθ : Real.sin θ = -σ * Real.sin u := by rcases hσ with rfl | rfl <;> simp [hθ]
  set K := a * n * Real.sin u with hK
  have hK0 : 0 ≤ K := by positivity
  have hK2 : K ^ 2 = n ^ 2 * (a ^ 2 - y ^ 2) := by
    rw [hK, mul_pow, mul_pow, hsinu2]
    field_simp
  have hμK : |μ| < K := by
    refine abs_lt_of_sq_lt_sq ?_ hK0
    rw [hK2]
    have : μ ^ 2 / n ^ 2 < a ^ 2 - y ^ 2 := by nlinarith
    rwa [div_lt_iff₀ (by positivity), mul_comm] at this
  have hfun : (fun t ↦ a * Real.cos (θ - n * t₀) * Real.cos (n * t) +
      -a * Real.sin (θ - n * t₀) * Real.sin (n * t)) =
      fun t ↦ a * Real.cos (n * (t - t₀) + θ) :=
    _root_.funext fun t ↦ (harmonic_eq a θ t₀ t n).symm
  refine ⟨a, a * Real.cos (θ - n * t₀), -a * Real.sin (θ - n * t₀), σ * K, ha1, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [← harmonic_eq, abs_mul, abs_of_pos ha0]
    exact mul_le_of_le_one_right ha0.le (Real.abs_cos_le_one _)
  · rw [← harmonic_eq, sub_self, mul_zero, zero_add, hcosθ]
    field_simp
  · rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ ↦ (n : ℝ) * (t - t₀) + θ) n t₀ := by
      simpa using (((hasDerivAt_id t₀).sub_const t₀).const_mul (n : ℝ)).add_const θ
    have h3 := ((Real.hasDerivAt_cos _).comp t₀ h1).const_mul a
    convert h3 using 1
    · rfl
    · rw [sub_self, mul_zero, zero_add, hsinθ, hK]
      ring
  · have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσμle : σ * μ ≤ |μ| := by
      rcases hσ with rfl | rfl
      · simpa using le_abs_self μ
      · simpa using neg_le_abs μ
    nlinarith

/-- The contradiction in angle coordinates: alternation angles for `p (cos t)` together with a point
`t₀` strictly inside one of the `2 n` intervals where `μ² < n² (1 - p (cos t₀)²)`, `μ` being the
derivative of `p (cos t)` at `t₀`, produce `2 n + 2` zeros of a difference with a degree-`n`
harmonic. -/
private theorem false_of_comparison {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (hdeg : p.natDegree ≤ n)
    (hone : p.eval 1 = 1) {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) (hτN : τ (2 * n) = 2 * Real.pi)
    (hτinc : ∀ i < 2 * n, τ i < τ (i + 1))
    (hτcrit : ∀ i ≤ 2 * n, 1 ≤ |p.eval (Real.cos (τ i))|)
    (hτprod : ∀ i < 2 * n, p.eval (Real.cos (τ i)) * p.eval (Real.cos (τ (i + 1))) < 0)
    {k : ℕ} (hk : k < 2 * n) {t₀ μ : ℝ} (ht₀k : τ k < t₀) (ht₀k1 : t₀ < τ (k + 1))
    (hR : HasDerivAt (fun t ↦ p.eval (Real.cos t)) μ t₀)
    (hlt : μ ^ 2 < n ^ 2 * (1 - p.eval (Real.cos t₀) ^ 2)) : False := by
  set r := fun t ↦ p.eval (Real.cos t) with hr
  obtain ⟨σ, hσ, hσk, hσk1⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * r (τ k) < 0 ∧
      0 < σ * r (τ (k + 1)) := by
    rcases mul_neg_iff.mp (hτprod k hk) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨-1, Or.inr rfl, by simp only [hr]; linarith, by simp only [hr]; linarith⟩
    · exact ⟨1, Or.inl rfl, by simp only [hr]; linarith, by simp only [hr]; linarith⟩
  obtain ⟨a, c, s, S', ha1, hSabs, hSt₀, hS, hσS⟩ :=
    exists_comparison_harmonic (t₀ := t₀) hn hσ hlt
  set D : ℝ → ℝ := fun t ↦ p.eval (Real.cos t) - (c * Real.cos (n * t) + s * Real.sin (n * t))
    with hD
  have hDcont : Continuous D := by
    have hp : Continuous fun t : ℝ ↦ p.eval (Real.cos t) :=
      p.continuous.comp Real.continuous_cos
    simp only [hD]
    fun_prop
  have hDt₀ : D t₀ = 0 := by simp only [hD, hSt₀, sub_self]
  have hf : HasDerivAt (fun t ↦ σ * D t) (σ * (μ - S')) t₀ := (hR.sub hS).const_mul σ
  have hsignD : ∀ i ≤ 2 * n, 0 < D (τ i) * r (τ i) := fun i hi ↦
    mul_sub_pos_of_one_le_abs (hτcrit i hi) (hSabs _) ha1
  have hprodD : ∀ i < 2 * n, D (τ i) * D (τ (i + 1)) < 0 := by
    intro i hi
    have h1 := hsignD i hi.le
    have h2 := hsignD (i + 1) hi
    have h3 := hτprod i hi
    by_contra h
    push Not at h
    have h4 := mul_nonpos_of_nonneg_of_nonpos h h3.le
    have h5 : D (τ i) * D (τ (i + 1)) * (r (τ i) * r (τ (i + 1))) =
        D (τ i) * r (τ i) * (D (τ (i + 1)) * r (τ (i + 1))) := by ring
    simp only [hr] at h5 h1 h2
    nlinarith [mul_pos h1 h2]
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσDk : σ * D (τ k) < 0 := by
    have h1 := hsignD k hk.le
    have : (σ * D (τ k)) * (σ * r (τ k)) = D (τ k) * r (τ k) := by
      rw [show (σ * D (τ k)) * (σ * r (τ k)) = (σ * σ) * (D (τ k) * r (τ k)) by ring, hσ2,
        one_mul]
    nlinarith
  have hσDk1 : 0 < σ * D (τ (k + 1)) := by
    have h1 := hsignD (k + 1) hk
    have : (σ * D (τ (k + 1))) * (σ * r (τ (k + 1))) = D (τ (k + 1)) * r (τ (k + 1)) := by
      rw [show (σ * D (τ (k + 1))) * (σ * r (τ (k + 1))) =
        (σ * σ) * (D (τ (k + 1)) * r (τ (k + 1))) by ring, hσ2, one_mul]
    nlinarith
  obtain ⟨y₁, hy₁, hfy₁⟩ := hf.exists_Ioo_lt_of_neg hσS ht₀k
  obtain ⟨y₂, hy₂, hfy₂⟩ := hf.exists_Ioo_gt_of_neg hσS ht₀k1
  simp only [hDt₀, mul_zero] at hfy₁ hfy₂
  have hp1 : D (τ k) * D y₁ < 0 := by
    have : D (τ k) * D y₁ = (σ * D (τ k)) * (σ * D y₁) := by
      rw [show (σ * D (τ k)) * (σ * D y₁) = (σ * σ) * (D (τ k) * D y₁) by ring, hσ2, one_mul]
    rw [this]; exact mul_neg_of_neg_of_pos hσDk hfy₁
  have hp2 : D y₂ * D (τ (k + 1)) < 0 := by
    have : D y₂ * D (τ (k + 1)) = (σ * D y₂) * (σ * D (τ (k + 1))) := by
      rw [show (σ * D y₂) * (σ * D (τ (k + 1))) = (σ * σ) * (D y₂ * D (τ (k + 1))) by ring, hσ2,
        one_mul]
    rw [this]; exact mul_neg_of_neg_of_pos hfy₂ hσDk1
  obtain ⟨w₁, hw₁, hDw₁⟩ := exists_Ioo_eq_zero_of_mul_neg hDcont hy₁.1 hp1
  obtain ⟨w₂, hw₂, hDw₂⟩ := exists_Ioo_eq_zero_of_mul_neg hDcont hy₂.2 hp2
  obtain ⟨Z, hZcard, hZ⟩ := exists_finset_zeros_of_sign_changes hDcont hτinc hprodD hk
    hw₁.1 (hw₁.2.trans hy₁.2) (hy₂.1.trans hw₂.1) hw₂.2 hDw₁ hDt₀ hDw₂
  have hD0 : D 0 ≠ 0 := by
    simp only [hD, Real.cos_zero, hone]
    have := (abs_le.mp (hSabs 0)).2
    simp only [mul_zero, Real.cos_zero, Real.sin_zero] at this ⊢
    linarith
  have hcount := card_zeros_eval_cos_sub_trig_le (p := p) (n := n) (c := c) (s := s) (z := Z)
    hdeg (fun t ht ↦ ⟨(hτ0 ▸ (hZ t ht).1).le, hτN ▸ (hZ t ht).2.1⟩)
    (fun t ht ↦ (hZ t ht).2.2) ⟨0, hD0⟩
  lia

/-- **Inverse Bernstein inequality.** Let `p` have degree `n > 0`, `n` simple roots in `(-1, 1)`,
`p 1 = 1`, `p (-1) = (-1) ^ n`, and `|p c| ≥ 1` at every critical point `c ∈ (-1, 1)`. Then
`n² (1 - p(x)²) ≤ (1 - x²) p'(x)²` on `[-1, 1]`. The proof compares `p (cos t)` with a harmonic
`a cos (n (t - t₀) + θ)` and counts zeros (Erdélyi–Hardin–Saff, arXiv:1307.4056). -/
theorem sq_mul_one_sub_sq_le_of_abs_eval_critical
    {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (hdeg : p.natDegree = n)
    (hroots : (p.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = n) (hsimple : p.roots.Nodup)
    (hone : p.eval 1 = 1) (hmone : p.eval (-1) = (-1) ^ n)
    (hcrit : ∀ c ∈ Ioo (-1 : ℝ) 1, p.derivative.eval c = 0 → 1 ≤ |p.eval c|)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (n : ℝ) ^ 2 * (1 - p.eval x ^ 2) ≤ (1 - x ^ 2) * p.derivative.eval x ^ 2 := by
  by_cases hpx : 1 ≤ |p.eval x|
  · exact sq_mul_one_sub_sq_le_of_one_le_abs_eval hx hpx
  push Not at hpx
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC0, hCn, hstep, hcritC, hprod, -⟩ :=
    exists_alternation_points hn hdeg hroots hsimple hone hmone hcrit
  have hmonoC : ∀ a b, a ≤ b → b ≤ n → C a ≤ C b := by
    intro a b hab hbn
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hstep b (by lia)).le
  have hmemC : ∀ k ≤ n, C k ∈ Icc (-1 : ℝ) 1 := fun k hk ↦
    ⟨hC0 ▸ hmonoC 0 k (Nat.zero_le _) hk, hCn ▸ hmonoC k n hk le_rfl⟩
  have hxC : ∀ k ≤ n, C k ≠ x := by
    intro k hk h
    have := hcritC k hk
    rw [h] at this
    linarith
  have hxlt : x < C n := lt_of_le_of_ne (hCn ▸ hx.2) (hxC n le_rfl).symm
  have hex : ∃ m, x < C m := ⟨n, hxlt⟩
  have hxm : x < C (Nat.find hex) := Nat.find_spec hex
  have hmn : Nat.find hex ≤ n := Nat.find_min' hex hxlt
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hC0] at hxm
    linarith [hx.1]
  set j := Nat.find hex - 1 with hj
  have hjn : j < n := by lia
  have hCjx : C j < x := lt_of_le_of_ne (not_lt.mp (Nat.find_min hex (by lia))) (hxC j hjn.le)
  have hxCj : x < C (j + 1) := by rw [show j + 1 = Nat.find hex by lia]; exact hxm
  set τ : ℕ → ℝ := fun i ↦ if i ≤ n then Real.arccos (C (n - i))
    else 2 * Real.pi - Real.arccos (C (i - n)) with hτ
  obtain ⟨hτ0, hτN, hτinc, hτcrit, hτprod⟩ :=
    alternation_angles (p := p) hn hC0 hCn hstep hcritC hprod (τ := τ) (fun i ↦ rfl)
  set k := n - 1 - j with hk
  have hτk : τ k = Real.arccos (C (j + 1)) := by
    simp only [hτ, show k ≤ n by lia, ↓reduceIte, show n - k = j + 1 by lia]
  have hτk1 : τ (k + 1) = Real.arccos (C j) := by
    simp only [hτ, show k + 1 ≤ n by lia, ↓reduceIte, show n - (k + 1) = j by lia]
  have hx1 : -1 < x := (hC0 ▸ hmonoC 0 j (Nat.zero_le _) hjn.le).trans_lt hCjx
  have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hxCj.trans_le (hmemC _ (by lia)).2]
  have hcosx : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have hsin2 : Real.sin (Real.arccos x) ^ 2 = 1 - x ^ 2 := by
    rw [Real.sin_arccos, Real.sq_sqrt hx2.le]
  have hR := (p.hasDerivAt (Real.cos (Real.arccos x))).comp (Real.arccos x)
    (Real.hasDerivAt_cos (Real.arccos x))
  refine false_of_comparison hn hdeg.le hone hτ0 hτN hτinc hτcrit hτprod (k := k) (by lia)
    (t₀ := Real.arccos x) ?_ ?_ hR ?_
  · rw [hτk]; exact Real.arccos_lt_arccos hx.1 hxCj (hmemC _ (by lia)).2
  · rw [hτk1]; exact Real.arccos_lt_arccos (hmemC _ hjn.le).1 hCjx hx.2
  · rw [hcosx, mul_pow, neg_sq, hsin2]
    linarith

/-- A real polynomial of degree `n` whose values change sign across `n` consecutive intervals
`(C k, C (k + 1))` has simple roots, exactly one in each interval and no others, and at the root
in `(C k, C (k + 1))` its derivative has the sign of `h (C (k + 1))`. -/
theorem roots_of_sign_changes {h : ℝ[X]} {n : ℕ} (hn : 0 < n) (hdeg : h.natDegree = n)
    {C : ℕ → ℝ} (hC : ∀ k < n, C k < C (k + 1))
    (hsign : ∀ k < n, h.eval (C k) * h.eval (C (k + 1)) < 0) :
    h.roots.Nodup ∧ h.roots.card = n ∧
      (∀ r, h.IsRoot r → ∃ k < n, r ∈ Ioo (C k) (C (k + 1))) ∧
      (∀ k < n, ∀ r ∈ Ioo (C k) (C (k + 1)), h.IsRoot r →
        0 < h.derivative.eval r * h.eval (C (k + 1))) := by
  have hmono : ∀ a b, a ≤ b → b ≤ n → C a ≤ C b := by
    intro a b hab hbn
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hC b (by lia)).le
  have hne : h ≠ 0 := by
    rintro rfl
    simp at hdeg
    lia
  have hex : ∀ k < n, ∃ y ∈ Ioo (C k) (C (k + 1)), h.eval y = 0 := fun k hk ↦
    exists_Ioo_eq_zero_of_mul_neg (f := fun x ↦ h.eval x) h.continuous (hC k hk) (hsign k hk)
  choose! z hz hz0 using hex
  have hdisj : ∀ i < n, ∀ j < n, ∀ y, y ∈ Ioo (C i) (C (i + 1)) →
      y ∈ Ioo (C j) (C (j + 1)) → i = j := by
    intro i hi j hj y hyi hyj
    by_contra hij
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · linarith [hyi.2, hyj.1, hmono (i + 1) j hlt hj.le]
    · linarith [hyj.2, hyi.1, hmono (j + 1) i hlt hi.le]
  have hinj : Set.InjOn z (Finset.range n) := by
    intro i hi j hj hij
    have hi' : i < n := by simpa using hi
    have hj' : j < n := by simpa using hj
    exact hdisj i hi' j hj' (z i) (hz i hi') (hij ▸ hz j hj')
  let Z := (Finset.range n).image z
  have hZcard : Z.card = n := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hZle : Z.val ≤ h.roots := by
    rw [Multiset.le_iff_subset Z.nodup]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hy)
    exact (mem_roots hne).mpr (hz0 i (Finset.mem_range.mp hi))
  have hroots : h.roots = Z.val := (Multiset.eq_of_le_of_card_le hZle (by
    rw [Finset.card_val, hZcard, ← hdeg]
    exact card_roots' h)).symm
  have hroot_mem : ∀ r, h.IsRoot r → ∃ k < n, r = z k := by
    intro r hr
    have hr' : r ∈ Z := by
      rw [← Finset.mem_val, ← hroots]
      exact (mem_roots hne).mpr hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr'
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  have hnodup : h.roots.Nodup := hroots ▸ Z.nodup
  refine ⟨hnodup, by rw [hroots, Finset.card_val, hZcard], fun r hr ↦ ?_, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := hroot_mem r hr
    exact ⟨k, hk, hz k hk⟩
  intro k hk r hr hroot
  have huniq : ∀ y ∈ Ioo (C k) (C (k + 1)), h.IsRoot y → y = z k := by
    intro y hy hyr
    obtain ⟨j, hj, rfl⟩ := hroot_mem y hyr
    rw [hdisj j hj k hk (z j) (hz j hj) hy]
  have hd : h.derivative.eval r ≠ 0 := by
    intro hd0
    have h1 : 1 < h.rootMultiplicity r :=
      (one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hroot, hd0⟩
    have h2 := Multiset.nodup_iff_count_le_one.mp hnodup r
    rw [count_roots] at h2
    lia
  have hc : h.eval (C (k + 1)) ≠ 0 := right_ne_zero_of_mul (hsign k hk).ne
  by_contra hpos
  have hneg : h.eval (C (k + 1)) * h.derivative.eval r < 0 := by
    rw [mul_comm]
    exact lt_of_le_of_ne (not_lt.mp hpos) (mul_ne_zero hd hc)
  have hder : HasDerivAt (fun x ↦ h.eval (C (k + 1)) * h.eval x)
      (h.eval (C (k + 1)) * h.derivative.eval r) r := (h.hasDerivAt r).const_mul _
  obtain ⟨y, hy, hgy⟩ := hder.exists_Ioo_gt_of_neg hneg hr.2
  replace hgy : h.eval (C (k + 1)) * h.eval y < 0 := by simpa [hroot.eq_zero] using hgy
  obtain ⟨w, hw, hw0⟩ := exists_Ioo_eq_zero_of_mul_neg
    (f := fun x ↦ h.eval (C (k + 1)) * h.eval x) (continuous_const.mul h.continuous) hy.2
    (mul_neg_of_neg_of_pos hgy (mul_self_pos.mpr hc))
  have hw' : h.IsRoot w := (mul_eq_zero.mp hw0).resolve_left hc
  have := (huniq w ⟨hr.1.trans (hy.1.trans hw.1), hw.2⟩ hw').trans
    (huniq r hr hroot).symm
  linarith [hy.1, hw.1]

end Polynomial
