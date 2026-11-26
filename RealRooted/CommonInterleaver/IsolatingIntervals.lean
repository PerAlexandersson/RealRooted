/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CommonInterleaver.NegativeGrid
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Tactic

/-!
# Common isolating intervals from simple nonnegative mixtures

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted

/-- A simple zero and otherwise nonpositive roots leave exactly one fewer negative roots. -/
theorem card_negative_roots_eq_sub_one {p : ℝ[X]} (hs : p.Splits)
    (hn : p.roots.Nodup) (hz : 0 ∈ p.roots) (hpos : ∀ x ∈ p.roots, x ≤ 0) :
    (p.roots.filter (· < 0)).card = p.natDegree - 1 := by
  classical
  have he : p.roots.filter (fun x => ¬x < 0) = {0} := by
    have hh : p.roots.filter (fun x => ¬x < 0) = p.roots.filter (0 = ·) := by
      apply Multiset.filter_congr
      intro x hx
      have := hpos x hx
      constructor <;> intro h <;> grind
    rw [hh, Multiset.filter_eq, Multiset.count_eq_one_of_mem hn hz]
    rfl
  have hh := congrArg Multiset.card (Multiset.filter_add_not (· < 0) p.roots)
  rw [Multiset.card_add, he, Multiset.card_singleton, splits_iff_card_roots.mp hs] at hh
  lia

private theorem exhaust_negative_roots {p : ℝ[X]} {d : ℕ} {r : Fin d → ℝ}
    (hp : p ≠ 0) (inj : Function.Injective r) (negative : ∀ i, r i < 0)
    (root : ∀ i, p.IsRoot (r i)) (count : (p.roots.filter (· < 0)).card = d)
    {y : ℝ} (hy : y < 0) (ey : p.IsRoot y) : ∃ j, r j = y := by
  classical
  let points := (univ : Finset (Fin d)).map ⟨r, inj⟩
  let negatives := (p.roots.filter (· < 0)).toFinset
  have incl : points ⊆ negatives := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_map.mp hx
    exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
      ⟨(mem_roots hp).mpr (root j), negative j⟩)
  have size : points.card = d := by simp [points]
  have eq : points = negatives := eq_of_subset_of_card_le incl
    (((Multiset.toFinset_card_le _).trans_eq count).trans_eq size.symm)
  have mem : y ∈ negatives := Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
    ⟨(mem_roots hp).mpr ey, hy⟩)
  obtain ⟨j, _, h⟩ := mem_map.mp (eq.symm ▸ mem : y ∈ points)
  exact ⟨j, h⟩

private theorem grid_signed_eval {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff)
    {x : ℝ} (hx : ¬ p.IsRoot x) {j : ℕ}
    (hcount : (p.roots.filter (x < ·)).card = j) :
    0 < (-1 : ℝ) ^ j * p.eval x := by
  have hh := hp.eval_mul_leadingCoeff_neg_one_pow_pos (leadingCoeff_ne_zero.mp hlc.ne') hx
  rw [hcount] at hh
  nlinarith

private theorem signed_grid_change {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hc : ∀ j, 0 < (-1 : ℝ) ^ (j.val + 1) * p.eval (c j)) (j : Fin m) :
    p.eval (c j.castSucc) * p.eval (c j.succ) < 0 := by
  have h1 := hc j.castSucc
  have h2 := hc j.succ
  have hp : ((-1 : ℝ) ^ (j.val + 1)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have h2' : 0 < -((-1 : ℝ) ^ (j.val + 1)) * p.eval (c j.succ) := by
    simpa only [Fin.val_succ, pow_succ, mul_neg_one] using h2
  have hh := mul_pos h1 h2'
  change 0 < ((-1 : ℝ) ^ (j.val + 1) * p.eval (c j.castSucc)) *
    (-((-1 : ℝ) ^ (j.val + 1)) * p.eval (c j.succ)) at hh
  have he : ((-1 : ℝ) ^ (j.val + 1) * p.eval (c j.castSucc)) *
      (-((-1 : ℝ) ^ (j.val + 1)) * p.eval (c j.succ)) =
      -p.eval (c j.castSucc) * p.eval (c j.succ) := by
    calc
      _ = -((-1 : ℝ) ^ (j.val + 1)) ^ 2 *
          (p.eval (c j.castSucc) * p.eval (c j.succ)) := by ring
      _ = _ := by rw [hp]; ring
  rw [he] at hh
  linarith

/-- Compatibility and simplicity separate the finite family's root slots. -/
private theorem simple_mixture_grid
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ[X]) {m : ℕ}
    (hnn : ∀ i, HasNonnegCoeffs (f i))
    (hall : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∃ i, 0 < w i) →
      let p := ∑ i, C (w i) * f i
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree = m + 1 ∧
        ∀ r ∈ p.roots, r ≤ 0) :
    ∃ c : Fin (m + 1) → ℝ, StrictAnti c ∧ (∀ j, c j < 0) ∧
      ∀ i, (f i).Splits ∧ HasPosLeadingCoeff (f i) ∧
        ∀ j, ¬ (f i).IsRoot (c j) ∧ ((f i).roots.filter (c j < ·)).card = j.val + 1 := by
  classical
  have hend i := hall (fun j => if j = i then 1 else 0)
    (by intro j; split_ifs <;> norm_num) ⟨i, by simp⟩
  simp only [apply_ite C, map_one, map_zero, ite_mul, one_mul, zero_mul,
    sum_ite_eq', mem_univ, ite_true] at hend
  have hpair (i j : ι) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :=
    hall (fun l => (if l = i then a else 0) + if l = j then b else 0)
      (by intro l; positivity) ⟨i, by simp; positivity⟩
  simp only [map_add, apply_ite C, map_zero, add_mul, ite_mul, zero_mul,
    sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hpair
  have hpos i : HasPosLeadingCoeff (f i) :=
    (hnn i).pos_leadingCoeff (ne_zero_of_mem_roots (hend i).2.2.1)
  have hcombo i j : PosComboRealRooted (f i) (f j) := by
    intro a b ha hb
    exact ⟨ne_zero_of_mem_roots (hpair i j ha hb).2.2.1, (hpair i j ha hb).1⟩
  have hcross i j l (hl : 0 < l) (hld : l < m + 1) :=
    rootSeqDesc_getD_lt_of_simple_posCombo (hpos i) (hpos j) (hnn i) (hnn j)
      (hcombo i j) ((hend i).2.2.2.1.trans (hend j).2.2.2.1.symm)
      (hend i).2.1 (hend j).2.1 (by
        intro u hμ
        simpa using (hpair i j (by norm_num : (0 : ℝ) < 1) hμ).2.1) hl (by
          rwa [(hend i).2.2.2.1])
  obtain ⟨c, hcanti, hcneg, hccount⟩ := exists_negative_root_grid f
    (fun i => (hend i).1) (fun i => (hend i).2.2.2.1) (fun i => (hend i).2.1)
    (fun i => (hend i).2.2.2.2) hcross
  exact ⟨c, hcanti, hcneg, fun i => ⟨(hend i).1, hpos i, hccount i⟩⟩

/-- A finite family whose nonzero nonnegative mixtures have simple nonpositive
roots and a simple zero has common open isolating intervals for all its negative
roots, uniformly over the weights. -/
theorem exists_common_isolating_intervals_of_simple_mixtures
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ[X]) {m : ℕ}
    (hnn : ∀ i, HasNonnegCoeffs (f i))
    (hall : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∃ i, 0 < w i) →
      let p := ∑ i, C (w i) * f i
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree = m + 1 ∧
        ∀ r ∈ p.roots, r ≤ 0) :
    ∃ lower upper : Fin m → ℝ, (∀ i, upper i < 0) ∧
      Pairwise (fun i j => Disjoint (Set.Ioo (lower i) (upper i))
        (Set.Ioo (lower j) (upper j))) ∧
      ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∃ i, 0 < w i) →
        ∀ i, ∃! y, y ∈ Set.Ioo (lower i) (upper i) ∧
          (∑ j, C (w j) * f j).IsRoot y := by
  classical
  obtain ⟨c, hcanti, hcneg, hfamily⟩ := simple_mixture_grid f hnn hall
  let x : Fin (m + 1) → ℝ := fun i => c i.rev
  have hx : StrictMono x := hcanti.comp Fin.rev_strictAnti
  have hdisj : Pairwise (fun i j : Fin m => Disjoint
      (Set.Ioo (x i.castSucc) (x i.succ)) (Set.Ioo (x j.castSucc) (x j.succ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    rcases lt_or_gt_of_ne hij with h | h
    · have hh := hx.monotone (show i.succ ≤ j.castSucc by change i.val + 1 ≤ j.val; lia)
      exact (not_lt_of_ge hh) (hyj.1.trans hyi.2)
    · have hh := hx.monotone (show j.succ ≤ i.castSucc by change j.val + 1 ≤ i.val; lia)
      exact (not_lt_of_ge hh) (hyi.1.trans hyj.2)
  refine ⟨fun i => x i.castSucc, fun i => x i.succ, fun i => hcneg _, hdisj, ?_⟩
  intro w hw hp
  let p := ∑ i, C (w i) * f i
  have hdata := hall w hw hp
  have hpne : p ≠ 0 := ne_zero_of_mem_roots hdata.2.2.1
  have hsign j : 0 < (-1 : ℝ) ^ (j.val + 1) * p.eval (c j) := by
    simp only [p, eval_finsetSum, eval_mul, eval_C, mul_sum]
    apply sum_pos'
    · intro i _
      have hh := grid_signed_eval (hfamily i).1 (hfamily i).2.1 ((hfamily i).2.2 j).1
        ((hfamily i).2.2 j).2
      nlinarith [hw i]
    · obtain ⟨i, hi⟩ := hp
      refine ⟨i, mem_univ _, ?_⟩
      have hh := grid_signed_eval (hfamily i).1 (hfamily i).2.1 ((hfamily i).2.2 j).1
        ((hfamily i).2.2 j).2
      nlinarith
  have hchanges (i : Fin m) : p.eval (x i.castSucc) * p.eval (x i.succ) < 0 := by
    have h1 : i.castSucc.rev = i.rev.succ := Fin.ext (by simp; lia)
    have h2 : i.succ.rev = i.rev.castSucc := Fin.ext (by simp)
    change p.eval (c i.castSucc.rev) * p.eval (c i.succ.rev) < 0
    rw [h1, h2, mul_comm]
    exact signed_grid_change hsign i.rev
  obtain ⟨r, hrmono, hroot⟩ := exists_ordered_roots_of_strict_sign_changes x hx hchanges
  have hrneg i : r i < 0 := (hroot i).2.1.trans (hcneg _)
  have hcount : (p.roots.filter (· < 0)).card = m := by
    rw [card_negative_roots_eq_sub_one hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.2,
      hdata.2.2.2.1]
    lia
  intro i
  refine ⟨r i, ⟨⟨(hroot i).1, (hroot i).2.1⟩, (hroot i).2.2⟩, ?_⟩
  rintro y ⟨hy, hpy⟩
  obtain ⟨j, rfl⟩ := exhaust_negative_roots hpne hrmono.injective hrneg
    (fun j => (hroot j).2.2) hcount (hy.2.trans (hcneg _)) hpy
  by_cases he : i = j
  · rw [he]
  · exact False.elim (Set.disjoint_left.mp (hdisj he) hy ⟨(hroot j).1, (hroot j).2.1⟩)

end RealRooted
