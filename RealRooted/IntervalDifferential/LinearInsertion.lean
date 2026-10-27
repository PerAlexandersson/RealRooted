/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.IntervalDifferential.Degree
public import RealRooted.IntervalDifferential.Certificates
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Order.Fin.Tuple
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Field.Basic
meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Linear insertion into the centered differential operator

The real linear factor `L-a` from Appendix C raises degree by one. Its
evaluation at an old root is `(r²-1)F'(r)`, while its endpoint evaluations
are scalar multiples of those of `F`. These are the signs used in the
simple-root interval insertion argument.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.IntervalDifferential

/-- Evaluation at an old zero isolates the derivative term. -/
theorem zigzagLinearFactor_eval_root (a r : ℝ) (F : ℝ[X]) (hr : F.IsRoot r) :
    (zigzagLinearFactor a F).eval r = (r ^ 2 - 1) * F.derivative.eval r := by
  simp only [zigzagLinearFactor, zigzagOperator_apply, eval_sub, eval_add,
    eval_mul, eval_pow, eval_X, eval_one, eval_C, hr.eq_zero]
  ring

/-- The left endpoint value of the insertion. -/
theorem zigzagLinearFactor_eval_neg_one (a : ℝ) (F : ℝ[X]) :
    (zigzagLinearFactor a F).eval (-1) = -(3 + a) * F.eval (-1) := by
  simp only [zigzagLinearFactor, zigzagOperator_apply, eval_sub, eval_add,
    eval_mul, eval_pow, eval_X, eval_one, eval_C]
  ring

/-- The right endpoint value of the insertion. -/
theorem zigzagLinearFactor_eval_one (a : ℝ) (F : ℝ[X]) :
    (zigzagLinearFactor a F).eval 1 = (3 - a) * F.eval 1 := by
  simp only [zigzagLinearFactor, zigzagOperator_apply, eval_sub, eval_add,
    eval_mul, eval_pow, eval_X, eval_one, eval_C]
  ring

/- The sign-product argument follows the one in
`RealRooted.Interlacing.Residue`. It is local here because that older module
cannot be imported by a module-compatible file. -/
private theorem positive_signed_difference_product (M : Multiset ℝ) (s : ℝ)
    (hs : s ∉ M) :
    0 < (M.map (fun r => s - r)).prod *
      (-1 : ℝ) ^ M.countP (fun r => s < r) := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.countP_cons]
    have hnot : s ∉ t := fun ht => hs (Multiset.mem_cons_of_mem ht)
    have hne : a ≠ s := fun heq => hs (heq ▸ Multiset.mem_cons_self a t)
    have hpos := ih hnot
    by_cases hlt : s < a
    · simp only [hlt, ite_true, pow_add, pow_one]
      have hfactor :
          (s - a) * (t.map (fun r => s - r)).prod *
            ((-1 : ℝ) ^ t.countP (fun r => s < r) * -1) =
          (a - s) * ((t.map (fun r => s - r)).prod *
            (-1 : ℝ) ^ t.countP (fun r => s < r)) := by ring
      rw [hfactor]
      exact mul_pos (sub_pos.mpr hlt) hpos
    · simp only [hlt, ite_false, Nat.add_zero]
      have halt : a < s := lt_of_le_of_ne (not_lt.mp hlt) hne
      have hfactor :
          (s - a) * (t.map (fun r => s - r)).prod *
            (-1 : ℝ) ^ t.countP (fun r => s < r) =
          (s - a) * ((t.map (fun r => s - r)).prod *
            (-1 : ℝ) ^ t.countP (fun r => s < r)) := by ring
      rw [hfactor]
      exact mul_pos (sub_pos.mpr halt) hpos

private theorem derivative_signed_at_simple_root {F : ℝ[X]}
    (hF : F.Splits) (hnd : F.roots.Nodup) (hF0 : F ≠ 0)
    {s : ℝ} (hs : s ∈ F.roots) :
    0 < F.leadingCoeff * F.derivative.eval s *
      (-1 : ℝ) ^ F.roots.countP (fun r => s < r) := by
  classical
  have hnot : s ∉ F.roots.erase s := by
    intro h
    have hc : F.roots.count s = 1 := Multiset.count_eq_one_of_mem hnd hs
    rw [← Multiset.count_pos, Multiset.count_erase_self, hc] at h
    lia
  have hcount : (F.roots.erase s).countP (fun r => s < r) =
      F.roots.countP (fun r => s < r) := by
    rw [← Multiset.cons_erase hs, Multiset.countP_cons]
    simp
  have hder : F.derivative.eval s =
      F.leadingCoeff * ((F.roots.erase s).map (fun r => s - r)).prod := by
    conv_lhs => rw [hF.eq_prod_roots]
    rw [derivative_C_mul, eval_mul, eval_C,
      eval_multiset_prod_X_sub_C_derivative hs]
  rw [hder, mul_assoc, mul_assoc]
  have hprod := positive_signed_difference_product (F.roots.erase s) s hnot
  rw [hcount] at hprod
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  nlinarith [sq_pos_of_ne_zero hlc]

private theorem eval_signed_away_from_roots {F : ℝ[X]}
    (hF : F.Splits) (hF0 : F ≠ 0) {s : ℝ} (hs : s ∉ F.roots) :
    0 < F.leadingCoeff * F.eval s *
      (-1 : ℝ) ^ F.roots.countP (fun r => s < r) := by
  classical
  rw [hF.eval_eq_prod_roots s, mul_assoc, mul_assoc]
  have hprod := positive_signed_difference_product F.roots s hs
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  nlinarith [sq_pos_of_ne_zero hlc]

private theorem sq_sub_one_neg_of_mem_Ioo {s : ℝ} (hs : -1 < s ∧ s < 1) :
    s ^ 2 - 1 < 0 := by
  have hprod := mul_pos (show 0 < 1 - s by linarith)
    (show 0 < 1 + s by linarith)
  nlinarith

/-- A root of the linear insertion is never an old root when all old roots
are simple and strictly inside the unit interval. Appendix C.1. -/
theorem zigzagLinearFactor_eval_base_ne_zero {F : ℝ[X]}
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hinside : ∀ z ∈ F.roots, -1 < z ∧ z < 1)
    (a s : ℝ) (hG : (zigzagLinearFactor a F).eval s = 0) :
    F.eval s ≠ 0 := by
  intro hzero
  have hs : s ∈ F.roots := (mem_roots hF0).mpr hzero
  have hderpos := derivative_signed_at_simple_root hF hnd hF0 hs
  have hder : F.derivative.eval s ≠ 0 := by
    intro hderzero
    rw [hderzero] at hderpos
    simp at hderpos
  have hfactor := sq_sub_one_neg_of_mem_Ioo (hinside _ hs)
  rw [zigzagLinearFactor_eval_root a s F ((mem_roots hF0).mp hs)] at hG
  exact (mul_ne_zero (ne_of_lt hfactor) hder) hG

private theorem root_count_jump {F : ℝ[X]} (hnd : F.roots.Nodup)
    {x y : ℝ} (hxy : x < y) (hy : y ∈ F.roots)
    (hgap : ∀ z ∈ F.roots, x < z → z < y → False) :
    F.roots.countP (fun z => x < z) =
      F.roots.countP (fun z => y < z) + 1 := by
  classical
  let s : Finset ℝ := F.roots.toFinset
  have hval : s.val = F.roots := by
    change (F.roots.toFinset).val = F.roots
    rw [← Multiset.toFinset_eq hnd]
  have hfilter : s.filter (fun z => x < z) =
      insert y (s.filter (fun z => y < z)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzs, hxz⟩ := Finset.mem_filter.mp hz
      by_cases heq : z = y
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · have hyz : y < z := by
          by_contra hn
          exact hgap z (Multiset.mem_toFinset.mp hzs) hxz
            (lt_of_le_of_ne (le_of_not_gt hn) heq)
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hzs, hyz⟩))
    · intro hz
      rcases Finset.mem_insert.mp hz with heq | hz
      · subst z
        exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hy, hxy⟩
      · obtain ⟨hzs, hyz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzs, hxy.trans hyz⟩
  have hcount (u : ℝ) : F.roots.countP (fun z => u < z) =
      (s.filter (fun z => u < z)).card := by
    rw [← hval, Multiset.countP_eq_card_filter, ← Finset.filter_val]
    rfl
  have hy_not : y ∉ s.filter (fun z => y < z) := by simp
  rw [hcount x, hcount y, hfilter, Finset.card_insert_of_notMem hy_not]

private theorem signed_product_opposite (c u v : ℝ) (k : ℕ)
    (hc : c ≠ 0)
    (hu : 0 < c * u * (-1 : ℝ) ^ (k + 1))
    (hv : 0 < c * v * (-1 : ℝ) ^ k) : u * v < 0 := by
  have hsquare : (((-1 : ℝ) ^ k) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [pow_succ] at hu
  have hprod := mul_pos hu hv
  have heq :
      (c * u * ((-1 : ℝ) ^ k * -1)) * (c * v * (-1 : ℝ) ^ k) =
        -(c ^ 2 * (u * v)) := by
    calc
      _ = -(c ^ 2 * (u * v) * (((-1 : ℝ) ^ k) ^ 2)) := by ring
      _ = _ := by rw [hsquare]; ring
  rw [heq] at hprod
  have hcpos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  by_contra hn
  have huv : 0 ≤ u * v := le_of_not_gt hn
  linarith [mul_nonneg hcpos.le huv]

private theorem signed_product_same (c u v : ℝ) (k : ℕ)
    (hc : c ≠ 0)
    (hu : 0 < c * u * (-1 : ℝ) ^ k)
    (hv : 0 < c * v * (-1 : ℝ) ^ k) : 0 < u * v := by
  have hsquare : (((-1 : ℝ) ^ k) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  have hprod := mul_pos hu hv
  have heq :
      (c * u * (-1 : ℝ) ^ k) * (c * v * (-1 : ℝ) ^ k) =
        c ^ 2 * (u * v) := by
    calc
      _ = c ^ 2 * (u * v) * (((-1 : ℝ) ^ k) ^ 2) := by ring
      _ = _ := by rw [hsquare]; ring
  rw [heq] at hprod
  have hcpos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  by_contra hn
  have huv : u * v ≤ 0 := le_of_not_gt hn
  linarith [mul_nonpos_of_nonneg_of_nonpos hcpos.le huv]

private theorem no_root_between_adjacent {F : ℝ[X]} {n : ℕ}
    (s : Finset ℝ) (hs : s = F.roots.toFinset) (hcard : s.card = n + 1)
    (i : Fin n) (z : ℝ) (hz : z ∈ F.roots)
    (hleft : s.orderEmbOfFin hcard i.castSucc < z)
    (hright : z < s.orderEmbOfFin hcard i.succ) : False := by
  let r := s.orderEmbOfFin hcard
  have hzmem : z ∈ s := hs ▸ Multiset.mem_toFinset.mpr hz
  have hzrange : z ∈ Set.range r := by
    rw [Finset.range_orderEmbOfFin s hcard]
    exact hzmem
  obtain ⟨k, rfl⟩ := hzrange
  have hik : i.castSucc < k := r.lt_iff_lt.mp hleft
  have hki : k < i.succ := r.lt_iff_lt.mp hright
  have hik' : i.val < k.val := hik
  have hki' : k.val < i.val + 1 := hki
  lia

private theorem sign_change_of_two_opposite_signs
    {a b c d : ℝ} (hac : a * c < 0) (hbd : b * d < 0)
    (hcd : c * d < 0) : a * b < 0 := by
  have hprod := mul_pos_of_neg_of_neg hac hbd
  have hfactor : (a * c) * (b * d) = (a * b) * (c * d) := by ring
  rw [hfactor] at hprod
  by_contra hnot
  have hab : 0 ≤ a * b := le_of_not_gt hnot
  exact (not_le_of_gt hprod) (mul_nonpos_of_nonneg_of_nonpos hab hcd.le)

private theorem sign_change_of_left_opposite_right_same
    {a b c d : ℝ} (hac : a * c < 0) (hbd : 0 < b * d)
    (hcd : 0 < c * d) : a * b < 0 := by
  have hprod := mul_neg_of_neg_of_pos hac hbd
  have hfactor : (a * c) * (b * d) = (a * b) * (c * d) := by ring
  rw [hfactor] at hprod
  by_contra hnot
  have hab : 0 ≤ a * b := le_of_not_gt hnot
  exact (not_le_of_gt hprod) (mul_nonneg hab hcd.le)

private theorem sign_change_of_two_same_signs
    {a b c d : ℝ} (hac : 0 < a * c) (hbd : 0 < b * d)
    (hcd : c * d < 0) : a * b < 0 := by
  have hprod := mul_pos hac hbd
  have hfactor : (a * c) * (b * d) = (a * b) * (c * d) := by ring
  rw [hfactor] at hprod
  by_contra hnot
  have hab : 0 ≤ a * b := le_of_not_gt hnot
  exact (not_le_of_gt hprod) (mul_nonpos_of_nonneg_of_nonpos hab hcd.le)

private theorem derivative_eval_mul_neg_at_adjacent {F : ℝ[X]} {n : ℕ}
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (s : Finset ℝ) (hs : s = F.roots.toFinset) (hcard : s.card = n + 1)
    (i : Fin n) :
    F.derivative.eval (s.orderEmbOfFin hcard i.castSucc) *
      F.derivative.eval (s.orderEmbOfFin hcard i.succ) < 0 := by
  let r := s.orderEmbOfFin hcard
  have hri : r i.castSucc ∈ F.roots := by
    apply Multiset.mem_toFinset.mp
    rw [← hs]
    exact Finset.orderEmbOfFin_mem s hcard i.castSucc
  have hrj : r i.succ ∈ F.roots := by
    apply Multiset.mem_toFinset.mp
    rw [← hs]
    exact Finset.orderEmbOfFin_mem s hcard i.succ
  have hij : r i.castSucc < r i.succ := r.strictMono i.castSucc_lt_succ
  have hcount : F.roots.countP (fun z => r i.castSucc < z) =
      F.roots.countP (fun z => r i.succ < z) + 1 :=
    root_count_jump hnd hij hrj
      (no_root_between_adjacent s hs hcard i)
  have hderi := derivative_signed_at_simple_root hF hnd hF0 hri
  have hderj := derivative_signed_at_simple_root hF hnd hF0 hrj
  rw [hcount] at hderi
  exact signed_product_opposite F.leadingCoeff _ _ _
    (leadingCoeff_ne_zero.mpr hF0) hderi hderj

private theorem linear_eval_mul_neg_at_adjacent {F : ℝ[X]} {n : ℕ}
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hinside : ∀ z ∈ F.roots, -1 < z ∧ z < 1)
    (s : Finset ℝ) (hs : s = F.roots.toFinset) (hcard : s.card = n + 1)
    (a : ℝ) (i : Fin n) :
    (zigzagLinearFactor a F).eval (s.orderEmbOfFin hcard i.castSucc) *
      (zigzagLinearFactor a F).eval (s.orderEmbOfFin hcard i.succ) < 0 := by
  let r := s.orderEmbOfFin hcard
  have hri : r i.castSucc ∈ F.roots := by
    apply Multiset.mem_toFinset.mp
    rw [← hs]
    exact Finset.orderEmbOfFin_mem s hcard i.castSucc
  have hrj : r i.succ ∈ F.roots := by
    apply Multiset.mem_toFinset.mp
    rw [← hs]
    exact Finset.orderEmbOfFin_mem s hcard i.succ
  have hderprod : F.derivative.eval (r i.castSucc) *
      F.derivative.eval (r i.succ) < 0 :=
    derivative_eval_mul_neg_at_adjacent hF hF0 hnd s hs hcard i
  have hqi := sq_sub_one_neg_of_mem_Ioo (hinside _ hri)
  have hqj := sq_sub_one_neg_of_mem_Ioo (hinside _ hrj)
  have hqprod : 0 < ((r i.castSucc) ^ 2 - 1) * ((r i.succ) ^ 2 - 1) :=
    mul_pos_of_neg_of_neg hqi hqj
  change (zigzagLinearFactor a F).eval (r i.castSucc) *
    (zigzagLinearFactor a F).eval (r i.succ) < 0
  rw [zigzagLinearFactor_eval_root a _ F ((mem_roots hF0).mp hri),
    zigzagLinearFactor_eval_root a _ F ((mem_roots hF0).mp hrj)]
  have hneg := mul_neg_of_pos_of_neg hqprod hderprod
  nlinarith

private theorem linear_eval_mul_neg_at_left {F : ℝ[X]} {n : ℕ}
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hinside : ∀ z ∈ F.roots, -1 < z ∧ z < 1)
    (s : Finset ℝ) (hs : s = F.roots.toFinset) (hcard : s.card = n + 1)
    (a : ℝ) (ha : -3 < a) :
    (zigzagLinearFactor a F).eval (-1) *
      (zigzagLinearFactor a F).eval (s.orderEmbOfFin hcard 0) < 0 := by
  let r := s.orderEmbOfFin hcard
  have hr0 : r 0 ∈ F.roots := by
    apply Multiset.mem_toFinset.mp
    rw [← hs]
    exact Finset.orderEmbOfFin_mem s hcard 0
  have hleft : -1 < r 0 := (hinside _ hr0).1
  have hnomid : ∀ z ∈ F.roots, -1 < z → z < r 0 → False := by
    intro z hz _ hz0
    have hzmem : z ∈ s := hs ▸ Multiset.mem_toFinset.mpr hz
    have hzrange : z ∈ Set.range r := by
      rw [Finset.range_orderEmbOfFin s hcard]
      exact hzmem
    obtain ⟨k, rfl⟩ := hzrange
    exact (not_lt_of_ge (r.monotone (Fin.zero_le k))) hz0
  have hcount : F.roots.countP (fun z => -1 < z) =
      F.roots.countP (fun z => r 0 < z) + 1 :=
    root_count_jump hnd hleft hr0 hnomid
  have hnegmem : (-1 : ℝ) ∉ F.roots := by
    intro hz
    exact (lt_irrefl (-1 : ℝ)) (hinside _ hz).1
  have heval := eval_signed_away_from_roots hF hF0 hnegmem
  have hder := derivative_signed_at_simple_root hF hnd hF0 hr0
  rw [hcount] at heval
  have hFprod : F.eval (-1) * F.derivative.eval (r 0) < 0 :=
    signed_product_opposite F.leadingCoeff _ _ _
      (leadingCoeff_ne_zero.mpr hF0) heval hder
  have hfactor := sq_sub_one_neg_of_mem_Ioo (hinside _ hr0)
  have hcoef : -(3 + a) < 0 := by linarith
  have hcoefprod : 0 < (-(3 + a)) * ((r 0) ^ 2 - 1) :=
    mul_pos_of_neg_of_neg hcoef hfactor
  change (zigzagLinearFactor a F).eval (-1) *
    (zigzagLinearFactor a F).eval (r 0) < 0
  rw [zigzagLinearFactor_eval_neg_one,
    zigzagLinearFactor_eval_root a _ F ((mem_roots hF0).mp hr0)]
  have hneg := mul_neg_of_pos_of_neg hcoefprod hFprod
  nlinarith

private theorem linear_eval_mul_neg_at_right {F : ℝ[X]} {n : ℕ}
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hinside : ∀ z ∈ F.roots, -1 < z ∧ z < 1)
    (s : Finset ℝ) (hs : s = F.roots.toFinset) (hcard : s.card = n + 1)
    (a : ℝ) (ha : a < 3) :
    (zigzagLinearFactor a F).eval (s.orderEmbOfFin hcard (Fin.last n)) *
      (zigzagLinearFactor a F).eval 1 < 0 := by
  let r := s.orderEmbOfFin hcard
  have hrlast : r (Fin.last n) ∈ F.roots := by
    apply Multiset.mem_toFinset.mp
    rw [← hs]
    exact Finset.orderEmbOfFin_mem s hcard (Fin.last n)
  have hright : r (Fin.last n) < 1 := (hinside _ hrlast).2
  have hcountlast : F.roots.countP (fun z => r (Fin.last n) < z) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro z hz hlt
    have hzmem : z ∈ s := hs ▸ Multiset.mem_toFinset.mpr hz
    have hzrange : z ∈ Set.range r := by
      rw [Finset.range_orderEmbOfFin s hcard]
      exact hzmem
    obtain ⟨k, rfl⟩ := hzrange
    exact (not_lt_of_ge (r.monotone (Fin.le_last k))) hlt
  have hcountone : F.roots.countP (fun z => (1 : ℝ) < z) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro z hz hlt
    exact (not_lt_of_ge (hinside z hz).2.le) hlt
  have honemem : (1 : ℝ) ∉ F.roots := by
    intro hz
    exact (lt_irrefl (1 : ℝ)) (hinside _ hz).2
  have hder := derivative_signed_at_simple_root hF hnd hF0 hrlast
  have heval := eval_signed_away_from_roots hF hF0 honemem
  rw [hcountlast] at hder
  rw [hcountone] at heval
  have hFprod : 0 < F.derivative.eval (r (Fin.last n)) * F.eval 1 :=
    signed_product_same F.leadingCoeff _ _ 0
      (leadingCoeff_ne_zero.mpr hF0) hder heval
  have hfactor := sq_sub_one_neg_of_mem_Ioo (hinside _ hrlast)
  have hcoef : 0 < 3 - a := by linarith
  have hcoefprod : ((r (Fin.last n)) ^ 2 - 1) * (3 - a) < 0 :=
    mul_neg_of_neg_of_pos hfactor hcoef
  change (zigzagLinearFactor a F).eval (r (Fin.last n)) *
    (zigzagLinearFactor a F).eval 1 < 0
  rw [zigzagLinearFactor_eval_root a _ F ((mem_roots hF0).mp hrlast),
    zigzagLinearFactor_eval_one]
  have hneg := mul_neg_of_neg_of_pos hcoefprod hFprod
  nlinarith

/-- The finite-grid form of Appendix C.1's linear insertion criterion. The
output polynomial can be arbitrary: its signs at the old simple roots and
at the two endpoints determine one new simple root in every gap. -/
theorem splits_nodup_interval_of_root_derivative_signs {F H : ℝ[X]}
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hinside : ∀ z ∈ F.roots, -1 < z ∧ z < 1)
    (hdegree : H.natDegree = F.natDegree + 1)
    (hroot : ∀ z ∈ F.roots, H.eval z * F.derivative.eval z < 0)
    (hleft : H.eval (-1) * F.eval (-1) < 0)
    (hright : 0 < H.eval 1 * F.eval 1) :
    H.Splits ∧ H.roots.Nodup ∧ ∀ z ∈ H.roots, -1 < z ∧ z < 1 := by
  classical
  cases hFdegree : F.natDegree with
  | zero =>
    have hconstant : F = C (F.coeff 0) := eq_C_of_natDegree_eq_zero hFdegree
    have hFvalue : F.eval 1 ≠ 0 := by
      rw [hconstant] at hF0 ⊢
      simpa only [eval_C] using (C_ne_zero.mp hF0)
    have hfeq : F.eval (-1) = F.eval 1 := by rw [hconstant]; simp
    have hFprod : 0 < F.eval (-1) * F.eval 1 := by
      rw [hfeq]
      exact mul_self_pos.mpr hFvalue
    have hHsign : H.eval (-1) * H.eval 1 < 0 :=
      sign_change_of_left_opposite_right_same hleft hright hFprod
    let grid : Fin 2 → ℝ := Fin.cons (-1) (fun _ : Fin 1 => 1)
    have hgrid : StrictMono grid := by
      apply Fin.strictMono_cons.mpr
      constructor
      · intro j
        norm_num
      · intro i j hij
        have heq : i = j := Subsingleton.elim i j
        subst j
        exact (lt_irrefl i hij).elim
    have hsign : ∀ i : Fin 1,
        H.eval (grid i.castSucc) * H.eval (grid i.succ) < 0 := by
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      simpa [grid] using hHsign
    have hHdegree : H.natDegree ≤ 1 := by rw [hdegree, hFdegree]
    have hH0 : H ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero, hFdegree] at hdegree
      lia
    obtain ⟨_, hsplit, hnodup, hbounds⟩ :=
      splits_nodup_roots_of_strict_sign_changes hH0 hHdegree grid hgrid hsign
    refine ⟨hsplit, hnodup, ?_⟩
    intro z hz
    simpa [grid] using hbounds z hz
  | succ n =>
    let s : Finset ℝ := F.roots.toFinset
    have hs : s = F.roots.toFinset := rfl
    have hcard : s.card = n + 1 := by
      calc
        s.card = F.roots.card := Multiset.toFinset_card_of_nodup hnd
        _ = F.natDegree := splits_iff_card_roots.mp hF
        _ = n + 1 := hFdegree
    let r := s.orderEmbOfFin hcard
    have hrmem (i : Fin (n + 1)) : r i ∈ F.roots := by
      apply Multiset.mem_toFinset.mp
      rw [← hs]
      exact Finset.orderEmbOfFin_mem s hcard i
    let grid : Fin (n + 3) → ℝ := Fin.cons (-1) (Fin.snoc r 1)
    have hsnoc : StrictMono (Fin.snoc r 1) := by
      rw [← Fin.insertNth_last' 1 r]
      apply (Fin.strictMono_insertNth_iff (Fin.last (n + 1)) 1 r).mpr
      refine ⟨r.strictMono, ?_, ?_⟩
      · intro i _
        exact (hinside _ (hrmem i)).2
      · intro i hi
        exact (not_le_of_gt i.castSucc_lt_last hi).elim
    have hgrid : StrictMono grid := by
      apply Fin.strictMono_cons.mpr
      constructor
      · intro j
        cases j using Fin.lastCases with
        | last => norm_num [grid]
        | cast i => simpa [grid] using (hinside _ (hrmem i)).1
      · exact hsnoc
    let B := zigzagLinearFactor 0 F
    have hanchorRoot (i : Fin (n + 1)) :
        0 < H.eval (r i) * B.eval (r i) := by
      have hfi := hroot _ (hrmem i)
      have hq := sq_sub_one_neg_of_mem_Ioo (hinside _ (hrmem i))
      have hp := mul_pos_of_neg_of_neg hfi hq
      change 0 < H.eval (r i) * (zigzagLinearFactor 0 F).eval (r i)
      rw [zigzagLinearFactor_eval_root 0 _ F ((mem_roots hF0).mp (hrmem i))]
      nlinarith
    have hanchorLeft : 0 < H.eval (-1) * B.eval (-1) := by
      change 0 < H.eval (-1) * (zigzagLinearFactor 0 F).eval (-1)
      rw [zigzagLinearFactor_eval_neg_one]
      nlinarith [hleft]
    have hanchorRight : 0 < H.eval 1 * B.eval 1 := by
      change 0 < H.eval 1 * (zigzagLinearFactor 0 F).eval 1
      rw [zigzagLinearFactor_eval_one]
      nlinarith [hright]
    have hanchor (j : Fin (n + 3)) : 0 < H.eval (grid j) * B.eval (grid j) := by
      cases j using Fin.cases with
      | zero => simpa [grid] using hanchorLeft
      | succ j =>
        cases j using Fin.lastCases with
        | last => simpa [grid] using hanchorRight
        | cast i => simpa [grid] using hanchorRoot i
    have hBsign (i : Fin (n + 2)) :
        B.eval (grid i.castSucc) * B.eval (grid i.succ) < 0 := by
      cases i using Fin.lastCases with
      | last =>
        have hidx : (Fin.last (n + 1)).castSucc =
            (Fin.last n).castSucc.succ := by ext; rfl
        simpa [B, grid, hidx] using
          linear_eval_mul_neg_at_right hF hF0 hnd hinside s hs hcard 0 (by norm_num)
      | cast j =>
        cases j using Fin.cases with
        | zero =>
          simpa [B, grid] using
            linear_eval_mul_neg_at_left hF hF0 hnd hinside s hs hcard 0
              (by norm_num)
        | succ k =>
          have hidx1 : k.succ.castSucc.castSucc =
              k.castSucc.castSucc.succ := by ext; rfl
          rw [hidx1]
          simp only [grid, Fin.cons_succ, Fin.snoc_castSucc]
          exact linear_eval_mul_neg_at_adjacent hF hF0 hnd hinside s hs hcard 0 k
    have hsign (i : Fin (n + 2)) :
        H.eval (grid i.castSucc) * H.eval (grid i.succ) < 0 :=
      sign_change_of_two_same_signs (hanchor i.castSucc) (hanchor i.succ) (hBsign i)
    have hHdegree : H.natDegree ≤ n + 2 := by rw [hdegree, hFdegree]
    have hH0 : H ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero, hFdegree] at hdegree
      lia
    obtain ⟨_, hsplit, hnodup, hbounds⟩ :=
      splits_nodup_roots_of_strict_sign_changes hH0 hHdegree grid hgrid hsign
    refine ⟨hsplit, hnodup, ?_⟩
    intro z hz
    simpa [grid] using hbounds z hz

/-- A linear spectral factor raises degree exactly once. Appendix C.1. -/
theorem zigzagLinearFactor_natDegree (a : ℝ) (F : ℝ[X]) (hF : F ≠ 0) :
    (zigzagLinearFactor a F).natDegree = F.natDegree + 1 := by
  have hlow : (C a * F).natDegree < (zigzagOperator F).natDegree := by
    rw [zigzagOperator_natDegree F hF]
    exact lt_of_le_of_lt (natDegree_C_mul_le a F) (Nat.lt_succ_self _)
  exact (natDegree_sub_eq_left_of_natDegree_lt hlow).trans
    (zigzagOperator_natDegree F hF)

/-- The linear insertion of a nonzero polynomial cannot vanish. -/
theorem zigzagLinearFactor_ne_zero (a : ℝ) (F : ℝ[X]) (hF : F ≠ 0) :
    zigzagLinearFactor a F ≠ 0 := by
  intro hzero
  have hdeg := zigzagLinearFactor_natDegree a F hF
  rw [hzero, natDegree_zero] at hdeg
  lia

/-- A real spectral factor with parameter strictly between `-3` and `3`
inserts one simple root into each gap of an interval-simple input polynomial.
Appendix C.1. -/
theorem zigzagLinearFactor_roots (F : ℝ[X]) (a : ℝ)
    (hFsplit : F.Splits) (hFne0 : F ≠ 0) (hFnodup : F.roots.Nodup)
    (hinside : ∀ z ∈ F.roots, -1 < z ∧ z < 1)
    (haL : -3 < a) (haR : a < 3) :
    (zigzagLinearFactor a F).Splits ∧
      (zigzagLinearFactor a F).roots.Nodup ∧
      ∀ z ∈ (zigzagLinearFactor a F).roots, -1 < z ∧ z < 1 := by
  apply splits_nodup_interval_of_root_derivative_signs
    hFsplit hFne0 hFnodup hinside (zigzagLinearFactor_natDegree a F hFne0)
  · intro z hz
    have hderpos := derivative_signed_at_simple_root hFsplit hFnodup hFne0 hz
    have hder : F.derivative.eval z ≠ 0 := by
      intro hzero
      rw [hzero] at hderpos
      simp at hderpos
    have hfactor := sq_sub_one_neg_of_mem_Ioo (hinside z hz)
    rw [zigzagLinearFactor_eval_root a z F ((mem_roots hFne0).mp hz)]
    nlinarith [sq_pos_of_ne_zero hder]
  · have hnotroot : (-1 : ℝ) ∉ F.roots := by
      intro hz
      exact (lt_irrefl (-1 : ℝ)) (hinside _ hz).1
    have hFval : F.eval (-1) ≠ 0 := by
      intro hz
      exact hnotroot ((mem_roots hFne0).mpr hz)
    rw [zigzagLinearFactor_eval_neg_one]
    have hcoef : 0 < 3 + a := by linarith
    nlinarith [sq_pos_of_ne_zero hFval]
  · have hnotroot : (1 : ℝ) ∉ F.roots := by
      intro hz
      exact (lt_irrefl (1 : ℝ)) (hinside _ hz).2
    have hFval : F.eval 1 ≠ 0 := by
      intro hz
      exact hnotroot ((mem_roots hFne0).mpr hz)
    rw [zigzagLinearFactor_eval_one]
    have hcoef : 0 < 3 - a := by linarith
    nlinarith [sq_pos_of_ne_zero hFval]

end RealRooted.IntervalDifferential
