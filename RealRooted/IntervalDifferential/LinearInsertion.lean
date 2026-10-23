/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Degree
public import RealRooted.IntervalDifferential.Certificates
public import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Linear insertion into the centered differential operator

The real linear factor `L-a` from Appendix C raises degree by one. Its
evaluation at an old root is `(r²-1)F'(r)`, while its endpoint evaluations
are scalar multiples of those of `F`. These are the signs used in the
simple-root interval insertion argument.
-/

@[expose] public section

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
  have hfactor : s ^ 2 - 1 < 0 := by
    obtain ⟨hl, hr⟩ := hinside _ hs
    have hprod := mul_pos (show 0 < 1 - s by linarith)
      (show 0 < 1 + s by linarith)
    nlinarith
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
  have hij : r i.castSucc < r i.succ := r.strictMono i.castSucc_lt_succ
  have hcount : F.roots.countP (fun z => r i.castSucc < z) =
      F.roots.countP (fun z => r i.succ < z) + 1 :=
    root_count_jump hnd hij hrj
      (no_root_between_adjacent s hs hcard i)
  have hderi := derivative_signed_at_simple_root hF hnd hF0 hri
  have hderj := derivative_signed_at_simple_root hF hnd hF0 hrj
  rw [hcount] at hderi
  have hderprod : F.derivative.eval (r i.castSucc) *
      F.derivative.eval (r i.succ) < 0 :=
    signed_product_opposite F.leadingCoeff _ _ _
      (leadingCoeff_ne_zero.mpr hF0) hderi hderj
  have hqi : (r i.castSucc) ^ 2 - 1 < 0 := by
    obtain ⟨hl, hr⟩ := hinside _ hri
    have hprod := mul_pos (show 0 < 1 - r i.castSucc by linarith)
      (show 0 < 1 + r i.castSucc by linarith)
    nlinarith
  have hqj : (r i.succ) ^ 2 - 1 < 0 := by
    obtain ⟨hl, hr⟩ := hinside _ hrj
    have hprod := mul_pos (show 0 < 1 - r i.succ by linarith)
      (show 0 < 1 + r i.succ by linarith)
    nlinarith
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
  have hfactor : (r 0) ^ 2 - 1 < 0 := by
    obtain ⟨hl, hr⟩ := hinside _ hr0
    have hprod := mul_pos (show 0 < 1 - r 0 by linarith)
      (show 0 < 1 + r 0 by linarith)
    nlinarith
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
  have hfactor : (r (Fin.last n)) ^ 2 - 1 < 0 := by
    obtain ⟨hl, hr⟩ := hinside _ hrlast
    have hprod := mul_pos (show 0 < 1 - r (Fin.last n) by linarith)
      (show 0 < 1 + r (Fin.last n) by linarith)
    nlinarith
  have hcoef : 0 < 3 - a := by linarith
  have hcoefprod : ((r (Fin.last n)) ^ 2 - 1) * (3 - a) < 0 :=
    mul_neg_of_neg_of_pos hfactor hcoef
  change (zigzagLinearFactor a F).eval (r (Fin.last n)) *
    (zigzagLinearFactor a F).eval 1 < 0
  rw [zigzagLinearFactor_eval_root a _ F ((mem_roots hF0).mp hrlast),
    zigzagLinearFactor_eval_one]
  have hneg := mul_neg_of_neg_of_pos hcoefprod hFprod
  nlinarith

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

end RealRooted.IntervalDifferential
