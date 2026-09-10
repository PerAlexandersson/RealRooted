module

public import Mathlib.Order.Fin.Tuple

/-!
# Ordered finite tuples

Upstream-shaped lemmas for inserting an entry into a strictly ordered finite tuple.
-/

public section

namespace StrictMono

/-- Inserting an entry between its lower and upper tuple bounds preserves strict
monotonicity. -/
theorem insertNth_of_bounds
    {α : Type*} [Preorder α] {n : ℕ} {f : Fin n → α} (hf : StrictMono f)
    {p : Fin (n + 1)} {x : α}
    (hbefore : ∀ i : Fin n, i.castSucc < p → f i < x)
    (hafter : ∀ i : Fin n, p ≤ i.castSucc → x < f i) :
    StrictMono (Fin.insertNth p x f) := by
  intro i j hij
  revert j
  refine Fin.succAboveCases p ?_ (fun i => ?_) i
  · intro j hij
    revert hij
    refine Fin.succAboveCases p ?_ (fun j => ?_) j
    · intro hij
      exact (lt_irrefl _ hij).elim
    · intro hij
      simpa using hafter j ((Fin.lt_succAbove_iff_le_castSucc p j).mp hij)
  · intro j hij
    revert hij
    refine Fin.succAboveCases p ?_ (fun j => ?_) j
    · intro hij
      simpa using hbefore i ((Fin.succAbove_lt_iff_castSucc_lt p i).mp hij)
    · intro hij
      simpa using hf (Fin.succAbove_lt_succAbove_iff.mp hij)

/-- Inserting a missing interior value into a strictly ordered finite tuple produces an
ordered larger tuple whose deletion recovers the original tuple. -/
theorem exists_ordered_interior_insert
    {α : Type*} [LinearOrder α] {q : ℕ} {cols : Fin (q + 2) → α}
    (hcols : StrictMono cols) {b : α} (hb : b ∉ Set.range cols)
    (hleft : cols 0 < b) (hright : b < cols (Fin.last (q + 1))) :
    ∃ (u : Fin (q + 3) → α) (r : Fin (q + 1)),
      StrictMono u ∧ u r.castSucc.succ = b ∧
        u ∘ r.castSucc.succ.succAbove = cols := by
  classical
  let t : Fin (q + 2) := Fin.find (fun i => b < cols i) ⟨Fin.last (q + 1), hright⟩
  have ht : b < cols t := by
    exact Fin.find_spec (p := fun i => b < cols i) _
  have ht_ne_zero : t ≠ 0 := by
    intro h
    exact (lt_asymm hleft) (by simpa [h] using ht)
  obtain ⟨r, hr⟩ := Fin.eq_succ_of_ne_zero ht_ne_zero
  let p : Fin (q + 3) := t.castSucc
  let u : Fin (q + 3) → α := Fin.insertNth p b cols
  have hbefore : ∀ i : Fin (q + 2), i.castSucc < p → cols i < b := by
    intro i hit
    have hnot : ¬ b < cols i := by
      apply Fin.find_min (p := fun i => b < cols i) _
      exact Fin.castSucc_lt_castSucc_iff.mp hit
    exact lt_of_le_of_ne (not_lt.mp hnot) (by
      intro h
      exact hb ⟨i, h⟩)
  have hafter : ∀ i : Fin (q + 2), p ≤ i.castSucc → b < cols i := by
    intro i hti
    apply ht.trans_le
    apply hcols.monotone
    exact Fin.castSucc_le_castSucc_iff.mp hti
  refine ⟨u, r, ?_, ?_, ?_⟩
  · exact insertNth_of_bounds hcols hbefore hafter
  · subst t
    simp [u, p, hr]
  · subst t
    simp [u, p, hr]

/-- A strictly ordered finite tuple either has consecutive values throughout or omits an
ambient value strictly between its endpoints. -/
theorem consecutive_or_exists_missing_between
    {q N : Nat} {cols : Fin (q + 2) → Fin N} (hcols : StrictMono cols) :
    (∀ j, (cols j).val = (cols 0).val + j.val) ∨
    ∃ b : Fin N, cols 0 < b ∧ b < cols (Fin.last (q + 1)) ∧
      b ∉ Set.range cols := by
  by_cases hcon : ∀ i : Fin (q + 1),
    (cols i.succ).val = (cols i.castSucc).val + 1
  · left
    intro j
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
      calc
        (cols j.succ).val = (cols j.castSucc).val + 1 := hcon j
        _ = ((cols 0).val + j.castSucc.val) + 1 := by rw [ih]
        _ = (cols 0).val + j.succ.val := by simp [Nat.add_assoc]
  · right
    push Not at hcon
    obtain ⟨i, hi⟩ := hcon
    have hstep : (cols i.castSucc).val + 1 ≤ (cols i.succ).val := by
      exact Nat.succ_le_iff.mpr (Fin.lt_def.mp (hcols i.castSucc_lt_succ))
    have hgap : (cols i.castSucc).val + 1 < (cols i.succ).val := by
      exact lt_of_le_of_ne hstep (Ne.symm hi)
    let b : Fin N := ⟨(cols i.castSucc).val + 1, lt_trans hgap (cols i.succ).isLt⟩
    have hleft : cols 0 < b := by
      change (cols 0).val < (cols i.castSucc).val + 1
      have hle := hcols.monotone (Fin.zero_le i.castSucc)
      exact lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hle) (by lia)
    have hright : b < cols (Fin.last (q + 1)) := by
      change (cols i.castSucc).val + 1 < (cols (Fin.last (q + 1))).val
      exact hgap.trans_le
        (Fin.le_iff_val_le_val.mp (hcols.monotone (Fin.le_last i.succ)))
    refine ⟨b, hleft, hright, ?_⟩
    rintro ⟨j, hj⟩
    have hval : (cols j).val = (cols i.castSucc).val + 1 := by
      simpa [b] using congrArg Fin.val hj
    by_cases hji : j.val ≤ i.val
    · have hle : j ≤ i.castSucc := Fin.le_iff_val_le_val.mpr hji
      have hcolsle := hcols.monotone hle
      have hcolsle_val := Fin.le_iff_val_le_val.mp hcolsle
      rw [hval] at hcolsle_val
      lia
    · have hji : i.val + 1 ≤ j.val := by lia
      have hle : i.succ ≤ j := Fin.le_iff_val_le_val.mpr hji
      have hcolsle := hcols.monotone hle
      have hcolsle_val := Fin.le_iff_val_le_val.mp hcolsle
      rw [hval] at hcolsle_val
      lia

/-- Removing the last entry of a strictly ordered tuple strictly decreases its value span. -/
theorem span_castSucc_last_lt
    {q N : Nat} {u : Fin (q + 3) → Fin N} (hu : StrictMono u) :
    (u ((Fin.last (q + 1)).castSucc)).val - (u 0).val <
      (u (Fin.last (q + 2))).val - (u 0).val := by
  have hlast : (Fin.last (q + 1)).castSucc < Fin.last (q + 2) :=
    Fin.castSucc_lt_last _
  have hlt := hu hlast
  have hle := hu.monotone (Fin.zero_le ((Fin.last (q + 1)).castSucc))
  exact Nat.sub_lt_sub_right (Fin.le_iff_val_le_val.mp hle) (Fin.lt_def.mp hlt)

/-- Removing the first entry of a strictly ordered tuple strictly decreases its value span. -/
theorem span_succ_zero_lt
    {q N : Nat} {u : Fin (q + 3) → Fin N} (hu : StrictMono u) :
    (u (Fin.last (q + 2))).val - (u ((0 : Fin (q + 2)).succ)).val <
      (u (Fin.last (q + 2))).val - (u 0).val := by
  have hzero : (0 : Fin (q + 3)) < (0 : Fin (q + 2)).succ := by
    change 0 < 1
    exact Nat.zero_lt_one
  have hlt := hu hzero
  have hle := hu.monotone (Fin.le_last ((0 : Fin (q + 2)).succ))
  exact Nat.sub_lt_sub_left
    ((Fin.lt_def.mp hlt).trans_le (Fin.le_iff_val_le_val.mp hle)) (Fin.lt_def.mp hlt)

end StrictMono
