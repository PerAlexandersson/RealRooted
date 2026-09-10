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

end StrictMono
