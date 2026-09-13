import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weighted finite sums with a unique successful index

This file records a coefficient-type-generic double-counting lemma for a
finite family in which every object has a unique successful index.
-/

namespace Finset

variable {α ι M : Type*} [AddCommMonoid M]

/-- If each member of `objects` has a unique successful index in `indices`
and every successful-index fiber has the same weighted sum, then the total
weight is the cardinality of `indices` times that common fiber sum. -/
theorem sum_eq_card_nsmul_of_existsUnique_mem_and_filter_sum
    (objects : Finset α) (indices : Finset ι) (success : ι → α → Prop)
    [DecidableRel success]
    (weight : α → M) (fiberSum : M)
    (hunique : ∀ a ∈ objects, ∃! i, i ∈ indices ∧ success i a)
    (hfiber : ∀ i ∈ indices,
      ∑ a ∈ objects.filter (success i), weight a = fiberSum) :
    ∑ a ∈ objects, weight a = indices.card • fiberSum := by
  classical
  have hone (a : α) (ha : a ∈ objects) :
      (∑ i ∈ indices, if success i a then weight a else 0) = weight a := by
    obtain ⟨i, hi, hunique⟩ := hunique a ha
    rw [Finset.sum_eq_single i]
    · simp [hi.2]
    · intro j hj hji
      have hn : ¬success j a := by
        intro hsuccess
        exact hji (hunique j ⟨hj, hsuccess⟩)
      simp [hn]
    · intro hi'
      exact (hi' hi.1).elim
  calc
    (∑ a ∈ objects, weight a) =
        ∑ a ∈ objects, ∑ i ∈ indices,
          if success i a then weight a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hone a ha).symm
    _ = ∑ i ∈ indices, ∑ a ∈ objects,
        if success i a then weight a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ indices, fiberSum := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      exact hfiber i hi
    _ = indices.card • fiberSum := by
      simp

end Finset
