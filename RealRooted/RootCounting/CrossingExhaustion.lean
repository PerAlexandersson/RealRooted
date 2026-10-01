import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite crossing exhaustion

This file isolates the discrete equality case used in root-crossing arguments.
If a sequence of natural-valued chamber counts can drop by at most the
multiplicity of each successive crossing, then its total endpoint drop is at
most the total crossing multiplicity. When the reverse inequality is supplied
by an external crossing budget, every crossing must be an exact downward jump
of its full multiplicity.
-/

namespace RealRooted

/-- Counting multiplicities over the distinct elements satisfying a predicate
recovers the predicate count in the original multiset. -/
theorem sum_count_filter_toFinset_eq_countP
    {α : Type*} [DecidableEq α] (s : Multiset α) (p : α → Prop)
    [DecidablePred p] :
    ∑ a ∈ s.toFinset.filter p, s.count a = s.countP p := by
  rw [Multiset.countP_eq_card_filter,
    ← Multiset.toFinset_sum_count_eq (s.filter p)]
  refine Finset.sum_congr ?_ ?_
  · ext a
    simp
  · intro a ha
    rw [Multiset.count_filter_of_pos]
    exact (by simpa using ha : a ∈ s ∧ p a).2

/-- If all chamber-count drops are bounded by their crossing multiplicities,
and the endpoint drop exhausts the total multiplicity budget, then every
crossing is a downward jump of its full multiplicity. -/
theorem nat_crossing_exhaustion
    {K : ℕ} {N m : ℕ → ℕ} {D : ℕ}
    (hjump : ∀ i < K, N i ≤ N (i + 1) + m i)
    (hend : N 0 = N K + D)
    (hbudget : ∑ i ∈ Finset.range K, m i ≤ D) :
    ∀ i < K, N i = N (i + 1) + m i := by
  let e : ℕ → ℤ := fun i => (m i : ℤ) + N (i + 1) - N i
  have he_nonneg : ∀ i < K, 0 ≤ e i := by
    intro i hi
    have h := hjump i hi
    dsimp [e]
    lia
  have hsum_e :
      (∑ i ∈ Finset.range K, e i) =
        (∑ i ∈ Finset.range K, (m i : ℤ)) + N K - N 0 := by
    have htel :
        (∑ i ∈ Finset.range K, ((N (i + 1) : ℤ) - N i)) =
          N K - N 0 := by
      simpa using Finset.sum_range_sub (fun i => (N i : ℤ)) K
    calc
      (∑ i ∈ Finset.range K, e i) =
          (∑ i ∈ Finset.range K, (m i : ℤ)) +
            ∑ i ∈ Finset.range K, ((N (i + 1) : ℤ) - N i) := by
              simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
              ring
      _ = (∑ i ∈ Finset.range K, (m i : ℤ)) + N K - N 0 := by
        rw [htel]
        ring
  have hsum_m_le : (∑ i ∈ Finset.range K, (m i : ℤ)) ≤ D := by
    exact_mod_cast hbudget
  have hsum_e_nonneg : 0 ≤ ∑ i ∈ Finset.range K, e i :=
    Finset.sum_nonneg fun i hi => he_nonneg i (Finset.mem_range.mp hi)
  have hend_int : (N 0 : ℤ) = N K + D := by
    exact_mod_cast hend
  have hsum_e_zero : ∑ i ∈ Finset.range K, e i = 0 := by
    rw [hsum_e]
    lia
  have he_zero : ∀ i ∈ Finset.range K, e i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => he_nonneg i (Finset.mem_range.mp hi))).mp hsum_e_zero
  intro i hi
  have hz := he_zero i (Finset.mem_range.mpr hi)
  dsimp [e] at hz
  lia

end RealRooted
