import Mathlib.Data.Finset.Card

/-!
# Multiset cardinality and deduplication

Small cardinality criteria for a multiset to have no duplicate elements.
These statements are intended for upstreaming to Mathlib.
-/

namespace Multiset

/-- A multiset with no more elements than its underlying finset has no
duplicates. -/
theorem nodup_of_card_le_toFinset_card {α : Type*} [DecidableEq α]
    {m : Multiset α} (h : m.card ≤ m.toFinset.card) : m.Nodup := by
  have hle : m.dedup ≤ m := Multiset.dedup_le m
  have hcard : m.card ≤ m.dedup.card := by simpa only [Multiset.card_toFinset] using h
  have heq : m.dedup = m := Multiset.eq_of_le_of_card_le hle hcard
  rw [← heq]
  exact m.nodup_dedup

/-- A multiset containing every member of a sufficiently large finset has no
duplicates. -/
theorem nodup_of_finset_card_le {α : Type*}
    {m : Multiset α} {s : Finset α}
    (hsub : ∀ x ∈ s, x ∈ m) (hcard : m.card ≤ s.card) : m.Nodup := by
  classical
  refine nodup_of_card_le_toFinset_card (le_trans hcard ?_)
  exact Finset.card_le_card fun x hx => Multiset.mem_toFinset.mpr (hsub x hx)

end Multiset
