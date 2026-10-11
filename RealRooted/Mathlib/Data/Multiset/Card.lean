import Mathlib.Data.Finset.Card

/-!
# Multiset cardinality and deduplication

Small cardinality criteria for a multiset to have no duplicate elements.
These statements are intended for upstreaming to Mathlib.
-/

namespace Multiset

/-- A multiset containing every member of a sufficiently large finset has no
duplicates. -/
theorem nodup_of_finset_card_le {α : Type*}
    {m : Multiset α} {s : Finset α}
    (hsub : ∀ x ∈ s, x ∈ m) (hcard : m.card ≤ s.card) : m.Nodup := by
  classical
  apply (Multiset.nodup_iff_le_length_dedup m).mpr
  exact le_trans hcard (by
    simpa only [Multiset.card_toFinset] using
      Finset.card_le_card fun x hx => Multiset.mem_toFinset.mpr (hsub x hx))

end Multiset
