import RealRooted.Mathlib.Data.Multiset.Rel

/-!
# Sorted root matching

An arbitrary close perfect matching of two real multisets can be uncrossed into
a close pointwise matching of their ascending sorts.  This is the finite
ordered-root input for limiting interlacing and root-count inequalities.
-/

namespace RealRooted

/-- A close multiset matching pairs corresponding ascending order statistics. -/
theorem forall₂_sort_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {ρ : ℝ}
    (hrel : Multiset.Rel (fun x y : ℝ => |y - x| < ρ) s t) :
    List.Forall₂ (fun x y : ℝ => |y - x| < ρ)
      (s.sort (· ≤ ·)) (t.sort (· ≤ ·)) := by
  apply Multiset.Rel.forall₂_sort
  · intro a c b d hac hbd had hcb
    rw [abs_lt] at had hcb ⊢
    constructor <;> constructor <;> linarith
  · exact hrel

end RealRooted
