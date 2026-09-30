import RealRooted.LiuOppositeSigns.RootCount
import RealRooted.Mathlib.Data.Multiset.Rel
import RealRooted.RootMultiplicityMatching

/-!
# Root-count stability under close multiset matchings

These lemmas provide the local closedness input for the limiting step in Liu's
opposite-leading-sign theorem.  They compare root counts only at thresholds
separated from the original roots and compare the selected largest roots.
-/

namespace RealRooted

open LiuOppositeSigns Polynomial

/-- Largest roots of closely matched nonzero polynomials are close. -/
theorem IsLargestRoot.abs_sub_lt_of_roots_rel
    {p q : ℝ[X]} {r s δ : ℝ} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hr : IsLargestRoot p r) (hs : IsLargestRoot q s)
    (hmatch : Multiset.Rel (fun a b ↦ |b - a| < δ) p.roots q.roots) :
    |s - r| < δ := by
  have hr_mem : r ∈ p.roots := (Polynomial.mem_roots hp_ne).mpr hr.isRoot
  have hs_mem : s ∈ q.roots := (Polynomial.mem_roots hq_ne).mpr hs.isRoot
  obtain ⟨b, hb_mem, hrb⟩ :=
    Multiset.exists_mem_of_rel_of_mem hmatch hr_mem
  obtain ⟨a, ha_mem, has⟩ := by
    simpa only [Function.flip_def] using
      Multiset.exists_mem_of_rel_of_mem ((Multiset.rel_flip).2 hmatch) hs_mem
  have hb_le : b ≤ s := hs.roots_le b hb_mem
  have ha_le : a ≤ r := hr.roots_le a ha_mem
  rw [abs_lt]
  constructor
  · linarith [(abs_lt.mp hrb).1]
  · linarith [(abs_lt.mp has).2]

end RealRooted
