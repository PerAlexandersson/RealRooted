import RealRooted.LiuOppositeSigns
import RealRooted.Mathlib.Data.Multiset.Rel
import RealRooted.RootMultiplicityMatching

/-!
# Root-count stability under close multiset matchings

These lemmas provide the local closedness input for the limiting step in Liu's
opposite-leading-sign theorem.  They compare root counts only at thresholds
separated from the original roots and compare the selected largest roots.
-/

namespace RealRooted

open Polynomial

/-- A close root matching preserves the root count at a separated threshold. -/
theorem rootCountAtOrAbove_eq_of_roots_rel_abs_sub_lt
    {p q : ℝ[X]} {x δ : ℝ}
    (hsep : ∀ r ∈ p.roots, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r s ↦ |s - r| < δ) p.roots q.roots) :
    rootCountAtOrAbove p x = rootCountAtOrAbove q x := by
  unfold rootCountAtOrAbove
  apply Multiset.Rel.card_filter_eq hmatch (fun r => x ≤ r) (fun s => x ≤ s)
  intro r hr s hs hrs
  have habs := abs_lt.mp hrs
  constructor
  · intro hxr
    have hrx : δ ≤ r - x := by
      simpa [abs_of_nonneg (sub_nonneg.mpr hxr)] using hsep r hr
    linarith [habs.1]
  · intro hxs
    by_contra hxr
    have hrx : δ ≤ x - r := by
      have hrx' : r ≤ x := le_of_lt (lt_of_not_ge hxr)
      simpa [abs_of_nonpos (sub_nonpos.mpr hrx')] using hsep r hr
    linarith [habs.2]

/-- Largest roots of closely matched nonzero polynomials are close. -/
theorem IsLargestRoot.abs_sub_lt_of_roots_rel
    {p q : ℝ[X]} {r s δ : ℝ} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hr : IsLargestRoot p r) (hs : IsLargestRoot q s)
    (hmatch : Multiset.Rel (fun a b ↦ |b - a| < δ) p.roots q.roots) :
    |s - r| < δ := by
  have hr_mem : r ∈ p.roots := (Polynomial.mem_roots hp_ne).mpr hr.isRoot
  have hs_mem : s ∈ q.roots := (Polynomial.mem_roots hq_ne).mpr hs.isRoot
  obtain ⟨b, hb_mem, hrb⟩ := hmatch.exists_right_of_mem_left hr_mem
  obtain ⟨a, ha_mem, has⟩ :=
    Multiset.Rel.exists_left_of_mem_right hmatch hs_mem
  have hb_le : b ≤ s := hs.roots_le b hb_mem
  have ha_le : a ≤ r := hr.roots_le a ha_mem
  rw [abs_lt]
  constructor
  · linarith [(abs_lt.mp hrb).1]
  · linarith [(abs_lt.mp has).2]

end RealRooted
