import RealRooted.Basic

/-!
# Liu x-subtraction splitting tools

This module contains reusable low-degree root-list splitting helpers used by
the normalized x-subtraction endpoint leaves.
-/

open Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- A nonzero polynomial splits once a nodup list of roots is at least as long
as its natural degree.  This local helper packages the repeated
root-count-to-splitting argument used in low-degree endpoint leaves. -/
lemma splits_of_roots_list_of_natDegree_le {p : ℝ[X]} {rs : List ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ rs.length)
    (hnd : rs.Nodup) (hroot : ∀ r ∈ rs, p.IsRoot r) :
    p.Splits := by
  have hsub : (↑rs : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)]
    intro r hr
    exact (mem_roots hp_ne).mpr (hroot r (Multiset.mem_coe.mp hr))
  apply splits_of_card_roots
  apply le_antisymm
  · exact card_roots' p
  · calc
      p.natDegree ≤ rs.length := hdeg
      _ = (↑rs : Multiset ℝ).card := (Multiset.coe_card rs).symm
      _ ≤ p.roots.card := Multiset.card_le_card hsub

/-- A nonzero polynomial of degree at most three splits when it has three
ordered real roots. -/
lemma splits_of_three_ordered_roots_of_natDegree_le {p : ℝ[X]} {a b c : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 3) (hab : a < b) (hbc : b < c)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hc : p.IsRoot c) :
    p.Splits := by
  have hac : a < c := lt_trans hab hbc
  exact splits_of_roots_list_of_natDegree_le (rs := [a, b, c]) hp_ne
    (by simpa using hdeg)
    (by simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt hbc])
    (by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc)

/-- A nonzero polynomial of degree at most four splits when it has four ordered
real roots. -/
lemma splits_of_four_ordered_roots_of_natDegree_le {p : ℝ[X]} {a b c d : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 4) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (ha : p.IsRoot a) (hb : p.IsRoot b) (hc : p.IsRoot c)
    (hd : p.IsRoot d) :
    p.Splits := by
  have hac : a < c := lt_trans hab hbc
  have had : a < d := lt_trans hac hcd
  have hbd : b < d := lt_trans hbc hcd
  exact splits_of_roots_list_of_natDegree_le (rs := [a, b, c, d]) hp_ne
    (by simpa using hdeg)
    (by
      simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt had, ne_of_lt hbc,
        ne_of_lt hbd, ne_of_lt hcd])
    (by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hd)

/-- A nonzero polynomial of degree at most five splits when it has five ordered
real roots. -/
lemma splits_of_five_ordered_roots_of_natDegree_le {p : ℝ[X]} {a b c d e : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 5) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e) (ha : p.IsRoot a) (hb : p.IsRoot b)
    (hc : p.IsRoot c) (hd : p.IsRoot d) (he : p.IsRoot e) :
    p.Splits := by
  have hac : a < c := lt_trans hab hbc
  have had : a < d := lt_trans hac hcd
  have hae : a < e := lt_trans had hde
  have hbd : b < d := lt_trans hbc hcd
  have hbe : b < e := lt_trans hbd hde
  have hce : c < e := lt_trans hcd hde
  exact splits_of_roots_list_of_natDegree_le (rs := [a, b, c, d, e]) hp_ne
    (by simpa using hdeg)
    (by
      simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt had, ne_of_lt hae,
        ne_of_lt hbc, ne_of_lt hbd, ne_of_lt hbe, ne_of_lt hcd,
        ne_of_lt hce, ne_of_lt hde])
    (by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hd
      · exact he)

end LiuOppositeSigns
end RealRooted
