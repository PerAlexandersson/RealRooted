import RealRooted.Basic
import RealRooted.MaWang

/-!
# Liu x-subtraction splitting tools

This module contains reusable low-degree root-list splitting helpers used by
the normalized x-subtraction endpoint leaves.
-/

open Polynomial Filter

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

/-- A nonzero cubic splits if two separated sign-changing intervals give two
real roots and a nonpositive value to their right plus divergence to `+∞` gives
the third root. -/
lemma splits_of_two_sign_change_intervals_and_right_tail {p : ℝ[X]}
    {x₁ x₂ y₁ y₂ z : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 3)
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hxy : x₂ ≤ y₁) (hyz : y₂ ≤ z)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hz : p.eval z ≤ 0)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits := by
  obtain ⟨r₁, hx₁_r₁, hr₁_x₂, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hx hsx
  obtain ⟨r₂, hy₁_r₂, hr₂_y₂, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hy hsy
  obtain ⟨r₃, hr₃_ge, hr₃_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hz htop
  have h12 : r₁ < r₂ := lt_trans (lt_of_lt_of_le hr₁_x₂ hxy) hy₁_r₂
  have h23 : r₂ < r₃ := lt_of_lt_of_le (lt_of_lt_of_le hr₂_y₂ hyz) hr₃_ge
  exact splits_of_three_ordered_roots_of_natDegree_le
    hp_ne hdeg h12 h23 hr₁_root hr₂_root hr₃_root

/-- A quartic splits if three weakly ordered sign-changing intervals give three
real roots, and a negative value at zero plus divergence to `+∞` gives the
fourth root to the right of zero.  The weak separation permits adjacent
intervals, which is useful for repeated-root boundary cases. -/
lemma splits_of_three_sign_change_intervals_and_right_tail_of_le {p : ℝ[X]}
    {x₁ x₂ y₁ y₂ z₁ z₂ : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 4)
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂)
    (hxy : x₂ ≤ y₁) (hyz : y₂ ≤ z₁) (hz0 : z₂ ≤ 0)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hsz : p.eval z₁ * p.eval z₂ < 0)
    (h0 : p.eval 0 < 0)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits := by
  obtain ⟨r₁, hx₁_r₁, hr₁_x₂, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hx hsx
  obtain ⟨r₂, hy₁_r₂, hr₂_y₂, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hy hsy
  obtain ⟨r₃, hz₁_r₃, hr₃_z₂, hr₃_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hz hsz
  obtain ⟨r₄, hr₄_ge, hr₄_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt h0) htop
  have h12 : r₁ < r₂ := lt_trans (lt_of_lt_of_le hr₁_x₂ hxy) hy₁_r₂
  have h23 : r₂ < r₃ := lt_trans (lt_of_lt_of_le hr₂_y₂ hyz) hz₁_r₃
  have h34 : r₃ < r₄ := lt_of_lt_of_le (lt_of_lt_of_le hr₃_z₂ hz0) hr₄_ge
  exact splits_of_four_ordered_roots_of_natDegree_le
    hp_ne hdeg h12 h23 h34 hr₁_root hr₂_root hr₃_root hr₄_root

/-- A quartic splits if three strictly ordered sign-changing intervals give
three real roots, and a negative value at zero plus divergence to `+∞` gives the
fourth root to the right of zero. -/
lemma splits_of_three_sign_change_intervals_and_right_tail {p : ℝ[X]}
    {x₁ x₂ y₁ y₂ z₁ z₂ : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 4)
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂)
    (hxy : x₂ < y₁) (hyz : y₂ < z₁) (hz0 : z₂ ≤ 0)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hsz : p.eval z₁ * p.eval z₂ < 0)
    (h0 : p.eval 0 < 0)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits :=
  splits_of_three_sign_change_intervals_and_right_tail_of_le
    hp_ne hdeg hx hy hz (le_of_lt hxy) (le_of_lt hyz) hz0
    hsx hsy hsz h0 htop

/-- A quartic splits if two weakly separated sign-changing intervals sit
between a left-tail value and a right-tail value. -/
lemma splits_of_two_sign_change_intervals_and_both_tails_of_le {p : ℝ[X]}
    {l x₁ x₂ y₁ y₂ r : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 4)
    (hlx : l ≤ x₁) (hx : x₁ < x₂) (hy : y₁ < y₂)
    (hxy : x₂ ≤ y₁) (hyr : y₂ ≤ r)
    (hl_eval : p.eval l ≤ 0)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hr_eval : p.eval r ≤ 0)
    (hbot : Tendsto (fun x => p.eval x) atBot atTop)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits := by
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop hl_eval hbot
  obtain ⟨r₁, hx₁_r₁, hr₁_x₂, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hx hsx
  obtain ⟨r₂, hy₁_r₂, hr₂_y₂, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hy hsy
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hr_eval htop
  have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans hlx) hx₁_r₁
  have h12 : r₁ < r₂ := lt_trans (lt_of_lt_of_le hr₁_x₂ hxy) hy₁_r₂
  have h2R : r₂ < rR := lt_of_lt_of_le (lt_of_lt_of_le hr₂_y₂ hyr) hrR_ge
  exact splits_of_four_ordered_roots_of_natDegree_le
    hp_ne hdeg hL1 h12 h2R hrL_root hr₁_root hr₂_root hrR_root

/-- A quintic splits if four weakly separated sign-changing intervals give
four real roots, and a nonpositive value to their right plus divergence to
`+∞` gives the fifth root. -/
lemma splits_of_four_sign_change_intervals_and_right_tail_of_le {p : ℝ[X]}
    {x₁ x₂ y₁ y₂ z₁ z₂ t₁ t₂ r : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 5)
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂) (ht : t₁ < t₂)
    (hxy : x₂ ≤ y₁) (hyz : y₂ ≤ z₁) (hzt : z₂ ≤ t₁) (htr : t₂ ≤ r)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hsz : p.eval z₁ * p.eval z₂ < 0)
    (hst : p.eval t₁ * p.eval t₂ < 0)
    (hr_eval : p.eval r ≤ 0)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits := by
  obtain ⟨r₁, hx₁_r₁, hr₁_x₂, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hx hsx
  obtain ⟨r₂, hy₁_r₂, hr₂_y₂, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hy hsy
  obtain ⟨r₃, hz₁_r₃, hr₃_z₂, hr₃_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hz hsz
  obtain ⟨r₄, ht₁_r₄, hr₄_t₂, hr₄_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg ht hst
  obtain ⟨r₅, hr₅_ge, hr₅_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hr_eval htop
  have h12 : r₁ < r₂ := lt_trans (lt_of_lt_of_le hr₁_x₂ hxy) hy₁_r₂
  have h23 : r₂ < r₃ := lt_trans (lt_of_lt_of_le hr₂_y₂ hyz) hz₁_r₃
  have h34 : r₃ < r₄ := lt_trans (lt_of_lt_of_le hr₃_z₂ hzt) ht₁_r₄
  have h45 : r₄ < r₅ := lt_of_lt_of_le (lt_of_lt_of_le hr₄_t₂ htr) hr₅_ge
  exact splits_of_five_ordered_roots_of_natDegree_le
    hp_ne hdeg h12 h23 h34 h45 hr₁_root hr₂_root hr₃_root hr₄_root hr₅_root

/-- A quintic splits if four strictly separated sign-changing intervals give
four real roots, and a nonpositive value to their right plus divergence to
`+∞` gives the fifth root. -/
lemma splits_of_four_sign_change_intervals_and_right_tail {p : ℝ[X]}
    {x₁ x₂ y₁ y₂ z₁ z₂ t₁ t₂ r : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 5)
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂) (ht : t₁ < t₂)
    (hxy : x₂ < y₁) (hyz : y₂ < z₁) (hzt : z₂ < t₁) (htr : t₂ ≤ r)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hsz : p.eval z₁ * p.eval z₂ < 0)
    (hst : p.eval t₁ * p.eval t₂ < 0)
    (hr_eval : p.eval r ≤ 0)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits :=
  splits_of_four_sign_change_intervals_and_right_tail_of_le
    hp_ne hdeg hx hy hz ht (le_of_lt hxy) (le_of_lt hyz) (le_of_lt hzt)
    htr hsx hsy hsz hst hr_eval htop

/-- A quintic splits if three weakly separated sign-changing intervals sit
between a left-tail value and a right-tail value. -/
lemma splits_of_three_sign_change_intervals_and_both_tails_of_le {p : ℝ[X]}
    {l x₁ x₂ y₁ y₂ z₁ z₂ r : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 5)
    (hlx : l ≤ x₁) (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂)
    (hxy : x₂ ≤ y₁) (hyz : y₂ ≤ z₁) (hzr : z₂ ≤ r)
    (hl_eval : 0 ≤ p.eval l)
    (hsx : p.eval x₁ * p.eval x₂ < 0)
    (hsy : p.eval y₁ * p.eval y₂ < 0)
    (hsz : p.eval z₁ * p.eval z₂ < 0)
    (hr_eval : p.eval r ≤ 0)
    (hbot : Tendsto (fun x => p.eval x) atBot atBot)
    (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits := by
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot hl_eval hbot
  obtain ⟨r₁, hx₁_r₁, hr₁_x₂, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hx hsx
  obtain ⟨r₂, hy₁_r₂, hr₂_y₂, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hy hsy
  obtain ⟨r₃, hz₁_r₃, hr₃_z₂, hr₃_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hz hsz
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hr_eval htop
  have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans hlx) hx₁_r₁
  have h12 : r₁ < r₂ := lt_trans (lt_of_lt_of_le hr₁_x₂ hxy) hy₁_r₂
  have h23 : r₂ < r₃ := lt_trans (lt_of_lt_of_le hr₂_y₂ hyz) hz₁_r₃
  have h3R : r₃ < rR := lt_of_lt_of_le (lt_of_lt_of_le hr₃_z₂ hzr) hrR_ge
  exact splits_of_five_ordered_roots_of_natDegree_le
    hp_ne hdeg hL1 h12 h23 h3R hrL_root hr₁_root hr₂_root hr₃_root hrR_root

end LiuOppositeSigns
end RealRooted
