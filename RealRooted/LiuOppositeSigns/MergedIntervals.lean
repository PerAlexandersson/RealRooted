import RealRooted.LiuOppositeSigns
import RealRooted.RootContinuity

/-!
# Liu merged-root interval support

This module contains the lightweight interval bookkeeping used for the
paper-route proof of Liu's opposite-leading-sign theorem.  The key point is to
avoid a separate merged-root datatype at first: a finite complementary interval
can be represented by two real endpoints together with the assertion that
neither endpoint polynomial has a root in the open interval.
-/

open Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- The signed strict-upper root-count difference is independent of the sample
point chosen inside a root-free finite interval. -/
theorem intCard_roots_gt_sub_eq_of_no_isRoot_Ioo
    {f g : ℝ[X]} {a b x y : ℝ}
    (hf : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card =
      ((f.roots.filter (y < ·)).card : ℤ) - (g.roots.filter (y < ·)).card := by
  by_cases hxy : x ≤ y
  · exact
      card_roots_filter_gt_sub_eq_of_no_isRoot_Icc hxy
        (fun z hxz hzy => hf z (lt_of_lt_of_le hax hxz) (lt_of_le_of_lt hzy hyb))
        (fun z hxz hzy => hg z (lt_of_lt_of_le hax hxz) (lt_of_le_of_lt hzy hyb))
  · have hyx : y ≤ x := le_of_not_ge hxy
    exact
      (card_roots_filter_gt_sub_eq_of_no_isRoot_Icc hyx
        (fun z hyz hzx => hf z (lt_of_lt_of_le hay hyz) (lt_of_le_of_lt hzx hxb))
        (fun z hyz hzx => hg z (lt_of_lt_of_le hay hyz) (lt_of_le_of_lt hzx hxb))).symm

/-- Oddness of the signed strict-upper root-count difference is independent of
the sample point chosen inside a root-free finite interval. -/
theorem odd_intCard_roots_gt_sub_iff_of_no_isRoot_Ioo
    {f g : ℝ[X]} {a b x y : ℝ}
    (hf : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      Odd (((f.roots.filter (y < ·)).card : ℤ) -
        (g.roots.filter (y < ·)).card)) := by
  rw [intCard_roots_gt_sub_eq_of_no_isRoot_Ioo hf hg hax hxb hay hyb]

end LiuOppositeSigns
end RealRooted
