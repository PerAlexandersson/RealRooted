import RealRooted.CommonInterleaverTwo

/-!
# Endpoint-Sign Lower Root Counts

This file contains the direct issue #42 endpoint-sign bridge from same-sign
endpoint evaluations to the succ-degree lower root-count equality.
-/

open Polynomial

namespace RealRooted

/-- Endpoint-sign lower root-count bridge for issue #42.

For a positive-leading succ-degree pair `f ≪ g`, if `x` is a common non-root
and the endpoint product `f.eval x * g.eval x` is positive, then the number of
roots of `g` at most `x` exceeds the number of roots of `f` at most `x` by one.
-/
theorem endpointSign_lowerRootCount_sub_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hprec : Prec f g) {x : ℝ} (hxf : ¬ f.IsRoot x)
    (hxg : ¬ g.IsRoot x) (hprod : 0 < f.eval x * g.eval x) :
    ((g.roots.filter (fun r => r ≤ x)).card : ℤ) -
      (f.roots.filter (fun r => r ≤ x)).card = 1 := by
  obtain ⟨hf, hg, ss, rs, _hss, _hrs, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hlen : ss.length + 1 = rs.length := by rw [hss_len, hrs_len, hdeg]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨_, hi⟩ | ⟨hbad, _⟩
    · exact hi
    · exfalso
      rw [hss_len, hrs_len, hdeg] at hbad
      lia
  have hf_upper : (f.roots.filter (x < ·)).card =
      (ss.filter (fun y => decide (x < y))).length := by
    rw [← hss_eq, Multiset.filter_coe, Multiset.coe_card]
  have hg_upper : (g.roots.filter (x < ·)).card =
      (rs.filter (fun y => decide (x < y))).length := by
    rw [← hrs_eq, Multiset.filter_coe, Multiset.coe_card]
  have hf_lower : (f.roots.filter (fun r => r ≤ x)).card =
      (ss.filter (fun y => decide (y ≤ x))).length := by
    rw [← hss_eq, Multiset.filter_coe, Multiset.coe_card]
  have hg_lower : (g.roots.filter (fun r => r ≤ x)).card =
      (rs.filter (fun y => decide (y ≤ x))).length := by
    rw [← hrs_eq, Multiset.filter_coe, Multiset.coe_card]
  have hnot_neg : ¬ f.eval x * g.eval x < 0 := not_lt.mpr (le_of_lt hprod)
  have hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card) := by
    intro hodd
    exact hnot_neg
      ((succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg
        hf_pos hg_pos hfg hdeg hf.2 hxf hxg).mp hodd)
  have hnot_list : ¬ Odd
      (((ss.filter (fun y => decide (x < y))).length : ℤ) -
        (rs.filter (fun y => decide (x < y))).length) := by
    rw [← hf_upper, ← hg_upper]
    exact hnot_odd
  have hcore :=
    listInterlaces_filter_le_sub_eq_one_of_not_odd_filter_lt_sub
      (x := x) hint hlen hnot_list
  rw [hf_lower, hg_lower]
  exact hcore

end RealRooted
