import RealRooted.LiuOppositeSigns.Theorem21Statements
import RealRooted.MaWang
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeCountFromAnalytic

/-!
# Liu positive-split pair bridge

This module contains the PositiveSplitRootCountPair bridge from Liu's
root-count packages to common interleavers and compatibility.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Same-degree positive-leading root-count leaf, phrased as a
`PositiveSplitRootCountPair` production target. -/
def positiveSplitSameDegreeRootCountAboveNonRootStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    PositiveSplitRootCountPair f g

/-- Succ-degree positive-leading root-count leaf, phrased as a
`PositiveSplitRootCountPair` production target. -/
def positiveSplitSuccDegreeRootCountAboveNonRootStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    PositiveSplitRootCountPair f g

theorem posComboNoCommonSameDegreeRootCountAboveNonRoot_of_positiveSplit
    (hpack : positiveSplitSameDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno x hfx hgx
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno).sameDegreeRootCountAboveNonRoot
    hdeg x hfx hgx

theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_positiveSplit
    (hpack : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x hfx hgx
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)
    |>.succDegreeRootCountAboveNonRoot hdeg x hfx hgx

/-- A strict-upper non-root count proof supplies the positive-split
same-degree Liu root-count package. -/
theorem positiveSplitSameDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    positiveSplitSameDegreeRootCountAboveNonRootStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact PositiveSplitRootCountPair.of_rootCountAbove_bounds_of_nonRoot
    hf_pos hg_pos hf_split hg_split
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- A strict-upper non-root count proof supplies the positive-split
successor-degree Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact PositiveSplitRootCountPair.of_rootCountAbove_bounds_of_nonRoot
    hf_pos hg_pos hf_split hg_split
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- A positive-leading same-degree compatible pair with no common roots
satisfies Liu's root-count compatibility condition. -/
theorem RootCountCompatible.of_compatible_sameDegree {f g : ℝ[X]}
    (hcompat : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    RootCountCompatible f g := by
  have hfg : PosComboRealRooted f g :=
    hcompat.toPosComboRealRooted hf_pos hg_pos
  exact RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hf_pos.ne_zero hg_pos.ne_zero
    (_root_.RealRooted.sameDegree_rootCountAbove_bounds_of_posCombo_noCommon
      hf_pos hg_pos hfg hdeg hno)

/-- A positive-leading, splitting, degree-one polynomial has one real root and
factors as its leading coefficient times the corresponding monic factor. -/
lemma exists_linear_factor_of_splits_natDegree_one
    {p : ℝ[X]} (hp_split : p.Splits) (hpdeg : p.natDegree = 1) :
    ∃ a : ℝ, p.roots = {a} ∧ p = C p.leadingCoeff * (X - C a) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, p.roots = {a} :=
    Multiset.card_eq_one.mp (by rw [card_roots_of_splits hp_split, hpdeg])
  refine ⟨a, ha, ?_⟩
  have hprod := hp_split.eq_prod_roots
  rw [ha] at hprod
  simpa using hprod

/-- In the `(2, 1)` positive split root-count case, the linear root cannot lie
strictly below both quadratic roots. -/
lemma left_root_le_singleton_root_of_positiveSplitRootCountPair_two_one
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c : ℝ} (hab : a ≤ b) (hfroots : f.roots = {a, b})
    (hgroots : g.roots = {c}) :
    a ≤ c := by
  by_contra hac
  have hca : c < a := lt_of_not_ge hac
  let x : ℝ := (a + c) / 2
  have hxa : x ≤ a := by
    dsimp [x]
    linarith
  have hxb : x ≤ b := hxa.trans hab
  have hcount := h.count.left_sub_le_one x
  have hf_count : rootCountAtOrAbove f x = 2 := by
    rw [rootCountAtOrAbove, hfroots]
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxb]
    simp
  have hg_count : rootCountAtOrAbove g x = 0 := by
    rw [rootCountAtOrAbove, hgroots]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r),
      if_neg (by dsimp [x]; linarith)]
    simp
  rw [hf_count, hg_count] at hcount
  norm_num at hcount

/-- In the `(3, 2)` positive split root-count case, the roots obey the
finite interleaving inequalities forced by Liu's closed upper-threshold count
condition. -/
lemma roots_order_of_positiveSplitRootCountPair_three_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    a ≤ u ∧ b ≤ v ∧ u ≤ c := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hau
    have hua : u < a := lt_of_not_ge hau
    let x : ℝ := (a + u) / 2
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hxc : x ≤ c := hxb.trans hbc
    have hux : u < x := by
      dsimp [x]
      linarith
    have hf_count : rootCountAtOrAbove f x = 3 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxa, hxb, hxc]
    have hq_count_le : rootCountAtOrAbove g x ≤ 1 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      by_cases hxv : x ≤ v
      · simp [hnot_xu, hxv]
      · simp [hnot_xu, hxv]
    have hcount := h.count.left_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hq_count_int : ((rootCountAtOrAbove g x : ℤ) ≤ 1) := by
      exact_mod_cast hq_count_le
    linarith
  · by_contra hbv
    have hvb : v < b := lt_of_not_ge hbv
    let x : ℝ := (b + v) / 2
    have hxb : x ≤ b := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := hxb.trans hbc
    have hvx : v < x := by
      dsimp [x]
      linarith
    have hux : u < x := lt_of_le_of_lt huv hvx
    have hf_count_ge : 2 ≤ rootCountAtOrAbove f x := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxa : x ≤ a
      · simp [hxa, hxb, hxc]
      · simp [hxa, hxb, hxc]
    have hq_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      simp [hnot_xu, hnot_xv]
    have hcount := h.count.left_sub_le_one x
    rw [hq_count] at hcount
    norm_num at hcount
    have hf_count_int : (2 : ℤ) ≤ rootCountAtOrAbove f x := by
      exact_mod_cast hf_count_ge
    linarith
  · by_contra huc
    have hcu : c < u := lt_of_not_ge huc
    let x : ℝ := (c + u) / 2
    have hcx : c < x := by
      dsimp [x]
      linarith
    have hxu : x ≤ u := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt (hab.trans hbc) hcx
    have hbx : b < x := lt_of_le_of_lt hbc hcx
    have hxv : x ≤ v := hxu.trans huv
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      simp [hnot_xa, hnot_xb, hnot_xc]
    have hq_count : rootCountAtOrAbove g x = 2 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxu, hxv]
    have hcount := h.count.right_sub_le_one x
    rw [hf_count, hq_count] at hcount
    norm_num at hcount

/-- A `(3, 2)` positive split root-count pair admits ordered root data with
the interleaving inequalities needed by the degree-two x-subtraction terminal.
-/
lemma exists_roots_order_of_positiveSplitRootCountPair_three_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2) :
    ∃ a b c u v : ℝ,
      a ≤ b ∧ b ≤ c ∧ u ≤ v ∧
        f.roots = {a, b, c} ∧ g.roots = {u, v} ∧
          f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) ∧
            g = C g.leadingCoeff * ((X - C u) * (X - C v)) ∧
              a ≤ u ∧ b ≤ v ∧ u ≤ c := by
  obtain ⟨a, b, c, hab, hbc, hfroots, hffac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.left_splits hfdeg
  obtain ⟨u, v, huv, hgroots, hgfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two h.right_splits hgdeg
  obtain ⟨hau, hbv, huc⟩ :=
    roots_order_of_positiveSplitRootCountPair_three_two
      h hab hbc huv hfroots hgroots
  exact
    ⟨a, b, c, u, v, hab, hbc, huv, hfroots, hgroots, hffac, hgfac,
      hau, hbv, huc⟩

/-- A split real quartic factors through an ordered quadruple of real roots. -/
theorem exists_roots_quadruple_of_splits_natDegree_four {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 4) :
    ∃ a b c d : ℝ, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      f.roots = {a, b, c, d} ∧
        f = C f.leadingCoeff *
          ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_len : rs.length = 4 := by
    simp [rs, card_roots_of_splits hf, hdeg]
  obtain ⟨a, b, c, d, hrs⟩ := List.length_eq_four.mp hrs_len
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by
    simp [rs]
  have hsorted : ([a, b, c, d] : List ℝ).Pairwise (· ≤ ·) := by
    simpa [hrs] using hrs_sorted
  have hab : a ≤ b := by
    simpa using (List.pairwise_cons.1 hsorted).1 b (by simp)
  have hbc : b ≤ c := by
    have htail := (List.pairwise_cons.1 hsorted).2
    simpa using (List.pairwise_cons.1 htail).1 c (by simp)
  have hcd : c ≤ d := by
    have htail := (List.pairwise_cons.1 hsorted).2
    have htail2 := (List.pairwise_cons.1 htail).2
    simpa using (List.pairwise_cons.1 htail2).1 d (by simp)
  have hcoe : f.roots = {a, b, c, d} := by
    have hse : (↑rs : Multiset ℝ) = f.roots := by
      simp [rs]
    rw [hrs] at hse
    rw [← hse]
    rfl
  refine ⟨a, b, c, d, hab, hbc, hcd, hcoe, ?_⟩
  rw [Polynomial.Splits.eq_prod_roots hf, hcoe]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- In the `(4, 3)` positive split root-count case, the roots obey the finite
inequalities needed by the quartic/cubic x-subtraction endpoint. -/
lemma roots_order_of_positiveSplitRootCountPair_four_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c d u v w : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hfroots : f.roots = {a, b, c, d})
    (hgroots : g.roots = {u, v, w}) :
    a ≤ u ∧ b ≤ v ∧ c ≤ w ∧ u ≤ c ∧ v ≤ d := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra hau
    have hua : u < a := lt_of_not_ge hau
    let x : ℝ := (a + u) / 2
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hxc : x ≤ c := hxb.trans hbc
    have hxd : x ≤ d := hxc.trans hcd
    have hux : u < x := by
      dsimp [x]
      linarith
    have hf_count : rootCountAtOrAbove f x = 4 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxa, hxb, hxc, hxd]
    have hg_count_le : rootCountAtOrAbove g x ≤ 2 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      by_cases hxv : x ≤ v <;> by_cases hxw : x ≤ w <;>
        simp [hnot_xu, hxv, hxw]
    have hcount := h.count.left_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hg_count_int : ((rootCountAtOrAbove g x : ℤ) ≤ 2) := by
      exact_mod_cast hg_count_le
    linarith
  · by_contra hbv
    have hvb : v < b := lt_of_not_ge hbv
    let x : ℝ := (b + v) / 2
    have hxb : x ≤ b := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := hxb.trans hbc
    have hxd : x ≤ d := hxc.trans hcd
    have hvx : v < x := by
      dsimp [x]
      linarith
    have hux : u < x := lt_of_le_of_lt huv hvx
    have hf_count_ge : 3 ≤ rootCountAtOrAbove f x := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxa : x ≤ a <;> simp [hxa, hxb, hxc, hxd]
    have hg_count_le : rootCountAtOrAbove g x ≤ 1 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      by_cases hxw : x ≤ w <;> simp [hnot_xu, hnot_xv, hxw]
    have hcount := h.count.left_sub_le_one x
    have hf_count_int : (3 : ℤ) ≤ rootCountAtOrAbove f x := by
      exact_mod_cast hf_count_ge
    have hg_count_int : ((rootCountAtOrAbove g x : ℤ) ≤ 1) := by
      exact_mod_cast hg_count_le
    linarith
  · by_contra hcw
    have hwc : w < c := lt_of_not_ge hcw
    let x : ℝ := (c + w) / 2
    have hxc : x ≤ c := by
      dsimp [x]
      linarith
    have hxd : x ≤ d := hxc.trans hcd
    have hwx : w < x := by
      dsimp [x]
      linarith
    have hux : u < x := lt_of_le_of_lt (huv.trans hvw) hwx
    have hvx : v < x := lt_of_le_of_lt hvw hwx
    have hf_count_ge : 2 ≤ rootCountAtOrAbove f x := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxa : x ≤ a <;> by_cases hxb : x ≤ b <;>
        simp [hxa, hxb, hxc, hxd]
    have hg_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      have hnot_xw : ¬ x ≤ w := not_le.mpr hwx
      simp [hnot_xu, hnot_xv, hnot_xw]
    have hcount := h.count.left_sub_le_one x
    rw [hg_count] at hcount
    norm_num at hcount
    have hf_count_int : (2 : ℤ) ≤ rootCountAtOrAbove f x := by
      exact_mod_cast hf_count_ge
    linarith
  · by_contra huc
    have hcu : c < u := lt_of_not_ge huc
    let x : ℝ := (c + u) / 2
    have hcx : c < x := by
      dsimp [x]
      linarith
    have hxu : x ≤ u := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt (hab.trans hbc) hcx
    have hbx : b < x := lt_of_le_of_lt hbc hcx
    have hxv : x ≤ v := hxu.trans huv
    have hxw : x ≤ w := hxv.trans hvw
    have hf_count_le : rootCountAtOrAbove f x ≤ 1 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      by_cases hxd : x ≤ d <;> simp [hnot_xa, hnot_xb, hnot_xc, hxd]
    have hg_count : rootCountAtOrAbove g x = 3 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxu, hxv, hxw]
    have hcount := h.count.right_sub_le_one x
    rw [hg_count] at hcount
    norm_num at hcount
    have hf_count_int : ((rootCountAtOrAbove f x : ℤ) ≤ 1) := by
      exact_mod_cast hf_count_le
    linarith
  · by_contra hvd
    have hdv : d < v := lt_of_not_ge hvd
    let x : ℝ := (d + v) / 2
    have hdx : d < x := by
      dsimp [x]
      linarith
    have hxv : x ≤ v := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt (hab.trans (hbc.trans hcd)) hdx
    have hbx : b < x := lt_of_le_of_lt (hbc.trans hcd) hdx
    have hcx : c < x := lt_of_le_of_lt hcd hdx
    have hxw : x ≤ w := hxv.trans hvw
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      have hnot_xd : ¬ x ≤ d := not_le.mpr hdx
      simp [hnot_xa, hnot_xb, hnot_xc, hnot_xd]
    have hg_count_ge : 2 ≤ rootCountAtOrAbove g x := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxu : x ≤ u <;> simp [hxu, hxv, hxw]
    have hcount := h.count.right_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hg_count_int : (2 : ℤ) ≤ rootCountAtOrAbove g x := by
      exact_mod_cast hg_count_ge
    linarith

/-- A `(4, 3)` positive split root-count pair admits ordered root data with
the inequalities needed by the quartic/cubic x-subtraction terminal. -/
lemma exists_roots_order_of_positiveSplitRootCountPair_four_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    (hfdeg : f.natDegree = 4) (hgdeg : g.natDegree = 3) :
    ∃ a b c d u v w : ℝ,
      a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ u ≤ v ∧ v ≤ w ∧
        f.roots = {a, b, c, d} ∧ g.roots = {u, v, w} ∧
          f = C f.leadingCoeff *
            ((X - C a) * (X - C b) * (X - C c) * (X - C d)) ∧
            g = C g.leadingCoeff * ((X - C u) * (X - C v) * (X - C w)) ∧
              a ≤ u ∧ b ≤ v ∧ c ≤ w ∧ u ≤ c ∧ v ≤ d := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hfroots, hffac⟩ :=
    exists_roots_quadruple_of_splits_natDegree_four h.left_splits hfdeg
  obtain ⟨u, v, w, huv, hvw, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.right_splits hgdeg
  obtain ⟨hau, hbv, hcw, huc, hvd⟩ :=
    roots_order_of_positiveSplitRootCountPair_four_three
      h hab hbc hcd huv hvw hfroots hgroots
  exact
    ⟨a, b, c, d, u, v, w, hab, hbc, hcd, huv, hvw, hfroots,
      hgroots, hffac, hgfac, hau, hbv, hcw, huc, hvd⟩

namespace PositiveSplitRootCountPair

theorem pairHasCommonInterleaver_of_sameDegree {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g) (hdeg : g.natDegree = f.natDegree) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  have hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 1 :=
    sameDegreeRootCountAbove_of_nonRoot_bound
      h.left_pos.ne_zero h.right_pos.ne_zero
      (fun _ hfx hgx => h.rootCountAbove_bounds_of_nonRoot hfx hgx)
  have hcross :=
    rootCrossing_of_rootCountAbove_diff_le_one
      h.left_splits h.right_splits hdeg hcount
  have hlenf : (rootSeqDesc f).length = f.natDegree :=
    rootSeqDesc_length h.left_splits
  have hleng : (rootSeqDesc g).length = g.natDegree :=
    rootSeqDesc_length h.right_splits
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      h.left_pos.ne_zero h.right_pos.ne_zero h.left_splits h.right_splits hdeg <|
        fun j hj =>
          rootSlotInterval_inter_nonempty_of_sameDegree_crossing
            (rootSeqDesc f) (rootSeqDesc g)
            rootSeqDesc_pairwise rootSeqDesc_pairwise
            (by rw [hleng, hlenf, hdeg])
            (fun k hk1 hk2 => hcross.1 k hk1 (by rw [hlenf] at hk2; exact hk2))
            (fun k hk1 hk2 => hcross.2 k hk1 (by rw [hlenf] at hk2; exact hk2))
            j (by rw [hlenf]; exact hj) (by rw [hleng, hdeg]; exact hj)

theorem pairHasCommonInterleaver_of_succDegree {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  have hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 1 :=
    sameDegreeRootCountAbove_of_nonRoot_bound
      h.left_pos.ne_zero h.right_pos.ne_zero
      (fun _ hfx hgx => h.rootCountAbove_bounds_of_nonRoot hfx hgx)
  have hcross :=
    succDegreeRootCrossing_of_rootCountAbove
      h.left_splits h.right_splits hdeg hcount
  have hlenf : (rootSeqDesc f).length = f.natDegree :=
    rootSeqDesc_length h.left_splits
  have hleng : (rootSeqDesc g).length = g.natDegree :=
    rootSeqDesc_length h.right_splits
  exact
    pairHasCommonInterleaver_of_succDegree_slotIntersections
      h.left_pos.ne_zero h.right_pos.ne_zero h.left_splits h.right_splits hdeg <|
        fun j hj =>
          rootSlotInterval_inter_nonempty_of_crossing
            (rootSeqDesc f) (rootSeqDesc g)
            rootSeqDesc_pairwise rootSeqDesc_pairwise
            (by rw [hleng, hlenf, hdeg])
            (fun k hk1 hk2 => hcross.1 k hk1 (by rw [hlenf] at hk2; exact hk2))
            (fun k hk1 hk2 => hcross.2 k hk1 (by rw [hlenf] at hk2; exact hk2))
            j (by rw [hlenf]; exact hj)
            (by
              rw [hleng, hdeg]
              exact Nat.lt_succ_of_lt hj)

/-- Common-interleaver constructor for the reverse successor-degree
orientation. -/
theorem pairHasCommonInterleaver_of_leftSuccDegree {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g)
    (hdeg : f.natDegree = g.natDegree + 1) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  obtain ⟨h', hgh, hfh⟩ := h.symm.pairHasCommonInterleaver_of_succDegree hdeg
  exact ⟨h', hfh, hgh⟩

/-- Any positive-leading split pair with Liu-compatible root counts has a
common interleaver. -/
theorem pairHasCommonInterleaver {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  have hgap := h.natDegree_abs_sub_le_one
  have hleft : f.natDegree ≤ g.natDegree + 1 := by
    have hle := (abs_le.mp hgap).2
    have : (f.natDegree : ℤ) ≤ (g.natDegree : ℤ) + 1 := by linarith
    exact_mod_cast this
  have hright : g.natDegree ≤ f.natDegree + 1 := by
    have hle := (abs_le.mp hgap).1
    have : (g.natDegree : ℤ) ≤ (f.natDegree : ℤ) + 1 := by linarith
    exact_mod_cast this
  by_cases hfg_eq : f.natDegree = g.natDegree
  · exact h.pairHasCommonInterleaver_of_sameDegree hfg_eq.symm
  · rcases Nat.lt_or_gt_of_ne hfg_eq with hfg_lt | hgf_lt
    · have hdeg : g.natDegree = f.natDegree + 1 :=
        Nat.le_antisymm hright (Nat.succ_le_of_lt hfg_lt)
      exact h.pairHasCommonInterleaver_of_succDegree hdeg
    · have hdeg : f.natDegree = g.natDegree + 1 :=
        Nat.le_antisymm hleft (Nat.succ_le_of_lt hgf_lt)
      exact h.pairHasCommonInterleaver_of_leftSuccDegree hdeg

/-- Liu-compatible positive-leading split pairs are compatible. -/
theorem compatible {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g) :
    Compatible f g := by
  obtain ⟨k, hfk, hgk⟩ := h.pairHasCommonInterleaver
  exact Compatible.of_commonInterleaver hfk hgk h.left_pos h.right_pos

/-- A common-right-interleaver witness is unchanged by removing a negation
from the left endpoint, since `Prec` only depends on the roots. -/
theorem pairHasCommonInterleaver_of_neg_left {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair (-f) g) :
    ∃ k : ℝ[X], Prec f k ∧ Prec g k := by
  obtain ⟨k, hfk, hgk⟩ := h.pairHasCommonInterleaver
  refine ⟨k, ?_, hgk⟩
  have hscale : Prec (C (-1 : ℝ) * (-f)) k :=
    prec_C_mul_left hfk (by norm_num)
  simpa using hscale

/-- A common-right-interleaver witness is unchanged by removing a negation
from the right endpoint, since `Prec` only depends on the roots. -/
theorem pairHasCommonInterleaver_of_neg_right {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f (-g)) :
    ∃ k : ℝ[X], Prec f k ∧ Prec g k := by
  obtain ⟨k, hfk, hgk⟩ := h.pairHasCommonInterleaver
  refine ⟨k, hfk, ?_⟩
  have hscale : Prec (C (-1 : ℝ) * (-g)) k :=
    prec_C_mul_left hgk (by norm_num)
  simpa using hscale

end PositiveSplitRootCountPair

/-- All-combinations real-rootedness descends through translation by
`X + C r`. -/
theorem allComboRealRooted_of_comp_X_add_C {f g : ℝ[X]} (r : ℝ)
    (hall : AllComboRealRooted (f.comp (X + C r)) (g.comp (X + C r))) :
    AllComboRealRooted f g := by
  intro α β
  have htranslate :
      (C α * f + C β * g).comp (X + C r) =
        C α * f.comp (X + C r) + C β * g.comp (X + C r) := by
    simp
  exact splits_of_comp_X_add_C_splits r
    (by simpa [htranslate] using hall α β)

namespace Compatible

/-- Compatibility descends through translation by `X + C r`. -/
lemma of_comp_X_add_C {f g : ℝ[X]} (r : ℝ)
    (hcompat : Compatible (f.comp (X + C r)) (g.comp (X + C r))) :
    Compatible f g := by
  intro α β hα hβ
  have htranslate :
      C α * f.comp (X + C r) + C β * g.comp (X + C r) =
        (C α * f + C β * g).comp (X + C r) := by
    simp
  rcases hcompat α β hα hβ with hzero | hrr
  · left
    by_contra hne
    have hcomp_ne : (C α * f + C β * g).comp (X + C r) ≠ 0 :=
      (Polynomial.comp_X_add_C_ne_zero_iff).2 hne
    exact hcomp_ne (htranslate ▸ hzero)
  · right
    refine ⟨?_, ?_⟩
    · intro hzero
      have hcomp_zero : (C α * f + C β * g).comp (X + C r) = 0 := by
        simpa using congrArg (fun p : ℝ[X] => p.comp (X + C r)) hzero
      exact hrr.1 (htranslate.symm ▸ hcomp_zero)
    · exact splits_of_comp_X_add_C_splits r (htranslate ▸ hrr.2)

/-- A one-parameter positive right pencil, together with split endpoints,
gives full nonnegative compatibility by scaling the left coefficient to `1`. -/
lemma of_splits_of_pos_right_family {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits)
    (hfamily : ∀ μ : ℝ, 0 < μ → (f + C μ * g).Splits) :
    Compatible f g := by
  intro α β hα hβ
  by_cases hsum : C α * f + C β * g = 0
  · exact Or.inl hsum
  · right
    refine ⟨hsum, ?_⟩
    by_cases hα0 : α = 0
    · subst hα0
      simpa using (Polynomial.Splits.C (R := ℝ) β).mul hg
    · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      by_cases hβ0 : β = 0
      · subst hβ0
        simpa using (Polynomial.Splits.C (R := ℝ) α).mul hf
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
        have hμ_pos : 0 < β / α := div_pos hβ_pos hα_pos
        have hright : (f + C (β / α) * g).Splits :=
          hfamily (β / α) hμ_pos
        have hscale :
            C α * (f + C (β / α) * g) = C α * f + C β * g := by
          rw [mul_add]
          congr 1
          have hαβ : α * (β / α) = β := by
            field_simp [hα0]
          calc
            C α * (C (β / α) * g) = C (α * (β / α)) * g := by
              simp [mul_assoc]
            _ = C β * g := by rw [hαβ]
        rw [← hscale]
        exact (Polynomial.Splits.C (R := ℝ) α).mul hright

end Compatible

end LiuOppositeSigns
end RealRooted
