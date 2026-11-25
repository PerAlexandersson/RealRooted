module

import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SameDegree
import RealRooted.CommonInterleaver.RootCountCombinatorics
public import RealRooted.LiuOppositeSigns.XSub.LinearQuadratic
import RealRooted.LiuOppositeSigns.XSub.SplittingTools
import RealRooted.LiuOppositeSigns.XSub.SameDegree
public import RealRooted.LiuOppositeSigns.PositiveSplitRootCount
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.QuadraticRoot
import RealRooted.MaWang.StrictSigns.Assembly
import RealRooted.MaWang.StrictSigns.RootSigns
import RealRooted.Linear

/-!
# Liu quadratic/quadratic x-subtraction leaf

This module contains the normalized quadratic/quadratic positive-split
x-subtraction cases, derived from the general same-degree endpoint.
-/

public section

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The normalized degree-two pair has a common interleaver, so the general
same-degree tail theorem applies, including all root coincidences. -/
private lemma normalized_quadratic {a b c d μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (had : a ≤ d)
    (hcb : c ≤ b) (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) - C μ * ((X - C c) * (X - C d))).Splits := by
  let p : ℝ[X] := (X - C a) * (X - C b)
  let q : ℝ[X] := (X - C c) * (X - C d)
  let k : ℝ[X] := (X - C (max a c)) * (X - C (max b d))
  have hp : p.Monic := (monic_X_sub_C a).mul (monic_X_sub_C b)
  have hq : q.Monic := (monic_X_sub_C c).mul (monic_X_sub_C d)
  have hk : k.Monic := (monic_X_sub_C (max a c)).mul (monic_X_sub_C (max b d))
  have hp_split : p.Splits := (Splits.X_sub_C a).mul (Splits.X_sub_C b)
  have hq_split : q.Splits := (Splits.X_sub_C c).mul (Splits.X_sub_C d)
  have hk_split : k.Splits :=
    (Splits.X_sub_C (max a c)).mul (Splits.X_sub_C (max b d))
  have hp_roots : p.roots = (↑[a, b] : Multiset ℝ) := by
    change p.roots = {a, b}
    simp [p, roots_mul, X_sub_C_ne_zero]
  have hq_roots : q.roots = (↑[c, d] : Multiset ℝ) := by
    change q.roots = {c, d}
    simp [q, roots_mul, X_sub_C_ne_zero]
  have hk_roots : k.roots = (↑[max a c, max b d] : Multiset ℝ) := by
    change k.roots = {max a c, max b d}
    simp [k, roots_mul, X_sub_C_ne_zero]
  have hpk : StrictInterl p k := by
    refine ⟨⟨hp.ne_zero, hp_split⟩, ⟨hk.ne_zero, hk_split⟩,
      [a, b], [max a c, max b d], ?_, ?_, hp_roots.symm, hk_roots.symm, Or.inr ?_⟩
    · simp [hab]
    · grind [List.pairwise_cons, max_le_iff, le_max_iff]
    · exact ⟨rfl, by simp [ListAlternates, ListInterlaces, hab, hcb, max_le_iff]⟩
  have hqk : StrictInterl q k := by
    refine ⟨⟨hq.ne_zero, hq_split⟩, ⟨hk.ne_zero, hk_split⟩,
      [c, d], [max a c, max b d], ?_, ?_, hq_roots.symm, hk_roots.symm, Or.inr ?_⟩
    · simp [hcd]
    · grind [List.pairwise_cons, max_le_iff, le_max_iff]
    · exact ⟨rfl, by simp [ListAlternates, ListInterlaces, had, hcd, max_le_iff]⟩
  have hpair : PositiveSplitRootCountPair p q := by
    refine ⟨hasPosLeadingCoeff_of_monic hp, hasPosLeadingCoeff_of_monic hq,
      hp_split, hq_split, ?_⟩
    apply RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot hp.ne_zero hq.ne_zero
    intro x _ _
    have hpdeg : k.natDegree = p.natDegree := by
      simp [p, k, natDegree_mul, X_sub_C_ne_zero]
    have hpbound :=
      (sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
        hk_split hp_split hpdeg.symm x).mpr
          (sameDegreeRootCountOriented_of_strictInterl hpk hpdeg x)
    have hqdeg : k.natDegree = q.natDegree := by
      simp [q, k, natDegree_mul, X_sub_C_ne_zero]
    have hqbound :=
      (sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
        hk_split hq_split hqdeg.symm x).mpr
          (sameDegreeRootCountOriented_of_strictInterl hqk hqdeg x)
    constructor <;> lia
  have hpnn : HasNonnegCoeffs p :=
    (hasNonnegCoeffs_X_sub_C (hab.trans hb0)).mul (hasNonnegCoeffs_X_sub_C hb0)
  have hqnn : HasNonnegCoeffs q :=
    (hasNonnegCoeffs_X_sub_C (hcd.trans hd0)).mul (hasNonnegCoeffs_X_sub_C hd0)
  exact hpair.xSub_splits_of_same_degree_nonneg hpnn hqnn
    (by simp [p, q, natDegree_mul, X_sub_C_ne_zero]) hμ

/-- In the `(2, 2)` positive split root-count case, the two ordered root
intervals overlap. -/
lemma roots_overlap_of_positiveSplitRootCountPair_two_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d}) :
    a ≤ d ∧ c ≤ b := by
  constructor
  · by_contra had
    have hda : d < a := lt_of_not_ge had
    let x : ℝ := (a + d) / 2
    have hdx : d < x := by
      dsimp [x]
      linarith
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hcx : c < x := lt_of_le_of_lt hcd hdx
    have hcount := h.count.left_sub_le_one x
    have hf_count : rootCountAtOrAbove f x = 2 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa,
        Multiset.filter_singleton, ite_eq_left hxb]
      simp
    have hg_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [not_le.mpr hcx, not_le.mpr hdx]
    rw [hf_count, hg_count] at hcount
    norm_num at hcount
  · by_contra hcb
    have hbc : b < c := lt_of_not_ge hcb
    let x : ℝ := (b + c) / 2
    have hbx : b < x := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := by
      dsimp [x]
      linarith
    have hxd : x ≤ d := hxc.trans hcd
    have hax : a < x := lt_of_le_of_lt hab hbx
    have hcount := h.count.right_sub_le_one x
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [not_le.mpr hax, not_le.mpr hbx]
    have hg_count : rootCountAtOrAbove g x = 2 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.filter_cons_of_pos ({d} : Multiset ℝ) hxc,
        Multiset.filter_singleton, ite_eq_left hxd]
      simp
    rw [hf_count, hg_count] at hcount
    norm_num at hcount

/-- A monic quadratic minus a positive multiple of a linear factor splits
whenever the linear root lies weakly below the upper quadratic root. -/
lemma quadraticSubLinear_splits_of_right_root_le_upper
    {a b c μ : ℝ} (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits := by
  have hpoly :
      ((X - C a) * (X - C b)) - C μ * (X - C c) =
        C 1 * X ^ 2 + C (-(a + b + μ)) * X + C (a * b + μ * c) := by
    simp only [C_add, C_mul, C_neg, C_1]
    ring
  have hdisc : 0 ≤ discrim 1 (-(a + b + μ)) (a * b + μ * c) := by
    by_cases hac : a ≤ c
    · let u : ℝ := c - a
      let v : ℝ := b - c
      have hu : 0 ≤ u := by dsimp [u]; linarith
      have hv : 0 ≤ v := by dsimp [v]; linarith
      have hdisc_eq :
          discrim 1 (-(a + b + μ)) (a * b + μ * c) =
            (μ + v - u) ^ 2 + 4 * u * v := by
        dsimp [u, v]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
    · have hca : c ≤ a := le_of_not_ge hac
      let u : ℝ := a - c
      let v : ℝ := b - a
      have hu : 0 ≤ u := by dsimp [u]; linarith
      have hv : 0 ≤ v := by dsimp [v]; linarith
      have hdisc_eq :
          discrim 1 (-(a + b + μ)) (a * b + μ * c) =
            μ ^ 2 + 4 * μ * u + 2 * μ * v + v ^ 2 := by
        dsimp [u, v]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc

/-- Boundary case of the quadratic/quadratic leaf when the right endpoint has
root zero.  Factoring out `X` leaves a quadratic-minus-linear pencil. -/
lemma xSubQuadraticQuadraticSplits_of_right_root_zero
    {a b c μ : ℝ} (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * X)).Splits := by
  have hquad : (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits :=
    quadraticSubLinear_splits_of_right_root_le_upper hab hcb hμ
  have hfactor :
      X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * X) =
          X * (((X - C a) * (X - C b)) - C μ * (X - C c)) := by
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hquad

/-- Boundary case of the quadratic/quadratic leaf when the two quadratic
endpoints share a root. -/
lemma xSubQuadraticQuadraticSplits_of_common_root
    {r s t μ : ℝ} (hs0 : s ≤ 0) (ht0 : t ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * (X - C s)) -
      C μ * ((X - C r) * (X - C t))).Splits := by
  have hquad₀ :
      (((X - C s) * (X - C 0)) - C μ * (X - C t)).Splits :=
    quadraticSubLinear_splits_of_right_root_le_upper
      (a := s) (b := 0) (c := t) hs0 ht0 hμ
  have hquad : (X * (X - C s) - C μ * (X - C t)).Splits := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquad₀
  have hfactor :
      X * ((X - C r) * (X - C s)) -
        C μ * ((X - C r) * (X - C t)) =
          (X - C r) * (X * (X - C s) - C μ * (X - C t)) := by
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hquad

/-- The normalized quadratic/quadratic x-subtraction polynomial is a genuine
cubic. -/
lemma natDegree_xSubQuadraticQuadratic (a b c d μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).natDegree = 3 := by
  compute_degree <;> norm_num

/-- The normalized quadratic/quadratic x-subtraction polynomial is nonzero. -/
lemma xSubQuadraticQuadratic_ne_zero (a b c d μ : ℝ) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d)) ≠ 0 := fun hzero => by
  have hdeg := natDegree_xSubQuadraticQuadratic a b c d μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized quadratic/quadratic x-subtraction polynomial has positive
leading coefficient. -/
lemma hasPosLeadingCoeff_xSubQuadraticQuadratic (a b c d μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))) := by
  have hquad_pos : HasPosLeadingCoeff ((X - C a) * (X - C b)) :=
    (hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b))) :=
    hquad_pos.X_mul
  have hleft_deg : (X * ((X - C a) * (X - C b))).natDegree = 3 := by compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C c) * (X - C d))).natDegree <
      (X * ((X - C a) * (X - C b))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C c) * (X - C d))) <
      degree (X * ((X - C a) * (X - C b))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized quadratic/quadratic x-subtraction leaf. -/
lemma eval_xSubQuadraticQuadratic (a b c d μ x : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).eval x =
      x * ((x - a) * (x - b)) - μ * ((x - c) * (x - d)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized quadratic/quadratic x-subtraction polynomial tends to
`+∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticQuadratic_atTop_atTop (a b c d μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  apply P.tendsto_atTop_of_leadingCoeff_nonneg
  · apply natDegree_pos_iff_degree_pos.mp
    simp [P, natDegree_xSubQuadraticQuadratic]
  · have h := (hasPosLeadingCoeff_xSubQuadraticQuadratic a b c d μ).le
    simpa [P] using h

private lemma splits_of_two_sign_changes_of_cubic {p : ℝ[X]} {a b c d : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 3)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) (hd0 : d ≤ 0)
    (hab_sign : p.eval a * p.eval b < 0) (hcd_sign : p.eval c * p.eval d < 0)
    (hzero : p.eval 0 ≤ 0) (htop : Tendsto (fun x => p.eval x) atTop atTop) :
    p.Splits := by
  obtain ⟨r₁, _, hr₁b, hr₁_root⟩ := exists_isRoot_between_of_eval_mul_neg hab hab_sign
  obtain ⟨r₂, cr₂, hr₂d, hr₂_root⟩ := exists_isRoot_between_of_eval_mul_neg hcd hcd_sign
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hzero htop
  exact splits_of_three_ordered_roots_of_natDegree_le hp_ne hdeg
    (lt_trans hr₁b (hbc.trans_lt cr₂))
    (lt_of_lt_of_le (hr₂d.trans_le hd0) hrR_ge) hr₁_root hr₂_root hrR_root

/-- Strict order case `a < c < b < d < 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_a_c_b_d
    {a b c d μ : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  apply normalized_quadratic <;> linarith

/-- Strict order case `a < c ≤ d < b ≤ 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_a_c_d_b
    {a b c d μ : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  apply normalized_quadratic <;> linarith

/-- Strict order case `c < a ≤ b < d < 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_c_a_b_d
    {a b c d μ : ℝ} (hca : c < a) (hab : a ≤ b) (hbd : b < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  apply normalized_quadratic <;> linarith

/-- Strict order case `c < a < d < b ≤ 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_c_a_d_b
    {a b c d μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  apply normalized_quadratic <;> linarith

/-- The normalized monic quadratic/quadratic x-subtraction pencil splits. -/
theorem xSubQuadraticQuadraticSplits {a b c d μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (had : a ≤ d)
    (hcb : c ≤ b) (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) - C μ * ((X - C c) * (X - C d))).Splits := by
  exact normalized_quadratic hab hcd had hcb hb0 hd0 hμ

/-- Degree-two/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  exact hpair.xSub_splits_of_same_degree_nonneg hpnn hqnn (by lia) hμ

/-- Degree-two right endpoint case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 2 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 2 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 2 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two
    (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Endpoint cases through right degree two for the same-degree
sign-normalized x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_one : g.natDegree ≤ 1
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
      hpair hgnn hdeg hle_one
  · have htwo : g.natDegree = 2 := by lia
    exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two
      hpair hfnn hgnn hdeg htwo

end LiuOppositeSigns
end RealRooted
