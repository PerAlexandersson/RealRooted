import RealRooted.LiuOppositeSigns.Theorem21Statements.NoCommonCrossing.CrossOwnedGaps

/-!
# Branch consequences of Liu's no-common-root crossing argument

This module turns the cross-owned-gap invariant and root-count bounds into the
left/right Theorem 2.1 branch predicate.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Opposite-sign caller boundary for the finite Liu count descent from the
cross-owned finite-gap input.  This avoids asking for the stronger original
one-sided `≤ 1` strict-upper bounds, which do not hold in every deletion
orientation. -/
theorem theorem21RootCountBranches_of_crossOwned
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ := exists_largestRoots hf hg hsgn hf_deg hg_deg
  exact theorem21RootCountBranches_of_crossOwned_consecutive_roots
    hsgn.left_ne_zero hsgn.right_ne_zero hr hs
    (fun _ hc => hsimple_f.roots_count_eq_one hc)
    (fun _ hc => hsimple_g.roots_count_eq_one hc)
    hno hcross

/-- Caller boundary for Liu's finite count descent from open-gap
root-freeness data for the endpoint families.  This composes the analytic
`CrossOwnedNotOddGaps` supplier with the existing finite root-count branch
theorem, without introducing a new branch hierarchy. -/
theorem theorem21RootCountBranches_of_no_isRoot_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_no : ∀ x a b : ℝ, a < x → x < b →
      f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ z : ℝ, a < z → z < b →
        ¬ (g + C (νL x)⁻¹ * f).IsRoot z)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_no : ∀ x a b : ℝ, a < x → x < b →
      g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ z : ℝ, a < z → z < b →
        ¬ (f + C (νR x) * g).IsRoot z) :
    theorem21RootCountBranches f g := by
  exact theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_no_isRoot_Ioo
      hfg hno hf hg νL νR hνL_pos hνL_large hdegL hleft_no
      hνR_pos hνR_small hdegR hright_no)

/-- A distinct-degree compatible pair is strictly positive-combination
real-rooted.  The usual positive-leading hypothesis is not needed here:
distinct endpoint degrees rule out the zero-polynomial branch for positive
weights by comparing the degrees of the two scaled summands. -/
theorem posComboRealRooted_of_compatible_natDegree_ne
    {f g : ℝ[X]} (hcompat : Compatible f g)
    (hdeg : f.natDegree ≠ g.natDegree) :
    PosComboRealRooted f g := by
  intro α β hα hβ
  rcases hcompat α β hα.le hβ.le with hzero | hrr
  · exfalso
    have hαdeg : (C α * f).natDegree = f.natDegree :=
      Polynomial.natDegree_C_mul (ne_of_gt hα)
    have hβdeg : (C β * g).natDegree = g.natDegree :=
      Polynomial.natDegree_C_mul (ne_of_gt hβ)
    rcases lt_or_gt_of_ne hdeg with hlt | hgt
    · have hscaled : (C α * f).natDegree < (C β * g).natDegree := by simpa [hαdeg, hβdeg] using hlt
      have hsum_deg :
          (C α * f + C β * g).natDegree = (C β * g).natDegree :=
        Polynomial.natDegree_add_eq_right_of_natDegree_lt hscaled
      have hg_deg_zero : g.natDegree = 0 := by
        simpa [hzero, hβdeg, Polynomial.natDegree_zero] using hsum_deg.symm
      have hg_deg_pos : 0 < g.natDegree :=
        lt_of_le_of_lt (Nat.zero_le _) hlt
      lia
    · have hscaled : (C β * g).natDegree < (C α * f).natDegree := by simpa [hαdeg, hβdeg] using hgt
      have hsum_deg :
          (C α * f + C β * g).natDegree = (C α * f).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt hscaled
      have hf_deg_zero : f.natDegree = 0 := by
        simpa [hzero, hαdeg, Polynomial.natDegree_zero] using hsum_deg.symm
      have hf_deg_pos : 0 < f.natDegree :=
        lt_of_le_of_lt (Nat.zero_le _) hgt
      lia
  · exact hrr

/-- In the no-common, nonconstant splitting regime, compatibility supplies the
strictly positive-combination real-rootedness hypothesis.  A zero positive
combination would make every root of `g` a root of `f`, contradicting the
no-common-root hypothesis. -/
theorem posComboRealRooted_of_compatible_noCommon_nonconstant
    {f g : ℝ[X]} (hcompat : Compatible f g) (hno : NoCommonRoots f g)
    (hg : g.Splits) (hg_deg : g.natDegree ≠ 0) :
    PosComboRealRooted f g := by
  intro α β hα hβ
  rcases hcompat α β hα.le hβ.le with hzero | hrr
  · exfalso
    have hg_ne : g ≠ 0 := by
      intro hg_zero
      exact hg_deg (by simp [hg_zero])
    obtain ⟨r, hr_mem⟩ :=
      Multiset.exists_mem_of_ne_zero (hg.roots_ne_zero hg_deg)
    have hgr : g.IsRoot r := (Polynomial.mem_roots hg_ne).mp hr_mem
    have hsum_eval : (C α * f + C β * g).eval r = 0 := by simp [hzero]
    have hgr_eval : g.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hgr
    have hfr_eval : f.eval r = 0 := by
      have hα_eval : α * f.eval r = 0 := by
        simpa [eval_add, eval_mul, eval_C, hgr_eval] using hsum_eval
      exact (mul_eq_zero.mp hα_eval).resolve_left (ne_of_gt hα)
    have hfr : f.IsRoot r := by simpa [Polynomial.IsRoot.def] using hfr_eval
    exact (hno r hfr) hgr
  · exact hrr

/-- Caller boundary for Liu's finite count descent in the distinct-degree
case.  This is the preferred entry point when the endpoint degrees differ:
the local compactness and degree-constancy supplier proves the cross-owned
finite-gap input internally. -/
theorem theorem21RootCountBranches_of_natDegree_ne
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hdeg : f.natDegree ≠ g.natDegree) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_natDegree_ne hfg hno hf hg hdeg)

/-- Compatible caller boundary for Liu's finite count descent in the
distinct-degree case.  Compatibility supplies the positive-combination
real-rootedness hypothesis because unequal endpoint degrees prevent positive
linear combinations from vanishing. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_ne
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcompat : Compatible f g)
    (hdeg : f.natDegree ≠ g.natDegree) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_ne hsgn
    (posComboRealRooted_of_compatible_noCommon_nonconstant hcompat hno hg hg_deg)
    hf hg hf_deg hg_deg hsimple_f hsimple_g hno hdeg

/-- Caller boundary for Liu's finite count descent in the equal-degree case,
provided the positive crossing parameters stay on the appropriate side of the
unique leading-term cancellation parameter in same-owner gaps. -/
theorem theorem21RootCountBranches_of_natDegree_eq_of_crossing_cancel_sides
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hdeg : f.natDegree = g.natDegree)
    (hleft_cancel_lt : ∀ x a b : ℝ, a < x → x < b →
      f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
        -f.leadingCoeff / g.leadingCoeff < μ)
    (hright_lt_cancel : ∀ x a b : ℝ, a < x → x < b →
      g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
        μ < -f.leadingCoeff / g.leadingCoeff) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_natDegree_eq_of_crossing_cancel_sides
      hfg hno hf hg hdeg hleft_cancel_lt hright_lt_cancel)

/-- Compatible caller boundary for the equal-degree crossing-side
case.  Compatibility supplies positive-combination real-rootedness in the
no-common nonconstant regime; the two local cancellation-side hypotheses remain
explicit. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_eq_of_crossing_cancel_sides
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcompat : Compatible f g)
    (hdeg : f.natDegree = g.natDegree)
    (hleft_cancel_lt : ∀ x a b : ℝ, a < x → x < b →
      f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
        -f.leadingCoeff / g.leadingCoeff < μ)
    (hright_lt_cancel : ∀ x a b : ℝ, a < x → x < b →
      g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
        μ < -f.leadingCoeff / g.leadingCoeff) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_eq_of_crossing_cancel_sides hsgn
    (posComboRealRooted_of_compatible_noCommon_nonconstant hcompat hno hg hg_deg)
    hf hg hf_deg hg_deg hsimple_f hsimple_g hno hdeg
    hleft_cancel_lt hright_lt_cancel

/-- Caller boundary for Liu's finite count descent from parameter-bound and
zero-end degree-constancy data.  This is a convenience wrapper for callers
already living at `OppositeLeadingSigns.crossOwnedNotOddGaps_of_parameter_bounds`;
new analytic proofs should usually target the endpoint count-difference or
open-gap no-root boundaries directly. -/
theorem theorem21RootCountBranches_of_parameter_bounds
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegL_inv : ∀ x η : ℝ, η ∈ Set.Icc (0 : ℝ) (νL x)⁻¹ →
      (g + C η * f).natDegree = (g + C (0 : ℝ) * f).natDegree)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegR_zero : ∀ x η : ℝ, η ∈ Set.Icc (0 : ℝ) (νR x) →
      (f + C η * g).natDegree = (f + C (0 : ℝ) * g).natDegree) :
    theorem21RootCountBranches f g := by
  exact theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_parameter_bounds
      hfg hno hf hg νL νR hνL_pos hνL_large hdegL hdegL_inv
      hνR_pos hνR_small hdegR hdegR_zero)

/-- Caller boundary for the finite Liu count descent from stronger one-sided
strict-upper `≤ 1` root-count bounds.  The raw largest-root witnesses and
multiplicity-one root-count assumptions are supplied from nonconstant splitting
endpoints and `HasSimpleRoots`.  Prefer `theorem21RootCountBranches_of_crossOwned`
when the available input is the cross-owned finite-gap predicate. -/
theorem theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hupper_fg : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hupper_gf : ∀ x : ℝ, ¬ g.IsRoot x → ¬ f.IsRoot x →
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ := exists_largestRoots hf hg hsgn hf_deg hg_deg
  exact theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned_consecutive_roots
    hsgn.left_ne_zero hsgn.right_ne_zero hr hs hupper_fg hupper_gf
    (fun _ hc => hsimple_f.roots_count_eq_one hc)
    (fun _ hc => hsimple_g.roots_count_eq_one hc)
    hno hcross

/-- Opposite-sign caller boundary for the finite Liu count descent.  Compatible
root counts supply the two one-sided strict-upper bounds needed by the direct
one-sided theorem. -/
theorem theorem21RootCountBranches_of_rootCountCompatible_of_crossOwned
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcount : RootCountCompatible f g)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned hsgn hf hg
    hf_deg hg_deg
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hsgn.left_ne_zero hsgn.right_ne_zero hfx hgx)
    (fun _ hgx hfx => hcount.symm.rootCountAbove_left_sub_le_one_of_nonRoot
      hsgn.right_ne_zero hsgn.left_ne_zero hgx hfx)
    hsimple_f hsimple_g hno hcross

/-- Explicit large-parameter fallback for the endpoint-shaped `g`/`g`
contradiction in Liu's odd-indexed interval argument.  If the transported
right-family count drop reaches a parameter whose endpoint strict-upper counts
agree with those of `f`, then same-owner `g`-endpoints contradict the fact that
`f` has no roots in `(a, b]`.

The paper-route proof should normally use a small-parameter/downward-transport
version of this statement instead; this theorem keeps the already-proved
large-parameter form available under explicit hypotheses. -/
theorem OppositeLeadingSigns.false_of_right_roots_add_right_large_count_eq_left
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → μ ≤ ν)
    (hdeg_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc μ ν,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (ha_eq : ((f + C ν * g).roots.filter (a < ·)).card =
      (f.roots.filter (a < ·)).card)
    (hb_eq : ((f + C ν * g).roots.filter (b < ·)).card =
      (f.roots.filter (b < ·)).card) :
    False := by
  obtain ⟨μ, hμ_pos, hμ_root, _hdrop, hdrop_le⟩ :=
    hsgn.exists_pos_crossing_add_right_Ioo_right_roots_gt_drop_two_le
      hfg hno hf hg hga hgb hf_no hg_no hax hxb hay hyb hnot_odd
  have hdropν :
      ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C ν * g).roots.filter (a < ·)).card :=
    hdrop_le ν (hν_large μ hμ_pos hμ_root) (hdeg_large μ hμ_pos hμ_root)
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hf_no_Icc : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z :=
    hno.symm.right_not_isRoot_Icc_of_left_roots hga hgb hf_no
  exact false_of_add_right_count_drop_of_count_sub_eq_no_isRoot_Icc
    hab hf_no_Icc hdropν (by rw [ha_eq, hb_eq]; simp)

end LiuOppositeSigns
end RealRooted
