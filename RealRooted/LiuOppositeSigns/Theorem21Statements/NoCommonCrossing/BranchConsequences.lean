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

end LiuOppositeSigns
end RealRooted
