import RealRooted.CommonInterleaver.RightPencil
import RealRooted.LiuOppositeSigns
import RealRooted.LiuOppositeSigns.NoCommonRoots

/-!
# Common-root deletion for Liu's opposite-sign theorem

This module isolates the algebraic reduction that deletes a shared linear
factor and restores the original compatible pair afterward.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Multiplying both entries by the same splitting factor preserves
compatibility. -/
theorem compatible_mul_common_factor {d f g : ℝ[X]}
    (hd : d.Splits) (h : Compatible f g) :
    Compatible (d * f) (d * g) := by
  intro α β hα hβ
  have hfactor :
      C α * (d * f) + C β * (d * g) = d * (C α * f + C β * g) := by
    ring
  rcases h α β hα hβ with hzero | hrr
  · exact Or.inl (by rw [hfactor, hzero, mul_zero])
  · by_cases hprod_zero : C α * (d * f) + C β * (d * g) = 0
    · exact Or.inl hprod_zero
    · exact Or.inr ⟨hprod_zero, by rw [hfactor]; exact hd.mul hrr.2⟩

/-- If two compatible polynomials have a common root, deleting that shared
linear factor preserves compatibility. -/
theorem compatible_deleteRootFactor_of_common_root {f g : ℝ[X]} {r : ℝ}
    (h : Compatible f g) (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    Compatible (deleteRootFactor f r) (deleteRootFactor g r) := by
  intro α β hα hβ
  let df : ℝ[X] := deleteRootFactor f r
  let dg : ℝ[X] := deleteRootFactor g r
  let combo : ℝ[X] :=
    C α * df + C β * dg
  change combo = 0 ∨ (combo ≠ 0 ∧ combo.Splits)
  have hf_def : f = (X - C r) * df := by
    simpa [df] using (factor_deleteRootFactor_of_isRoot hrf).symm
  have hg_def : g = (X - C r) * dg := by
    simpa [dg] using (factor_deleteRootFactor_of_isRoot hrg).symm
  have hfactor :
      C α * f + C β * g = (X - C r) * combo := by
    dsimp [combo]
    rw [hf_def, hg_def]
    ring_nf
  have hcase :
      (X - C r) * combo = 0 ∨
        ((X - C r) * combo ≠ 0 ∧ ((X - C r) * combo).Splits) := by
    simpa [hfactor] using h α β hα hβ
  rcases hcase with hzero | hrr
  · rcases mul_eq_zero.mp hzero with hlinear_zero | hcombo_zero
    · exact False.elim (X_sub_C_ne_zero r hlinear_zero)
    · exact Or.inl hcombo_zero
  · refine Or.inr ⟨?_, ?_⟩
    · intro hcombo_zero
      exact hrr.1 (by rw [hcombo_zero, mul_zero])
    · exact
        (splits_mul_iff_right (X_sub_C_ne_zero r)
          (Polynomial.Splits.X_sub_C r)).mp hrr.2

/-- Common-root branch for the unreduced Liu statement: peel one common
linear factor and require compatibility of the cofactors. -/
def CommonRootDeletionCompatibleBranch (f g : ℝ[X]) : Prop :=
  ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r ∧
    Compatible (deleteRootFactor f r) (deleteRootFactor g r)

namespace CommonRootDeletionCompatibleBranch

theorem compatible {f g : ℝ[X]}
    (h : CommonRootDeletionCompatibleBranch f g) :
    Compatible f g := by
  rcases h with ⟨r, hfr, hgr, hcompat⟩
  have hmul :=
    compatible_mul_common_factor
      (d := X - C r)
      (Polynomial.Splits.X_sub_C r)
      hcompat
  have hf_def : (X - C r) * deleteRootFactor f r = f :=
    factor_deleteRootFactor_of_isRoot hfr
  have hg_def : (X - C r) * deleteRootFactor g r = g :=
    factor_deleteRootFactor_of_isRoot hgr
  simpa [hf_def, hg_def] using hmul

/-- Compatible polynomials with a common root satisfy the common-root deletion
branch. -/
theorem of_compatible_of_not_noCommonRoots {f g : ℝ[X]}
    (hcompat : Compatible f g) (hno : ¬ NoCommonRoots f g) :
    CommonRootDeletionCompatibleBranch f g := by
  rcases exists_common_root_of_not_noCommonRoots hno with ⟨r, hfr, hgr⟩
  exact ⟨r, hfr, hgr,
    compatible_deleteRootFactor_of_common_root hcompat hfr hgr⟩

end CommonRootDeletionCompatibleBranch

/-- Corrected unreduced branch predicate: either Liu's no-common largest-root
branch holds, or a common root can be peeled and the cofactors are compatible.
-/
def theorem21RootCountBranchesWithCommon (f g : ℝ[X]) : Prop :=
  theorem21RootCountBranches f g ∨ CommonRootDeletionCompatibleBranch f g

/-- Reduced common-root branch predicate.  In the ordinary root-count branch we
remember the no-common-root hypothesis, so no-common reverse statements can be
used after splitting off the common-root case. -/
def theorem21RootCountBranchesReduced (f g : ℝ[X]) : Prop :=
  (NoCommonRoots f g ∧ theorem21RootCountBranches f g) ∨
    CommonRootDeletionCompatibleBranch f g

namespace theorem21RootCountBranchesReduced

/-- Forget the extra no-common-root witness in the reduced branch predicate. -/
theorem withCommon {f g : ℝ[X]}
    (h : theorem21RootCountBranchesReduced f g) :
    theorem21RootCountBranchesWithCommon f g := by
  rcases h with hbranches | hcommon
  · exact Or.inl hbranches.2
  · exact Or.inr hcommon

end theorem21RootCountBranchesReduced

end LiuOppositeSigns
end RealRooted
