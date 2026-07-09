import RealRooted.CommonInterleaverTwo
import RealRooted.LiuOppositeSigns

/-!
# Liu opposite-sign compatibility theorem targets

This module connects the lightweight root-count scaffolding in
`RealRooted.LiuOppositeSigns` to the existing `Compatible` API.  The hard
mathematical content of Lily L. Liu's Theorem 2.1 is kept as a named statement
so later proof work can target a stable interface.
-/

open Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- Liu Theorem 2.1, stated against the project's `Compatible` predicate:
for two real-rooted polynomials with opposite leading signs, compatibility is
equivalent to the appropriate largest-root deletion branch satisfying Liu's
closed-at-or-above root-count condition. -/
def theorem21CompatibleRootCountStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Projection form of `theorem21CompatibleRootCountStatement`. -/
theorem compatible_iff_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn

/-- Forward direction of Liu Theorem 2.1 as a reusable projection. -/
theorem theorem21RootCountBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  (h f g hf hg hsgn).1 hcompat

/-- Reverse direction of Liu Theorem 2.1 as a reusable projection. -/
theorem compatible_of_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  (h f g hf hg hsgn).2 hbranches

/-- Forward direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_of_compatible h hg hf hsgn.symm hcompat.comm

/-- Reverse direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches h hg hf hsgn.symm hbranches).comm

/-- Projection form of Liu Theorem 2.1 after swapping the two polynomials. -/
theorem compatible_iff_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches g f :=
  ⟨theorem21RootCountBranches_symm_of_compatible h hf hg hsgn,
    compatible_of_theorem21RootCountBranches_symm h hf hg hsgn⟩

/-- Liu Corollary 2.2: compatible real-rooted polynomials with opposite leading
signs have degree gap at most two. -/
def corollary22DegreeDiffStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Projection form of `corollary22DegreeDiffStatement`. -/
theorem corollary22DegreeDiff
    (h : corollary22DegreeDiffStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hcompat

/-- Liu Corollary 2.2 follows from the Theorem 2.1 compatibility criterion. -/
theorem corollary22DegreeDiff_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    corollary22DegreeDiffStatement :=
  fun _ _ hf hg hsgn hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff (corollary22DegreeDiff_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- Direct degree-gap consequence via the swapped branch projection of
Liu Theorem 2.1. -/
theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible h hf hg hsgn hcompat)

end LiuOppositeSigns
end RealRooted
