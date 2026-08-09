import RealRooted.LiuOppositeSigns.PositiveSplitPair

/-!
# Liu deletion-branch transport

This module keeps Liu's left and right deletion branches together with
the branch-retaining common-interleaver package.  The later factor-return
statement and assembly layers remain in `RealRooted.LiuOppositeSignsTheorem`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

namespace LeftRootCountBranch

/-- A left Liu branch gives a common-right-interleaver witness for the actual
deletion pair `(deleteRootFactor f r, g)`, after stripping the sign
normalization used to make leading coefficients positive. -/
theorem deletePairHasCommonInterleaver {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k := by
  rcases h.positiveSplitDeletionCount hsgn hf_splits hg_splits with hpos | hpos
  · exact hpos.pairHasCommonInterleaver_of_neg_right
  · exact hpos.pairHasCommonInterleaver_of_neg_left

/-- After translating by the restored largest root, the sign-normalized left
deletion pair has nonnegative coefficients. -/
theorem positiveDeletionPair_comp_X_add_C_hasNonnegCoeffs
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    (HasNonnegCoeffs ((deleteRootFactor f r).comp (X + C r)) ∧
        HasNonnegCoeffs ((-g).comp (X + C r))) ∨
      (HasNonnegCoeffs ((-(deleteRootFactor f r)).comp (X + C r)) ∧
        HasNonnegCoeffs (g.comp (X + C r))) := by
  have hroots :=
    h.deletionPair_roots_le_left_largest hsgn.left_ne_zero
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    refine ⟨?_, ?_⟩
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (h.delete_splits hf_splits) hroots.1
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg_splits.neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
  · right
    refine ⟨?_, ?_⟩
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (h.delete_splits hf_splits).neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg_splits hroots.2

/-- A supplied common-right-interleaver witness for the actual left deletion
pair gives compatibility of the sign-normalized deletion pair. -/
theorem positiveDeletionPair_compatible_of_commonInterleaver
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) :
    Compatible (deleteRootFactor f r) (-g) ∨
      Compatible (-(deleteRootFactor f r)) g := by
  rcases hcommon with ⟨k, hqk, hgk⟩
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    have hneg_gk : Prec (-g) k := by
      have hscale : Prec (C (-1 : ℝ) * g) k :=
        prec_C_mul_left hgk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hqk hneg_gk hpos.1 hpos.2
  · right
    have hneg_qk : Prec (-(deleteRootFactor f r)) k := by
      have hscale : Prec (C (-1 : ℝ) * deleteRootFactor f r) k :=
        prec_C_mul_left hqk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hneg_qk hgk hpos.1 hpos.2

/-- To prove all-combinations real-rootedness for a left branch, it is enough
to prove the translated target after restoring the deleted factor as `X`. -/
theorem allComboRealRooted_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hall : AllComboRealRooted
      (X * (deleteRootFactor f r).comp (X + C r)) (g.comp (X + C r))) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_comp_X_add_C r <| by
    simpa [h.left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hall

/-- Sign-normalized translated all-combinations data are enough to restore the
original left branch. -/
theorem allComboRealRooted_of_positiveTranslatedRestore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hall : AllComboRealRooted
        (X * (deleteRootFactor f r).comp (X + C r)) ((-g).comp (X + C r)) ∨
      AllComboRealRooted
        (X * (-(deleteRootFactor f r)).comp (X + C r)) (g.comp (X + C r))) :
    AllComboRealRooted f g := by
  apply h.allComboRealRooted_of_translated_restore
  rcases hall with hall | hall
  · simpa using hall.neg_right
  · simpa [mul_neg] using hall.neg_left

/-- To prove compatibility for a left branch, it is enough to prove the
translated target after restoring the deleted factor as `X`. -/
theorem compatible_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hcompat : Compatible
      (X * (deleteRootFactor f r).comp (X + C r)) (g.comp (X + C r))) :
    Compatible f g :=
  Compatible.of_comp_X_add_C r <| by
    simpa [h.left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hcompat

end LeftRootCountBranch

namespace RightRootCountBranch

/-- A right Liu branch gives a common-right-interleaver witness for the actual
deletion pair `(f, deleteRootFactor g s)`, after stripping the sign
normalization used to make leading coefficients positive. -/
theorem deletePairHasCommonInterleaver {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k := by
  rcases h.positiveSplitDeletionCount hsgn hf_splits hg_splits with hpos | hpos
  · exact hpos.pairHasCommonInterleaver_of_neg_right
  · exact hpos.pairHasCommonInterleaver_of_neg_left

/-- After translating by the restored largest root, the sign-normalized right
deletion pair has nonnegative coefficients. -/
theorem positiveDeletionPair_comp_X_add_C_hasNonnegCoeffs
    {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    (HasNonnegCoeffs (f.comp (X + C s)) ∧
        HasNonnegCoeffs ((-(deleteRootFactor g s)).comp (X + C s))) ∨
      (HasNonnegCoeffs ((-f).comp (X + C s)) ∧
        HasNonnegCoeffs ((deleteRootFactor g s).comp (X + C s))) := by
  have hroots :=
    h.deletionPair_roots_le_right_largest hsgn.right_ne_zero
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    refine ⟨?_, ?_⟩
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1 hf_splits hroots.1
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.2 (h.delete_splits hg_splits).neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
  · right
    refine ⟨?_, ?_⟩
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1 hf_splits.neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.2 (h.delete_splits hg_splits) hroots.2

/-- A supplied common-right-interleaver witness for the actual right deletion
pair gives compatibility of the sign-normalized deletion pair. -/
theorem positiveDeletionPair_compatible_of_commonInterleaver
    {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    Compatible f (-(deleteRootFactor g s)) ∨
      Compatible (-f) (deleteRootFactor g s) := by
  rcases hcommon with ⟨k, hfk, hqk⟩
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    have hneg_qk : Prec (-(deleteRootFactor g s)) k := by
      have hscale : Prec (C (-1 : ℝ) * deleteRootFactor g s) k :=
        prec_C_mul_left hqk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hfk hneg_qk hpos.1 hpos.2
  · right
    have hneg_fk : Prec (-f) k := by
      have hscale : Prec (C (-1 : ℝ) * f) k :=
        prec_C_mul_left hfk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hneg_fk hqk hpos.1 hpos.2

/-- To prove all-combinations real-rootedness for a right branch, it is enough
to prove the translated target after restoring the deleted factor as `X`. -/
theorem allComboRealRooted_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hall : AllComboRealRooted (f.comp (X + C s))
      (X * (deleteRootFactor g s).comp (X + C s))) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_comp_X_add_C s <| by
    simpa [h.right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hall

/-- Sign-normalized translated all-combinations data are enough to restore the
original right branch. -/
theorem allComboRealRooted_of_positiveTranslatedRestore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hall : AllComboRealRooted (f.comp (X + C s))
        (X * (-(deleteRootFactor g s)).comp (X + C s)) ∨
      AllComboRealRooted ((-f).comp (X + C s))
        (X * (deleteRootFactor g s).comp (X + C s))) :
    AllComboRealRooted f g := by
  apply h.allComboRealRooted_of_translated_restore
  rcases hall with hall | hall
  · simpa [mul_neg] using hall.neg_right
  · simpa using hall.neg_left

/-- To prove compatibility for a right branch, it is enough to prove the
translated target after restoring the deleted factor as `X`. -/
theorem compatible_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hcompat : Compatible (f.comp (X + C s))
      (X * (deleteRootFactor g s).comp (X + C s))) :
    Compatible f g :=
  Compatible.of_comp_X_add_C s <| by
    simpa [h.right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hcompat

end RightRootCountBranch

/-- Liu branch data together with a common-right interleaver for the actual
deletion pair selected by that branch.  This keeps the largest-root/order
certificate that is lost in the fully sign-normalized compatibility package. -/
def theorem21DeletionPairCommonInterleaverBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (LeftRootCountBranch f g r s ∧
        ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) ∨
      (RightRootCountBranch f g r s ∧
        ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)

/-- Liu root-count branches produce common-right-interleaver witnesses for the
actual deletion pair in the selected branch. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21DeletionPairCommonInterleaverBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl
      ⟨hleft, hleft.deletePairHasCommonInterleaver
        hsgn hf_splits hg_splits⟩⟩
  · exact ⟨r, s, Or.inr
      ⟨hright, hright.deletePairHasCommonInterleaver
        hsgn hf_splits hg_splits⟩⟩

/-- The branch-retaining common-interleaver package forgets back to Liu's
root-count branches. -/
theorem theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
    {f g : ℝ[X]} (h : theorem21DeletionPairCommonInterleaverBranches f g) :
    theorem21RootCountBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl hleft.1⟩
  · exact ⟨r, s, Or.inr hright.1⟩

/-- With splitting and opposite-leading-sign hypotheses, Liu's root-count
branches are equivalent to the branch-retaining common-interleaver package. -/
theorem theorem21DeletionPairCommonInterleaverBranches_iff_rootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) :
    theorem21DeletionPairCommonInterleaverBranches f g ↔
      theorem21RootCountBranches f g :=
  ⟨theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches,
    theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf_splits hg_splits hsgn⟩

/-- Forward half of Liu Theorem 2.1, restated with branch-retaining
deletion-pair common-interleaver witnesses. -/
def theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21DeletionPairCommonInterleaverBranches f g

/-- Nonconstant forward half of Liu Theorem 2.1, restated with
branch-retaining deletion-pair common-interleaver witnesses. -/
def theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21DeletionPairCommonInterleaverBranches f g

/-- Reverse half of Liu Theorem 2.1, restated with branch-retaining
deletion-pair common-interleaver witnesses. -/
def theorem21DeletionPairCommonInterleaverBranchesToCompatibleStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21DeletionPairCommonInterleaverBranches f g → Compatible f g

/-- Nonconstant reverse half of Liu Theorem 2.1, restated with
branch-retaining deletion-pair common-interleaver witnesses. -/
def theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21DeletionPairCommonInterleaverBranches f g → Compatible f g

/-- The isolated forward root-count direction supplies the branch-retaining
common-interleaver forward direction. -/
theorem theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement := by
  intro f g hf hg hsgn hcompat
  exact theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    hf hg hsgn (hforward hf hg hsgn hcompat)

/-- The branch-retaining common-interleaver forward direction forgets back to
the root-count forward direction. -/
theorem theorem21CompatibleToRootCountBranches_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleToRootCountBranchesStatement := by
  intro f g hf hg hsgn hcompat
  exact theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
    (hforward hf hg hsgn hcompat)

/-- The branch-retaining common-interleaver reverse direction restricts to the
nonconstant setting. -/
theorem
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstant_of_reverse
    (hreverse :
      theorem21DeletionPairCommonInterleaverBranchesToCompatibleStatement) :
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hbranches

/-- The isolated reverse root-count direction supplies the branch-retaining
common-interleaver reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverBranchesToCompatible_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  exact hreverse hf hg hsgn
    (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      hbranches)

/-- The isolated nonconstant reverse root-count direction supplies the
branch-retaining common-interleaver reverse direction. -/
theorem
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstant_of_rootCountReverse
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement) :
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact hreverse hf hg hsgn hf_deg hg_deg
    (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      hbranches)

/-- Liu Theorem 2.1 restated with branch-retaining deletion-pair
common-interleaver witnesses. -/
def theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g)

/-- Nonconstant Liu Theorem 2.1 restated with branch-retaining deletion-pair
common-interleaver witnesses. -/
def theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g)

/-- Reassemble the branch-retaining common-interleaver theorem package from
its isolated forward and reverse directions. -/
theorem theorem21CompatibleDeletionPairCommonInterleaverBranches_of_forward_and_reverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21DeletionPairCommonInterleaverBranchesToCompatibleStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement := by
  unfold theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Reassemble the nonconstant branch-retaining common-interleaver theorem
package from its isolated forward and reverse directions. -/
theorem
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstant_of_forward_and_reverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstantStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement := by
  unfold theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement
  intro f g hf hg hsgn hf_deg hg_deg
  exact ⟨hforward hf hg hsgn hf_deg hg_deg,
    hreverse hf hg hsgn hf_deg hg_deg⟩

/-- Liu's root-count theorem package gives the branch-retaining deletion-pair
common-interleaver iff package. -/
theorem theorem21DeletionPairCommonInterleaverIff_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21CompatibleDeletionPairCommonInterleaverBranches_of_forward_and_reverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount
        h))
    (theorem21DeletionPairCommonInterleaverBranchesToCompatible_of_reverse
      (theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount
        h))

/-- The branch-retaining deletion-pair common-interleaver iff implies Liu's
root-count theorem package. -/
theorem theorem21CompatibleRootCount_of_deletionPairCommonInterleaverIff
    (h :
      theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountStatement := by
  intro f g hf hg hsgn
  constructor
  · intro hcompat
    exact theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      ((h f g hf hg hsgn).1 hcompat)
  · intro hbranches
    exact (h f g hf hg hsgn).2
      (theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
        hf hg hsgn hbranches)

end LiuOppositeSigns
end RealRooted
