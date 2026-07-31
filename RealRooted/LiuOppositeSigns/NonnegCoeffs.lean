import RealRooted.LiuOppositeSigns
import RealRooted.WagnerX

/-!
# Nonnegative coefficients for Liu root deletion

This leaf module keeps the heavier Wagner coefficient/root API out of the core
Liu opposite-sign file while providing the cofactor nonnegativity transport
needed by common-root deletion arguments.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

/-- Deleting one real root from a nonnegative-coefficient real-rooted
polynomial with positive leading coefficient preserves nonnegative
coefficients. -/
theorem HasNonnegCoeffs.deleteRootFactor_of_isRoot
    {p : ℝ[X]} {r : ℝ} (hp_nonneg : HasNonnegCoeffs p)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hr : p.IsRoot r) :
    HasNonnegCoeffs (deleteRootFactor p r) := by
  have hdelete_ne : deleteRootFactor p r ≠ 0 :=
    deleteRootFactor_ne_zero_of_isRoot hp_ne hr
  have hdelete_splits : (deleteRootFactor p r).Splits :=
    deleteRootFactor_splits_of_isRoot hp_splits hr
  have hdelete_pos : HasPosLeadingCoeff (deleteRootFactor p r) := by
    simpa [HasPosLeadingCoeff,
      leadingCoeff_deleteRootFactor_of_isRoot hp_ne hr]
      using hp_nonneg.pos_leadingCoeff hp_ne
  have hdiv : deleteRootFactor p r ∣ p := by
    refine ⟨X - C r, ?_⟩
    rw [mul_comm, factor_deleteRootFactor_of_isRoot hr]
  exact hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
    hp_ne hp_splits hp_nonneg hdelete_ne hdelete_splits hdelete_pos hdiv

/-- The left cofactor of a positive-split pair inherits nonnegative
coefficients from the left endpoint. -/
theorem PositiveSplitRootCountPair.left_deleteRootFactor_nonneg
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) {r : ℝ} (hr : p.IsRoot r) :
    HasNonnegCoeffs (deleteRootFactor p r) :=
  HasNonnegCoeffs.deleteRootFactor_of_isRoot hp_nonneg
    h.left_pos.ne_zero h.left_splits hr

/-- The right cofactor of a positive-split pair inherits nonnegative
coefficients from the right endpoint. -/
theorem PositiveSplitRootCountPair.right_deleteRootFactor_nonneg
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hq_nonneg : HasNonnegCoeffs q) {r : ℝ} (hr : q.IsRoot r) :
    HasNonnegCoeffs (deleteRootFactor q r) :=
  HasNonnegCoeffs.deleteRootFactor_of_isRoot hq_nonneg
    h.right_pos.ne_zero h.right_splits hr

end LiuOppositeSigns
end RealRooted
