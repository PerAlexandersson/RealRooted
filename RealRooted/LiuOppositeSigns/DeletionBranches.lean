import RealRooted.LiuOppositeSigns.PositiveSplitPair
import RealRooted.LiuOppositeSigns.RootCountBranches.Interfaces

/-!
# Liu deletion-branch transport

This module restores compatibility of a pair from the translated deletion pair
selected by Liu's left or right root-count branch.  The factor-return proof of
the reverse direction is in `RealRooted.LiuOppositeSigns.FactorReturnAssembly`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

namespace LeftRootCountBranch

theorem compatible_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hcompat : Compatible
      (X * (deleteRootFactor f r).comp (X + C r)) (g.comp (X + C r))) :
    Compatible f g :=
  Compatible.of_comp_X_add_C r <| by
    simpa [h.left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hcompat

end LeftRootCountBranch

namespace RightRootCountBranch

theorem compatible_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hcompat : Compatible (f.comp (X + C s))
      (X * (deleteRootFactor g s).comp (X + C s))) :
    Compatible f g :=
  Compatible.of_comp_X_add_C s <| by
    simpa [h.right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hcompat

end RightRootCountBranch

end LiuOppositeSigns
end RealRooted
