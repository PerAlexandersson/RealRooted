import RealRooted.Tactic.OperatorPreservesInterlacing

open Polynomial

namespace RealRooted
namespace Tactic

example {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesAllComboPairs T := by
  rr_operator_all_combo_preserver using preserves := hT

example {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]}
    (hT : PreservesRealRootedOrZero T) (hall : AllComboRealRooted f g) :
    AllComboRealRooted (T f) (T g) := by
  rr_operator_all_combo using preserves := hT, all_combo := hall

example {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesInterlacingPairsUpToOrder0 T := by
  rr_operator_interlaces_up_to_order0 using preserves := hT

example {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]}
    (hT : PreservesRealRootedOrZero T) (hfg : Prec f g) :
    Prec0 (T f) (T g) ∨ Prec0 (T g) (T f) := by
  rr_operator_prec0_up_to_order using preserves := hT, prec := hfg

end Tactic
end RealRooted
