module

public import RealRooted.OperatorPreservesInterlacing

/-!
# Operator-preservation tactic frontends

Thin wrappers for the Obreschkoff consequence that a linear operator preserving
real-rootedness up to zero preserves interlacing pairs up to order.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- A linear operator preserving real-rootedness up to zero sends every pointwise
`AllComboRealRooted` pair to another such pair. -/
theorem operator_allCombo_sequence {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    {F G : Nat → ℝ[X]}
    (hT : PreservesRealRootedOrZero T)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (T (F i)) (T (G i)) := fun i =>
  preservesAllComboPairs_of_preservesRealRootedOrZero hT (hall i)

/-- An interlacing-pair preserver sends every pointwise strictly interlacing pair to an
`Interl` pair in one of the two orientations. -/
theorem operator_interl_sequence_of_interlacing_preserver
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {F G : Nat → ℝ[X]}
    (hT : PreservesInterlacingPairsUpToOrder0 T)
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i)) :
    ∀ i : Nat, Interl (T (F i)) (T (G i)) ∨ Interl (T (G i)) (T (F i)) :=
  fun i =>
    hT (hfg i)

/-- A linear operator preserving real-rootedness up to zero sends every pointwise strictly
interlacing pair to an `Interl` pair in one of the two orientations. -/
theorem operator_interl_sequence_up_to_order
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {F G : Nat → ℝ[X]}
    (hT : PreservesRealRootedOrZero T)
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i)) :
    ∀ i : Nat, Interl (T (F i)) (T (G i)) ∨ Interl (T (G i)) (T (F i)) :=
  operator_interl_sequence_of_interlacing_preserver
    (preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero hT) hfg

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
