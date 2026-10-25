module

public import RealRooted.OperatorPreservesInterlacing

/-!
# Operator-preservation tactic frontends

Thin wrappers for the Obreschkoff consequence that a linear operator preserving
real-rootedness up to zero preserves interlacing pairs up to order.
-/

@[expose] public section

open Polynomial

namespace RealRooted
namespace Tactic

theorem operator_allCombo_sequence {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    {F G : Nat → ℝ[X]}
    (hT : PreservesRealRootedOrZero T)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (T (F i)) (T (G i)) := fun i =>
  preservesAllComboPairs_of_preservesRealRootedOrZero hT (hall i)

theorem operator_interl_sequence_of_interlacing_preserver
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {F G : Nat → ℝ[X]}
    (hT : PreservesInterlacingPairsUpToOrder0 T)
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i)) :
    ∀ i : Nat, Interl (T (F i)) (T (G i)) ∨ Interl (T (G i)) (T (F i)) :=
  fun i =>
    hT (hfg i)

theorem operator_interl_sequence_up_to_order
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {F G : Nat → ℝ[X]}
    (hT : PreservesRealRootedOrZero T)
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i)) :
    ∀ i : Nat, Interl (T (F i)) (T (G i)) ∨ Interl (T (G i)) (T (F i)) :=
  operator_interl_sequence_of_interlacing_preserver
    (preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero hT) hfg

/-- Closes `PreservesAllComboPairs T` from `preserves : PreservesRealRootedOrZero T`. -/
syntax (name := rr_operator_all_combo_preserver_named)
  "rr_operator_all_combo_preserver" " using "
    "preserves" ":=" term :
  tactic

/-- Closes `AllComboRealRooted (T f) (T g)` from `preserves : PreservesRealRootedOrZero T` and
`all_combo : AllComboRealRooted f g`. -/
syntax (name := rr_operator_all_combo_named)
  "rr_operator_all_combo" " using "
    "preserves" ":=" term ","
    "all_combo" ":=" term :
  tactic

/-- Sequence form of `rr_operator_all_combo`: closes `∀ i, AllComboRealRooted (T (F i)) (T (G
i))`. -/
syntax (name := rr_operator_all_combo_sequence_named)
  "rr_operator_all_combo_sequence" " using "
    "preserves" ":=" term ","
    "all_combo" ":=" term :
  tactic

/-- Closes `PreservesInterlacingPairsUpToOrder0 T` from
`preserves : PreservesRealRootedOrZero T`. -/
syntax (name := rr_operator_interlaces_up_to_order0_named)
  "rr_operator_interlaces_up_to_order0" " using "
    "preserves" ":=" term :
  tactic

/-- Closes `∀ i, Interl (T (F i)) (T (G i)) ∨ Interl (T (G i)) (T (F i))` from
`interlacing_preserver : PreservesInterlacingPairsUpToOrder0 T` and
`strictInterl : ∀ i, StrictInterl (F i) (G i)`. -/
syntax (name := rr_operator_interl_sequence_of_preserver_named)
  "rr_operator_interl_sequence_of_preserver" " using "
    "interlacing_preserver" ":=" term ","
    "strictInterl" ":=" term :
  tactic

/-- Closes `Interl (T f) (T g) ∨ Interl (T g) (T f)` from
`preserves : PreservesRealRootedOrZero T` and `strictInterl : StrictInterl f g`. -/
syntax (name := rr_operator_interl_up_to_order_named)
  "rr_operator_interl_up_to_order" " using "
    "preserves" ":=" term ","
    "strictInterl" ":=" term :
  tactic

/-- Sequence form of `rr_operator_interl_up_to_order`: closes `∀ i, Interl (T (F i)) (T (G i)) ∨
Interl (T (G i)) (T (F i))`. -/
syntax (name := rr_operator_interl_sequence_up_to_order_named)
  "rr_operator_interl_sequence_up_to_order" " using "
    "preserves" ":=" term ","
    "strictInterl" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_operator_all_combo_preserver using
        preserves := $hT:term) =>
      `(tactic|
        exact RealRooted.preservesAllComboPairs_of_preservesRealRootedOrZero $hT)
  | `(tactic|
      rr_operator_all_combo using
        preserves := $hT:term,
        all_combo := $hall:term) =>
      `(tactic|
        exact RealRooted.preservesAllComboPairs_of_preservesRealRootedOrZero
          $hT $hall)
  | `(tactic|
      rr_operator_all_combo_sequence using
        preserves := $hT:term,
        all_combo := $hall:term) =>
      `(tactic|
        exact RealRooted.Tactic.operator_allCombo_sequence $hT $hall)
  | `(tactic|
      rr_operator_interlaces_up_to_order0 using
        preserves := $hT:term) =>
      `(tactic|
        exact RealRooted.preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
          $hT)
  | `(tactic|
      rr_operator_interl_sequence_of_preserver using
        interlacing_preserver := $hT:term,
        strictInterl := $hfg:term) =>
      `(tactic|
        exact RealRooted.Tactic.operator_interl_sequence_of_interlacing_preserver
          $hT $hfg)
  | `(tactic|
      rr_operator_interl_up_to_order using
        preserves := $hT:term,
        strictInterl := $hfg:term) =>
      `(tactic|
        exact RealRooted.preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
          $hT $hfg)
  | `(tactic|
      rr_operator_interl_sequence_up_to_order using
        preserves := $hT:term,
        strictInterl := $hfg:term) =>
      `(tactic|
        exact RealRooted.Tactic.operator_interl_sequence_up_to_order
          $hT $hfg)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
