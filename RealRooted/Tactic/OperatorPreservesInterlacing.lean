import RealRooted.OperatorPreservesInterlacing

/-!
# Operator-preservation tactic frontends

Thin wrappers for the Obreschkoff consequence that a linear operator preserving
real-rootedness up to zero preserves interlacing pairs up to order.
-/

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

syntax (name := rr_operator_all_combo_preserver_named)
  "rr_operator_all_combo_preserver" " using "
    "preserves" ":=" term :
  tactic

syntax (name := rr_operator_all_combo_named)
  "rr_operator_all_combo" " using "
    "preserves" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_operator_all_combo_sequence_named)
  "rr_operator_all_combo_sequence" " using "
    "preserves" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_operator_interlaces_up_to_order0_named)
  "rr_operator_interlaces_up_to_order0" " using "
    "preserves" ":=" term :
  tactic

syntax (name := rr_operator_interl_sequence_of_preserver_named)
  "rr_operator_interl_sequence_of_preserver" " using "
    "interlacing_preserver" ":=" term ","
    "strictInterl" ":=" term :
  tactic

syntax (name := rr_operator_interl_up_to_order_named)
  "rr_operator_interl_up_to_order" " using "
    "preserves" ":=" term ","
    "strictInterl" ":=" term :
  tactic

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

/- Parser compatibility for the pre-#984 Prec/Prec0 tactic surface.
    Canonical syntax is preferred; these declarations retain old scripts
    and dispatch through the deprecated theorem aliases above. -/
namespace RealRooted
namespace Tactic
syntax (name := rr_operator_prec0_sequence_of_preserver_named_legacy)
  "rr_operator_prec0_sequence_of_preserver" " using "
    "interlacing_preserver" ":=" term ","
    "prec" ":=" term :
  tactic

syntax (name := rr_operator_prec0_up_to_order_named_legacy)
  "rr_operator_prec0_up_to_order" " using "
    "preserves" ":=" term ","
    "prec" ":=" term :
  tactic

syntax (name := rr_operator_prec0_sequence_up_to_order_named_legacy)
  "rr_operator_prec0_sequence_up_to_order" " using "
    "preserves" ":=" term ","
    "prec" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_operator_prec0_sequence_of_preserver using
        interlacing_preserver := $hT:term,
        prec := $hfg:term) =>
      `(tactic|
        exact RealRooted.Tactic.operator_interl_sequence_of_interlacing_preserver
          $hT $hfg)
  | `(tactic|
      rr_operator_prec0_up_to_order using
        preserves := $hT:term,
        prec := $hfg:term) =>
      `(tactic|
        exact RealRooted.preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
          $hT $hfg)
  | `(tactic|
      rr_operator_prec0_sequence_up_to_order using
        preserves := $hT:term,
        prec := $hfg:term) =>
      `(tactic|
        exact RealRooted.Tactic.operator_interl_sequence_up_to_order
          $hT $hfg)
end Tactic
end RealRooted
