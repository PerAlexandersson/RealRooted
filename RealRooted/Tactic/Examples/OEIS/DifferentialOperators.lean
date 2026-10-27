import RealRooted.Tactic.Wagner

/-!
# OEIS Wagner regression example

Regression coverage for the Wagner frontend used by the OEIS facade.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Wagner common-left addition row-family exit exposed through the OEIS
facade. -/
example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hHF : ∀ n : Nat, StrictInterl (H n) (F n))
    (hHG : ∀ n : Nat, StrictInterl (H n) (G n)) :
    ∀ n : Nat, StrictInterl (H n) (F n + G n) := by
  rr_wagner_common_left_add_sequence using
    left := hF,
    right := hG,
    common_interlaces_left := hHF,
    common_interlaces_right := hHG

end Tactic
end RealRooted
