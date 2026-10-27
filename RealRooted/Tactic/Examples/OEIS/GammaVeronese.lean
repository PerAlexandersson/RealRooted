import RealRooted.Tactic.VeroneseSection

/-!
# OEIS Veronese router regression example

Veronese-section certificate routing coverage for the OEIS facade.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Veronese-section row-family PF exit exposed through the OEIS facade. -/
example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      IsPolyaFreqSeq (veroneseSectionPolynomial (r n) (k n) (P n)).coeff := by
  rr_veronese_section_sequence_pf_coeff using
    pf_coeff := hpf,
    r_pos := hr,
    k_lt_r := hk

end Tactic
end RealRooted
