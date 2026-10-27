import RealRooted.Tactic.MaWang.Sequences

/-!
# Ma--Wang weak-sequence regression examples

Generic weak derivative-sequence tests, including the complete inferred
certificate and ascribed-normalizer regression scope.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- A globally nonpositive derivative factor needs no root-window certificate. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    deriv_factor := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi


end Tactic
end RealRooted
