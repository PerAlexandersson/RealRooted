import RealRooted.Tactic.MaWang.Factors

/-!
# Ma--Wang factor-window regression examples

Regression examples for Ma--Wang factor-window frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Inner-window shell:
`P_{n+2}=U_nP_{n+1}+X(1+X)P'_{n+1}`, with roots in `[-1,0]`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_X_one_add_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- `A059340`: a globally nonpositive shifted-square derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-((1 + X : ℝ[X]) ^ 2)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_global_nonpos_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    deriv_factor := fun _ => -((1 + X : ℝ[X]) ^ 2),
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi


end Tactic
end RealRooted
