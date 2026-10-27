import RealRooted.Tactic.MaWang.Factors

/-!
# Ma--Wang X-factor sequence regression examples

Regression examples for X-factor Ma--Wang sequence frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Touchard/Bell base shell: `P_{n+2}=U_nP_{n+1}+X P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Strict-degree shortcut for the `X P'` Ma--Wang sequence shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ

/-- The strict-degree Ma--Wang shell feeds the generic interlacing finish. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  have hstrictInterl : ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
    rr_mw_derivative_X_sequence_nonneg using
      base := hbase,
      pos_lc := hpos,
      nonneg_coeffs := hnonneg,
      recurrence := hrec,
      degree_succ := hdeg_succ
  rr_finish using hstrictInterl, hdeg_succ


end Tactic
end RealRooted
