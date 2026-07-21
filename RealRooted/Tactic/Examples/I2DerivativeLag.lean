import RealRooted.Tactic.I2DerivativeLag

/-!
# Smoke examples for the Family I derivative-lag frontend
-/

open Polynomial

namespace RealRooted

example {P U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdegree_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hderivative_nonpos : ∀ n : Nat, ∀ r : ℝ,
      (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hlag_nonpos : ∀ n : Nat, ∀ r : ℝ,
      (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno_common :
      ∀ n : Nat, ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_i2_derivative_lag_directHalfLine_sequence
    hbase hpos hdegree_two hrec hderivative_nonpos hlag_nonpos hdeg_succ hno_common

example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdegree_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_i2_derivative_lag_wagnerGap_sequence
    hbase hnonneg hdegree_two ha hc hrec

end RealRooted
