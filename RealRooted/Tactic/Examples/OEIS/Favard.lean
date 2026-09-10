import RealRooted.Tactic.Favard.RowSign

/-!
# OEIS Favard router regression examples

Favard recurrence and row-sign certificate routing tests.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Favard row-family `Prec` exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

/-- Favard unit-lag Chebyshev row-family route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat, P (n + 2) = X * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Favard row-sign unit-lag route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat, P (n + 2) = -X * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_row_sign_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Favard denominator-normalized affine row-family route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        C (1 - ((n : ℝ) + 3)) *
          (((C (((4 * (n.succ : ℝ) + 2) / ((n.succ : ℝ) + 1))) * X -
                C (0 : ℝ)) *
              P (n + 1) -
            C ((4 * (n.succ : ℝ)) / ((n.succ : ℝ) + 1)) * P n))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun _ => (0 : ℝ),
    beta := fun m => (4 * (m : ℝ)) / ((m : ℝ) + 1),
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

/-- Favard raw scalar-denominator route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X - C (-1 : ℝ))
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        (C (6 - 4 * ((n : ℝ) + 3)) * X +
            C (3 - 2 * ((n : ℝ) + 3))) * P (n + 1) +
          C (-2 + ((n : ℝ) + 3)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun m => -((2 * (m : ℝ) + 1) / ((m : ℝ) + 1)),
    beta := fun m => (m : ℝ) / ((m : ℝ) + 1),
    raw_slope := fun n => 6 - 4 * ((n : ℝ) + 3),
    raw_const := fun n => 3 - 2 * ((n : ℝ) + 3),
    raw_lag := fun n => -2 + ((n : ℝ) + 3),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw


end Tactic
end RealRooted
