import RealRooted.Tactic.Favard.RowSign

/-!
# OEIS test-bed Favard examples

Regression examples for Favard row-sign frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Favard/Chebyshev Family F dispatcher skeleton -/

-- `A157077`: scalar denominator followed by positive-slope Favard.
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

-- `A063007`: raw scalar-denominator Favard numerator with nonzero shift.
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

-- `A376467`: same denominator-Favard normalization with a larger shift.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X - C (-3 : ℝ))
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        (C (6 - 4 * ((n : ℝ) + 3)) * X +
            C (9 - 6 * ((n : ℝ) + 3))) * P (n + 1) +
          C (-2 + ((n : ℝ) + 3)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun m => -((6 * (m : ℝ) + 3) / ((m : ℝ) + 1)),
    beta := fun m => (m : ℝ) / ((m : ℝ) + 1),
    raw_slope := fun n => 6 - 4 * ((n : ℝ) + 3),
    raw_const := fun n => 9 - 6 * ((n : ℝ) + 3),
    raw_lag := fun n => -2 + ((n : ℝ) + 3),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

-- `A049310`: Chebyshev `S(n,x)=U(n,x/2)` coefficient triangle.
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

-- `A049310`/`A124038`: `P_{n+2}=tP_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat, P (n + 2) = X * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A053122`: `P_{n+2}=(t-2)P_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (2 : ℝ))
    (hstep : ∀ n : Nat, P (n + 2) = (X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A078812`: `P_{n+2}=(t+2)P_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-2 : ℝ))
    (hstep : ∀ n : Nat, P (n + 2) = (X - C (-2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := -2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A124039`: row-sign normalized Chebyshev step `P_{n+2}=-tP_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat, P (n + 2) = -X * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_row_sign_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A124039`: real-rootedness endpoint for the same row-sign normalization.
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

-- `A053117`/`A053120`: `P_{n+2}=2tP_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat, P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using
    slope := 2,
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A053124`/`A084930`: `P_{n+2}=(4t-2)P_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (4 : ℝ) * X - C (2 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) = (C (4 : ℝ) * X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using
    slope := 4,
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A137286`: parameterized Favard step `P_m=tP_{m-1}-(m+1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) - C (((n + 1 : Nat) : ℝ) + 2) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun _ : Nat => (0 : ℝ),
    beta := fun m : Nat => (m : ℝ) + 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A137338`: parameterized Favard step `P_m=(t+1-m)P_{m-1}-(m-1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
        C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-! ### Family F promoted scalar-lag extension scan -/

-- `A049218`: active scalar-lag Favard shell
-- `P_m=tP_{m-1}-m(m+1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        X * P (n + 1) -
          C (((((n + 1 : Nat) : ℝ) + 1) * (((n + 1 : Nat) : ℝ) + 2))) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun _ : Nat => (0 : ℝ),
    beta := fun m : Nat => ((m : ℝ) + 1) * ((m : ℝ) + 2),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A094816`: shifted active range of
-- `P_m=(t+m-1)P_{m-1}-(m-2)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-1 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (-((((n + 1 : Nat) : ℝ) + 1)))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => -((m : ℝ) + 1),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A136532`: scalar-denominator row-sign Favard raw numerator.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 =
      -(C ((4 : ℝ) / 3) * X - C ((16 : ℝ) / 3)))
    (hraw : ∀ n : Nat,
      C (1 + ((n + 2 : Nat) : ℝ) / 2) * P (n + 2) =
        (C (-((((n : ℝ) + 5) / 2))) * X +
            C (((n : ℝ) + 3) * ((n : ℝ) + 5))) * P (n + 1) +
          C (-((((n : ℝ) + 3) * ((n : ℝ) + 4) * ((n : ℝ) + 5)) / 2)) *
            P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_raw_auto using
    slope := fun m : Nat => ((m : ℝ) + 4) / ((m : ℝ) + 3),
    alpha := fun m : Nat => 2 * ((m : ℝ) + 2) * ((m : ℝ) + 4) / ((m : ℝ) + 3),
    beta := fun m : Nat => ((m : ℝ) + 2) * ((m : ℝ) + 4),
    raw_slope := fun n : Nat => -(((n : ℝ) + 5) / 2),
    raw_const := fun n : Nat => ((n : ℝ) + 3) * ((n : ℝ) + 5),
    raw_lag := fun n : Nat =>
      -((((n : ℝ) + 3) * ((n : ℝ) + 4) * ((n : ℝ) + 5)) / 2),
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun n : Nat => 1 + ((n + 2 : Nat) : ℝ) / 2,
    raw_recurrence := hraw

-- `A136668`: `P_m=2mtP_{m-1}-(m+1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 * (((n + 1 : Nat) : ℝ) + 1)) * X) * P (n + 1) -
          C ((((n + 1 : Nat) : ℝ) + 2)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_auto using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun _ : Nat => (0 : ℝ),
    beta := fun m : Nat => (m : ℝ) + 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A181332`: constant affine Favard row `P_m=(t+3)P_{m-1}-2P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-3 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (-3 : ℝ)) * P (n + 1) - C (2 : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_auto using
    alpha := -3,
    beta := 2,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    step := hstep

-- `A199577`: shifted active shell
-- `P_m=(t-3-2m)P_{m-1}-(m+1)^2P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (5 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (2 * ((n + 1 : Nat) : ℝ) + 5)) * P (n + 1) -
          C (((((n + 1 : Nat) : ℝ) + 2) ^ 2)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => 2 * (m : ℝ) + 5,
    beta := fun m : Nat => ((m : ℝ) + 2) ^ 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A269951`: shifted active range of
-- `P_m=(t+m-1)P_{m-1}-(m-3)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-2 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (-((((n + 1 : Nat) : ℝ) + 2)))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => -((m : ℝ) + 2),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A285072`: `P_m=(2-t)P_{m-1}-P_{m-2}`, another row-sign Favard case.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (2 : ℝ)))
    (hstep : ∀ n : Nat, P (n + 2) = -(X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_row_sign_unit using
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A327997`: shifted active range of
-- `P_m=(t+m+1)P_{m-1}-3(m-2)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-3 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (-((((n + 1 : Nat) : ℝ) + 3)))) * P (n + 1) -
          C (3 * ((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => -((m : ℝ) + 3),
    beta := fun m : Nat => 3 * (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A137338`-shaped row-sign surface for n-dependent Favard coefficients.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat,
      P (n + 2) = -(X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
        C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- Unit-lag shortcut for A124039-type row-sign Favard shifts.
example {P : Nat → ℝ[X]} {α : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(X - C (α (n + 1))) * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_unit using
    alpha := α,
    base_zero := hP0,
    base_one := hP1,
    step := hstep


end Tactic
end RealRooted
