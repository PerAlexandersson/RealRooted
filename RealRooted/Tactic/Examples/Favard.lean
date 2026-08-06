import RealRooted.Tactic.Favard

/-!
# `rr_favard` examples

Abstract smoke tests for the Favard dispatcher tactic.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by
  rr_favard_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_favard_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_favard_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_favard_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_favard_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_favard_coeff_all_term

example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

/-- Exact local inference ignores an unrelated Favard certificate packet. -/
example {P Q : Nat → ℝ[X]} {α β γ δ : Nat → ℝ}
    (_hrecDecoy : SatisfiesFavardRecurrence Q γ δ)
    -- This guards against the positivity proof fixing the wrong coefficient sequence.
    (_hbetaDecoy : ∀ n : Nat, 0 < δ (n + 1))
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard

/-- The inferred auto form retains positivity automation. -/
example {P Q : Nat → ℝ[X]} {γ δ : Nat → ℝ}
    (_hrecDecoy : SatisfiesFavardRecurrence Q γ δ)
    (hrec : SatisfiesFavardRecurrence P (fun _ => 0) (fun _ => 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_auto

example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using
    recurrence := hrec,
    beta_pos := hbeta

example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard using hrec, hbeta

example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard using hrec, hbeta

example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, IsGeneralizedSturmSeq ((List.range (n + 1)).reverse.map P) := by
  rr_favard using hrec, hbeta

example {P : Nat → ℝ[X]} {α β : Nat → ℝ} {n : Nat}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

example {P : Nat → ℝ[X]} {α β : Nat → ℝ} {n : Nat}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    P n ≠ 0 := by
  rr_favard using hrec, hbeta

/-- Raw Favard recurrence with automatic positivity for an explicit lag. -/
example {P : Nat → ℝ[X]}
    (hrec : SatisfiesFavardRecurrence P (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_auto using
    recurrence := hrec

example {P : Nat → ℝ[X]}
    (hrec : SatisfiesFavardRecurrence P (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_auto using
    recurrence := hrec

/-- OEIS shape `A049310`/`A124038`: `P_{n+2}=tP_{n+1}-P_n`. -/
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

/-- Positional syntax smoke test for `rr_favard_const`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat, P (n + 2) = X * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using 0, hP0, hP1, hstep

/-- OEIS shape `A053122`/`A110162`: `P_{n+2}=(t-2)P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C 2)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C 2) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- OEIS shape `A102587`: `P_{n+2}=(t-1)P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C 1)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C 1) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- OEIS shapes `A078812`/`A085478`/`A111125`:
`P_{n+2}=(t+2)P_{n+1}-P_n`. -/
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

/-- OEIS shapes `A053117`/`A053120`/`A136523`/`A244419`:
`P_{n+2}=2tP_{n+1}-P_n`. -/
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

/-- Positional syntax smoke test for `rr_favard_affine_const`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat, P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using 2, 0, hP0, hP1, hstep

/-- OEIS shapes `A053124`/`A084930`: `P_{n+2}=(4t-2)P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (4 : ℝ) * X - C (2 : ℝ))
    (hstep :
      ∀ n : Nat, P (n + 2) = (C (4 : ℝ) * X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using
    slope := 4,
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- OEIS shapes `A049310`/`A124038`/`A127672`: real-rootedness consequence of
the same monic Chebyshev recurrence. -/
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

/-- Projection endpoint for the monic Chebyshev Favard wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat, P (n + 2) = X * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_const_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Real-rootedness consequence for the nonmonic `2t` Chebyshev recurrence. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat, P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_const_unit using
    slope := 2,
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Projection endpoint for the nonmonic `2t` Chebyshev recurrence. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat, P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_affine_const_unit using
    slope := 2,
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Parameterized monic Favard unit-lag shape:
`P_{n+2}=(t-α_{n+1})P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_unit using (fun m : Nat => (m : ℝ)), hP0, hP1, hstep

/-- The same parameterized unit-lag wrapper also dispatches real-rootedness
and pointwise nonzero goals. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    P n ≠ 0 := by
  rr_favard_param_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Projection endpoint for the parameterized monic Favard wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_param_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Positive-slope parameterized affine Favard unit-lag shape:
`P_{n+2}=(s_{n+1}t-α_{n+1})P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Projection endpoint for the affine parameterized Favard wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_affine_param_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Projection endpoint for the monic row-sign Favard wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (((n + 1 : Nat) : ℝ)) - X) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_param_row_sign_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- The affine parameterized unit-lag wrapper also accepts an explicit
positive-slope certificate when the slope sequence is symbolic. -/
example {P : Nat → ℝ[X]} {s : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_unit using
    slope := s,
    alpha := fun m : Nat => (m : ℝ),
    slope_pos := hs,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Constant-coefficient Favard shape with a shifted affine multiplier and
arbitrary positive lag, tested pointwise. -/
example {P : Nat → ℝ[X]} {α β : ℝ} {n : Nat}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_const using
    alpha := α,
    beta := β,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Constant-coefficient Favard shape, tested on a pointwise nonzero goal. -/
example {P : Nat → ℝ[X]} {α β : ℝ} {n : Nat}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    P n ≠ 0 := by
  rr_favard_const using
    alpha := α,
    beta := β,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Positive-slope affine Favard shape with arbitrary positive lag, tested
pointwise. -/
example {P : Nat → ℝ[X]} {s α β : ℝ} {n : Nat}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Positive-slope affine Favard shape, tested on a pointwise nonzero goal. -/
example {P : Nat → ℝ[X]} {s α β : ℝ} {n : Nat}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    P n ≠ 0 := by
  rr_favard_affine_const using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Automatic positivity for the positive-slope affine constant wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X - C (0 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (0 : ℝ)) * P (n + 1) -
          C (1 : ℝ) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_const_auto using
    slope := 2,
    alpha := 0,
    beta := 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Row-sign affine constant wrapper with explicit positive certificates. -/
example {P : Nat → ℝ[X]} {β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X - C (0 : ℝ)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (2 : ℝ) * X - C (0 : ℝ)) * P (n + 1) - C β * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_affine_const_row_sign using
    slope := 2,
    alpha := 0,
    beta := β,
    slope_pos := rr_positivity_term,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Automatic positivity for row-sign affine constant wrappers. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X - C (0 : ℝ)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (2 : ℝ) * X - C (0 : ℝ)) * P (n + 1) -
          C (1 : ℝ) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_favard_affine_const_row_sign_auto using
    slope := 2,
    alpha := 0,
    beta := 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Constant-coefficient Favard shape with arbitrary positive lag. -/
example {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const using
    alpha := α,
    beta := β,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Parameterized monic Favard lag with active-index positivity. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Parameterized monic Favard wrapper with explicit beta positivity. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  let αfun : Nat → ℝ := fun m => (m : ℝ)
  let βfun : Nat → ℝ := fun m => (m : ℝ)
  have hP1' : P 1 = X - C (αfun 0) := by
    simpa [αfun] using hP1
  have hstep' :
      ∀ n : Nat,
        P (n + 2) =
          (X - C (αfun (n + 1))) * P (n + 1) - C (βfun (n + 1)) * P n := by
    intro n
    simpa [αfun, βfun] using hstep n
  rr_favard_param using
    alpha := αfun,
    beta := βfun,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := hP1',
    step := hstep'

/-- Parameterized monic Favard wrapper, tested on a pointwise nonzero goal. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    P n ≠ 0 := by
  rr_favard_param_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Positive-slope parameterized affine Favard smoke test with variable lag
and shift. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Parameterized affine Favard wrapper with explicit positivity certificates. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, (P n).Splits := by
  let sfun : Nat → ℝ := fun _ => 2
  let αfun : Nat → ℝ := fun m => (m : ℝ)
  let βfun : Nat → ℝ := fun m => (m : ℝ)
  have hP1' : P 1 = C (sfun 0) * X - C (αfun 0) := by
    simpa [sfun, αfun] using hP1
  have hstep' :
      ∀ n : Nat,
        P (n + 2) =
          (C (sfun (n + 1)) * X - C (αfun (n + 1))) * P (n + 1) -
            C (βfun (n + 1)) * P n := by
    intro n
    simpa [sfun, αfun, βfun] using hstep n
  rr_favard_affine_param using
    slope := sfun,
    alpha := αfun,
    beta := βfun,
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := hP1',
    step := hstep'

/-- The inferred affine router finds the standard certificate packet while the
coefficient families and recurrence remain explicit. -/
example {P Q : Nat → ℝ[X]} {s α β u v w : Nat → ℝ}
    (_hsDecoy : ∀ n : Nat, 0 < u n)
    (_hβDecoy : ∀ n : Nat, 0 < w (n + 1))
    (_hQ0 : Q 0 = 1)
    (_hQ1 : Q 1 = C (u 0) * X - C (v 0))
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_affine_param_infer using
    slope := s,
    alpha := α,
    beta := β,
    step := hstep

/-- The inferred affine router also dispatches the combined nonzero and
real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_infer using
    slope := s,
    alpha := α,
    beta := β,
    step := hstep

/-- The inferred affine router exposes the consecutive interlacing packet. -/
example {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_favard_affine_param_infer using
    slope := s,
    alpha := α,
    beta := β,
    step := hstep

/-- The inferred form proves elementary positivity but still requires the two
base certificates from the local context or tagged declarations. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C ((((n + 1 : Nat) : ℝ) + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_infer using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    step := hstep

/-- Mixed packets can combine automatic slope positivity with a looked-up lag
certificate. -/
example {P : Nat → ℝ[X]} {β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_affine_param_infer using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := β,
    step := hstep

/-- Base certificates are intentionally not synthesized by the inferred form. -/
example {P : Nat → ℝ[X]}
    (_hP0 : P 0 = 1)
    (_hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n)
    (hgoal : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat, (P n).Splits := by
  fail_if_success
    rr_favard_affine_param_infer using
      slope := fun _ : Nat => (2 : ℝ),
      alpha := fun m : Nat => (m : ℝ),
      beta := fun _ : Nat => (1 : ℝ),
      step := _hstep
  exact hgoal

/-- Positive-slope parameterized affine Favard smoke test with a scalar
denominator on the displayed recurrence. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n * (n.succ : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The scalar-denominator affine Favard macro also handles distributed raw
recurrences on pointwise interlacing goals. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n * (n.succ : ℝ)) * P n) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The same distributed denominator path dispatches pointwise nonzero goals. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n * (n.succ : ℝ)) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Distributed raw recurrences may combine `n.succ` indexing with a lag
coefficient written as `C d_n * C beta_{n+1}`. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n) * C (n.succ : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The distributed denominator path also accepts the reversed scalar order
`C beta_{n+1} * C d_n`. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (n.succ : ℝ) * C (d n) * P n) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The lag coefficient may also be written as `C (beta_{n+1} * d_n)`. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C ((n.succ : ℝ) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The scalar-denominator affine Favard macro also dispatches
real-rootedness endpoints with explicit positivity certificates. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The distributed denominator path also dispatches pointwise real-rootedness
endpoints with explicit positivity certificates. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {s α β : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic scalar-denominator Favard alias with automatic lag positivity. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_den_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit monic scalar-denominator Favard alias with a supplied lag
positivity certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    P n ≠ 0 := by
  rr_favard_param_den using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Affine scalar-denominator Favard alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit affine scalar-denominator unit-lag alias with a supplied
slope-positivity certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    slope_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic scalar-denominator Favard alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_den_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Row-sign affine Favard with a factored scalar denominator. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) -
            C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The factored row-sign denominator path also dispatches global
real-rootedness endpoints. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) -
            C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The row-sign denominator path also accepts the mixed `n.succ` and
`C d_n * C beta_{n+1}` spelling. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n) * C (n.succ : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The row-sign distributed path accepts the reversed scalar order on a
pointwise interlacing endpoint. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (n.succ : ℝ) * C (d n) * P n) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The row-sign distributed path accepts `C (beta_{n+1} * d_n)` as the lag
coefficient. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C ((n.succ : ℝ) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic row-sign denominator alias with a positive variable lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_den_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit monic row-sign denominator alias with a supplied lag-positivity
certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    P n ≠ 0 := by
  rr_favard_param_row_sign_den using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Affine row-sign denominator alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit affine row-sign denominator unit-lag alias with a supplied
slope-positivity certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    slope_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic row-sign denominator alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_den_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Row-sign affine Favard with a distributed scalar denominator and explicit
positivity certificates, tested on a pointwise real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {s α β : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Row-sign affine Favard with an unfactored raw scalar-denominator numerator. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_raw_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-2 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Raw scalar-denominator Favard with product-displayed slope and lag
coefficients. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * C ((n : ℝ) + 2) * X + C (-((n : ℝ) + 1))) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_prod_auto using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => -((n : ℝ) + 1),
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Row-sign raw scalar-denominator Favard with product-displayed slope and
lag coefficients. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * C ((n : ℝ) + 2) * X + C ((n : ℝ) + 1)) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den_raw_prod_auto using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (-2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => (n : ℝ) + 1,
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Monic raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (1 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_den_raw_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (1 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Monic unit-lag raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (1 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    P n ≠ 0 := by
  rr_favard_param_den_raw_unit using
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (1 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Row-sign monic raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-1 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_den_raw_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-1 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Row-sign monic unit-lag raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-1 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_den_raw_unit using
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-1 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Direct raw Favard denominator normalizer. -/
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hraw : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n := by
  rr_favard_den_raw using hraw

/-- Explicit affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-((n : ℝ) + 2)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -((n : ℝ) + 2),
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Automatic positivity variant of the affine raw scalar-denominator alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-((n : ℝ) + 2)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -((n : ℝ) + 2),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- The raw scalar-denominator router also exposes consecutive interlacing. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-((n : ℝ) + 2)) * P n) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -((n : ℝ) + 2),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit product-displayed affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * C ((n : ℝ) + 2) * X + C (-((n : ℝ) + 1))) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_den_raw_prod using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => -((n : ℝ) + 1),
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Unit-lag affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit monic raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (1 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    P n ≠ 0 := by
  rr_favard_param_den_raw using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (1 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Constant-coefficient Favard wrapper with automatic positivity. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (0 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (0 : ℝ)) * P (n + 1) - C (1 : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_auto using
    alpha := 0,
    beta := 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Constant row-sign unit-lag wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (0 : ℝ)))
    (hstep : ∀ n : Nat, P (n + 2) = -(X - C (0 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_const_row_sign_unit using 0, hP0, hP1, hstep

/-- Parameterized affine row-sign wrapper with explicit positivity
certificates. -/
example {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- The inferred router rolls back from the standard orientation and finds the
row-sign certificate packet. -/
example {P : Nat → ℝ[X]} {s α β : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_infer using
    slope := s,
    alpha := α,
    beta := β,
    step := hstep

/-- Automatic positivity for parameterized affine row-sign wrappers. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X - C ((0 : Nat) : ℝ)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C ((((n + 1 : Nat) : ℝ) + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Unit-lag affine row-sign wrapper. -/
example {P : Nat → ℝ[X]} {s α : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) - P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_row_sign_unit using
    slope := s,
    alpha := α,
    slope_pos := hs,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Monic parameterized row-sign wrapper with explicit positivity. -/
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_row_sign using
    alpha := α,
    beta := β,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Automatic positivity for monic parameterized row-sign wrappers. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (n.succ : ℝ) - X) * P (n + 1) - C ((n.succ : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Explicit row-sign affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_raw using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-2 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit product-displayed row-sign affine raw denominator alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * C ((n : ℝ) + 2) * X + C ((n : ℝ) + 1)) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_row_sign_den_raw_prod using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (-2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => (n : ℝ) + 1,
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Unit-lag row-sign affine raw denominator alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den_raw_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-2 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit monic row-sign raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-1 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_den_raw using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-1 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

end Tactic
end RealRooted
