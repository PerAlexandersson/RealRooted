import RealRooted.Tactic.Favard

/-!
# `rr_favard` examples: direct

Abstract smoke tests for the direct Favard frontends, and the denominator and coefficient helpers of
`RealRooted.Tactic.Favard.Basic`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by rr_favard_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_favard_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_favard_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_favard_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_favard_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_favard_coeff_all_term

example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

/-- Exact local inference ignores an unrelated Favard certificate packet. -/
example {P Q : Nat → ℝ[X]} {α β γ δ : Nat → ℝ}
    (_hrecDecoy : SatisfiesFavardRecurrence Q γ δ)
    -- This guards against the positivity proof fixing the wrong coefficient sequence.
    (_hbetaDecoy : ∀ n : Nat, 0 < δ (n + 1))
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    StrictInterl (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

example {P : Nat → ℝ[X]} {α β : Nat → ℝ} {n : Nat}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    P n ≠ 0 := by
  rr_favard using hrec, hbeta

/-- Raw Favard recurrence with automatic positivity for an explicit lag. -/
example {P : Nat → ℝ[X]}
    (hrec : SatisfiesFavardRecurrence P (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_const_unit using 0, hP0, hP1, hstep

/-- OEIS shape `A053122`/`A110162`: `P_{n+2}=(t-2)P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C 2)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C 2) * P (n + 1) - P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using 2, 0, hP0, hP1, hstep

/-- OEIS shapes `A053124`/`A084930`: `P_{n+2}=(4t-2)P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (4 : ℝ) * X - C (2 : ℝ))
    (hstep :
      ∀ n : Nat, P (n + 2) = (C (4 : ℝ) * X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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

/-- Constant-coefficient Favard shape with a shifted affine multiplier and
arbitrary positive lag, tested pointwise. -/
example {P : Nat → ℝ[X]} {α β : ℝ} {n : Nat}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    StrictInterl (P n) (P (n + 1)) := by
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
    StrictInterl (P n) (P (n + 1)) := by
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
  have hP1' : P 1 = X - C (αfun 0) := by simpa [αfun] using hP1
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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
  have hP1' : P 1 = C (sfun 0) * X - C (αfun 0) := by simpa [sfun, αfun] using hP1
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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

/-- Direct raw Favard denominator normalizer. -/
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hraw : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n := by
  rr_favard_den_raw using hraw

/-- Constant-coefficient Favard wrapper with automatic positivity. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (0 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (0 : ℝ)) * P (n + 1) - C (1 : ℝ) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
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

end Tactic
end RealRooted
