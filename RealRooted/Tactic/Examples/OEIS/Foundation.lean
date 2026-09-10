import RealRooted.Tactic.AffineDerivative
import RealRooted.Tactic.OEIS.Basic
import RealRooted.Tactic.RootBounds

/-!
# OEIS foundational router regression examples

Foundational aliases, root-bound endpoints, and affine-derivative certificate
routing tests.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by rr_oeis_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_oeis_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_oeis_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_oeis_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_oeis_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_oeis_coeff_all_term

/-- Root-bound row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, ∀ r, (P n).IsRoot r → r ≤ 0 := by
  rr_root_nonpos_sequence using
    realrooted := hrr,
    nonneg := hpnn

/-- Sign-at-roots row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, ∀ r, (P n).IsRoot r →
      (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_sequence using
    realrooted := hrr,
    nonneg := hpnn

/-- Affine-derivative row-family `Prec` exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat, Prec
      (C (c n) * P n + (1 - X) * (P n).derivative)
      (P n) := by
  rr_prec_affine_derivative_nonneg_sequence using
    splits := hsplits,
    degree_ge_one := hdeg,
    nonneg := hnn,
    scalar_gt_degree := hc

/-- Affine-derivative row-family real-rootedness exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat,
      C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 ∧
        (C (c n) * P n + (1 - X) * (P n).derivative).Splits := by
  rr_prec_affine_derivative_nonneg_sequence_realrooted using
    splits := hsplits,
    degree_ge_one := hdeg,
    nonneg := hnn,
    scalar_gt_degree := hc

/-- Affine-derivative row-family coefficient side goal exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).coeff (P n).natDegree =
        (c n - (P n).natDegree) * (P n).leadingCoeff := by
  rr_affine_deriv_coeff_sequence using degree_ge_one := hdeg

/-- Affine-derivative row-family degree side goal exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).natDegree =
        (P n).natDegree := by
  rr_affine_deriv_natDegree_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

/-- Affine-derivative row-family leading coefficient side goal via the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).leadingCoeff =
        (c n - (P n).natDegree) * (P n).leadingCoeff := by
  rr_affine_deriv_leadingCoeff_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

/-- Affine-derivative row-family nonzero side goal exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat, C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 := by
  rr_affine_deriv_ne_zero_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc


end Tactic
end RealRooted
