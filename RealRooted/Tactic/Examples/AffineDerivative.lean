import RealRooted.Tactic.AffineDerivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

open Polynomial

namespace RealRooted
namespace Tactic

/-- Regression coverage for the zero, constant, cancellation, and nonzero-top
boundaries of the generic affine Euler degree API. -/
example :
    (C (3 : ℤ) * (0 : ℤ[X]) +
      (C 2 + C (-1 : ℤ) * X) * (0 : ℤ[X]).derivative).natDegree ≤
      (0 : ℤ[X]).natDegree := by
  exact Polynomial.natDegree_C_mul_add_affine_mul_derivative_le
    (0 : ℤ[X]) 3 2 (-1)

example :
    (C (3 : ℤ) * (1 : ℤ[X]) +
      (C 2 + C (-1 : ℤ) * X) * (1 : ℤ[X]).derivative).natDegree = 0 ∧
      (C (3 : ℤ) * (1 : ℤ[X]) +
        (C 2 + C (-1 : ℤ) * X) * (1 : ℤ[X]).derivative).leadingCoeff = 3 := by
  simpa using
    (Polynomial.natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
      (1 : ℤ[X]) 3 2 (-1) (by norm_num))

example :
    (C (1 : ℤ) * X +
      (C 0 + C (-1 : ℤ) * X) * X.derivative : ℤ[X]).coeff 1 = 0 := by
  have h := Polynomial.coeff_C_mul_add_affine_mul_derivative
    (X : ℤ[X]) 1 0 (-1) 1
  norm_num at h ⊢

example :
    (C (2 : ℤ) * X +
      (C 0 + C (-1 : ℤ) * X) * X.derivative : ℤ[X]).natDegree = 1 ∧
      (C (2 : ℤ) * X +
        (C 0 + C (-1 : ℤ) * X) * X.derivative).leadingCoeff = 1 := by
  simpa using
    (Polynomial.natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
      (X : ℤ[X]) 2 0 (-1) (by norm_num))

example {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ) :
    (C c * f + (1 - X) * f.derivative).eval r =
      (1 - r) * f.derivative.eval r := by
  rr_affine_deriv_eval_at_root using root := hr

example {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ)
    (hr_nonpos : r ≤ 0) :
    (C c * f + (1 - X) * f.derivative).eval r = 0 ↔
      f.derivative.eval r = 0 := by
  rr_affine_deriv_eval_zero_iff using root := hr, root_nonpos := hr_nonpos

example {f : ℝ[X]} (hdeg : 1 ≤ f.natDegree) (c : ℝ) :
    (C c * f + (1 - X) * f.derivative).coeff f.natDegree =
      (c - f.natDegree) * f.leadingCoeff := by
  rr_affine_deriv_coeff using degree_ge_one := hdeg

example {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    {c : ℝ} (hc : c ≠ (f.natDegree : ℝ)) :
    (C c * f + (1 - X) * f.derivative).natDegree = f.natDegree := by
  rr_affine_deriv_natDegree using
    nonzero := hf,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

example {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    {c : ℝ} (hc : c ≠ (f.natDegree : ℝ)) :
    (C c * f + (1 - X) * f.derivative).leadingCoeff =
      (c - f.natDegree) * f.leadingCoeff := by
  rr_affine_deriv_leadingCoeff using
    nonzero := hf,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

example {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    {c : ℝ} (hc : c ≠ (f.natDegree : ℝ)) :
    C c * f + (1 - X) * f.derivative ≠ 0 := by
  rr_affine_deriv_ne_zero using
    nonzero := hf,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).coeff (P n).natDegree =
        (c n - (P n).natDegree) * (P n).leadingCoeff := by
  rr_affine_deriv_coeff_sequence using degree_ge_one := hdeg

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

example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat, C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 := by
  rr_affine_deriv_ne_zero_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

example {f : ℝ[X]} (hf : f.Splits)
    (hdeg : 2 ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    Prec (C c * f + (1 - X) * f.derivative) f := by
  rr_prec_affine_derivative_strong using
    splits := hf,
    degree_ge_two := hdeg,
    pos_lc := hf_pos,
    roots_nonpos := hroots_nonpos,
    scalar_gt_degree := hc

example {f : ℝ[X]} (hf : f.Splits)
    (hdeg : f.natDegree = 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    Prec (C c * f + (1 - X) * f.derivative) f := by
  rr_prec_affine_derivative_degree_one using
    splits := hf,
    degree_eq_one := hdeg,
    pos_lc := hf_pos,
    roots_nonpos := hroots_nonpos,
    scalar_gt_degree := hc

example {f : ℝ[X]} (hf : f.Splits)
    (hdeg : 1 ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    Prec (C c * f + (1 - X) * f.derivative) f := by
  rr_prec_affine_derivative using
    splits := hf,
    degree_ge_one := hdeg,
    pos_lc := hf_pos,
    roots_nonpos := hroots_nonpos,
    scalar_gt_degree := hc

example {f : ℝ[X]} (hf : f.Splits)
    (hdeg : 1 ≤ f.natDegree)
    (hfnn : HasNonnegCoeffs f)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    Prec (C c * f + (1 - X) * f.derivative) f := by
  rr_prec_affine_derivative_nonneg using
    splits := hf,
    degree_ge_one := hdeg,
    nonneg := hfnn,
    scalar_gt_degree := hc

example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroots_nonpos : ∀ n : Nat, ∀ r ∈ (P n).roots, r ≤ 0)
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat, Prec
      (C (c n) * P n + (1 - X) * (P n).derivative)
      (P n) := by
  rr_prec_affine_derivative_sequence using
    splits := hsplits,
    degree_ge_one := hdeg,
    pos_lc := hpos,
    roots_nonpos := hroots_nonpos,
    scalar_gt_degree := hc

example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroots_nonpos : ∀ n : Nat, ∀ r ∈ (P n).roots, r ≤ 0)
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat,
      C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 ∧
        (C (c n) * P n + (1 - X) * (P n).derivative).Splits := by
  rr_prec_affine_derivative_sequence_realrooted using
    splits := hsplits,
    degree_ge_one := hdeg,
    pos_lc := hpos,
    roots_nonpos := hroots_nonpos,
    scalar_gt_degree := hc

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

example {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ)
    (hr_nonpos : r ≤ 0) :
    0 < (C c * f + (1 - X) * f.derivative).eval r ↔
      0 < f.derivative.eval r := by
  rr_affine_deriv_eval_pos_iff using root := hr, root_nonpos := hr_nonpos

example {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ)
    (hr_nonpos : r ≤ 0) :
    (C c * f + (1 - X) * f.derivative).eval r < 0 ↔
      f.derivative.eval r < 0 := by
  rr_affine_deriv_eval_neg_iff using root := hr, root_nonpos := hr_nonpos

end Tactic
end RealRooted
