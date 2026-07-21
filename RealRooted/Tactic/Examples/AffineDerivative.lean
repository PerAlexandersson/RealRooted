import RealRooted.Tactic.AffineDerivative

open Polynomial

namespace RealRooted
namespace Tactic

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
