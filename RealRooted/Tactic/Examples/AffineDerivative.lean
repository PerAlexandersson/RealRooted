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
