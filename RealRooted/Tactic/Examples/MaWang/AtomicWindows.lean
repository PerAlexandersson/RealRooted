import RealRooted.Tactic.MaWang.Steps

/-!
# Ma--Wang atomic-window regression examples

Regression examples for atomic Ma--Wang window frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroots_le_neg_one : ∀ r, f.IsRoot r → r ≤ -1)
    (hdeg_lo : f.natDegree ≤ (u * f + (1 + X) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (1 + X) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (1 + X) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (1 + X) * f.derivative) := by
  rr_mw_derivative_sign_root_upper using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_upper := hroots_le_neg_one

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hc : 0 ≤ c)
    (hroots_le_neg_one : ∀ r, f.IsRoot r → r ≤ -1)
    (hdeg_lo :
      f.natDegree ≤
        (u * f + (-(C c) * X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X * (1 + X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff (u * f + (-(C c) * X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C c) * X * (1 + X)) * f.derivative) := by
  rr_mw_derivative_neg_X_one_add_outer using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    coeff_nonneg := hc,
    root_upper := hroots_le_neg_one

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroots_le_neg_one : ∀ r, f.IsRoot r → r ≤ -1)
    (hdeg_lo :
      f.natDegree ≤
        (u * f + (-(C ((3 : ℝ) + 1)) * X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C ((3 : ℝ) + 1)) * X * (1 + X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff
        (u * f + (-(C ((3 : ℝ) + 1)) * X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C ((3 : ℝ) + 1)) * X * (1 + X)) * f.derivative) := by
  rr_mw_derivative_neg_X_one_add_outer_auto using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_upper := hroots_le_neg_one

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hc : 0 ≤ c)
    (hroots_le_neg_one : ∀ r, f.IsRoot r → r ≤ -1)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * (1 + X)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (C c * (1 + X)) * f.derivative) := by
  rr_mw_derivative_sign_root_upper using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_upper := hroots_le_neg_one

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroots_le_one : ∀ r, f.IsRoot r → r ≤ 1)
    (hdeg_lo : f.natDegree ≤ (u * f + (X - 1) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X - 1) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X - 1) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X - 1) * f.derivative) := by
  rr_mw_derivative_sign_root_upper using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_upper := hroots_le_one

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hc : 0 ≤ c)
    (hroots_le_one : ∀ r, f.IsRoot r → r ≤ 1)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * (X - 1)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * (X - 1)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * (X - 1)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (C c * (X - 1)) * f.derivative) := by
  rr_mw_derivative_sign_root_upper using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_upper := hroots_le_one

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroots_nonpos : ∀ r, f.IsRoot r → r ≤ 0)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * (1 - X) ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 - X) ^ 2) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * (1 - X) ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X * (1 - X) ^ 2) * f.derivative) := by
  rr_mw_derivative_sign_roots_nonpos using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    roots_nonpos := hroots_nonpos

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ 0)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (X * (1 - X) * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 - X) * (1 + X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff (u * f + (X * (1 - X) * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X * (1 - X) * (1 + X)) * f.derivative) := by
  rr_mw_derivative_sign_window using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_lower := hroot_lo,
    root_upper := hroot_hi


end Tactic
end RealRooted
