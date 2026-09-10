import RealRooted.Tactic.MaWang.Factors

/-!
# Ma--Wang scalar-window regression examples

Regression examples for scalar-window Ma--Wang frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Scalar left denominators are normalized before the Ma--Wang wrapper. -/
example {d : ℝ} (hd : d ≠ 0) {F RHS : ℝ[X]}
    (hraw : C d * F = RHS) :
    F = C d⁻¹ * RHS := by
  rr_mw_den_norm using
    recurrence := hraw,
    den_nonzero := hd

/-- The scalar denominator normalizer works in indexed recurrence side goals. -/
example {P RHS : Nat → ℝ[X]}
    (hraw : ∀ n : Nat, C ((n : ℝ) + 2) * P (n + 1) = RHS n) :
    ∀ n : Nat, P (n + 1) = C (((n : ℝ) + 2)⁻¹) * RHS n := by
  intro n
  rr_mw_den_norm using
    recurrence := hraw n,
    den_nonzero := rr_mw_active_den_at_term n

/-- A062190 has a negative scalar denominator after the active row shift. -/
example (n : Nat) :
    (1 - (3 / 4 : ℝ) * ((n : ℝ) + 2) -
      (1 / 4 : ℝ) * ((n : ℝ) + 2) ^ 2) ≠ 0 := by
  rr_mw_active_den_at n

/-- Raw scalar-denominator recurrences can feed the Ma--Wang sequence wrapper. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 2) * P (n + 2) =
        C ((n : ℝ) + 2) *
          (U n * P (n + 1) +
            (C ((n : ℝ) + 1) * X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    roots_nonpos := hroots,
    recurrence := by
      intro n
      rr_mw_den_norm using
        recurrence := hraw n,
        den_nonzero := rr_mw_active_den_at_term n,
    degree_succ := hdeg

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hdeg_lo : f.natDegree ≤ (u * f + X * f.derivative).natDegree)
    (hdeg_hi : (u * f + X * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + X * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + X * f.derivative) := by
  rr_mw_derivative_sign_roots_nonpos using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    roots_nonpos := hf_roots

example {f u : ℝ[X]}
    (hf_rr : f ≠ 0 ∧ f.Splits)
    (hf_nn : HasNonnegCoeffs f)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + X * f.derivative).natDegree)
    (hdeg_hi : (u * f + X * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + X * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + X * f.derivative) := by
  rr_mw_derivative_sign_nonneg_coeffs using
    realrooted := hf_rr,
    nonneg := hf_nn,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * X * (1 - X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * X * (1 - X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * X * (1 - X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (C c * X * (1 - X)) * f.derivative) := by
  rr_mw_derivative_sign_roots_nonpos using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    roots_nonpos := hf_roots

example {f u q : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * q) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X * q) * f.derivative) := by
  rr_mw_derivative_X_mul using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    roots_nonpos := hf_roots,
    factor_nonneg := hq_nonneg

example {f u q : ℝ[X]}
    (hf_rr : f ≠ 0 ∧ f.Splits)
    (hf_nn : HasNonnegCoeffs f)
    (hdegf : 2 ≤ f.natDegree)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * q) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X * q) * f.derivative) := by
  rr_mw_derivative_sign_nonneg_factor using
    realrooted := hf_rr,
    nonneg := hf_nn,
    factor_nonneg := hq_nonneg,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos

example {f u q : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hc : 0 ≤ c)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * X * q) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (C c * X * q) * f.derivative) := by
  rr_mw_derivative_C_mul_X_mul using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    coeff_nonneg := hc,
    roots_nonpos := hf_roots,
    factor_nonneg := hq_nonneg

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ 0)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 + X)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X * (1 + X)) * f.derivative) := by
  rr_mw_derivative_X_one_add_window using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_lower := hroot_lo,
    root_upper := hroot_hi

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hdeg_lo :
      f.natDegree ≤
        (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff
        (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative) := by
  rr_mw_derivative_one_add_two_window using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_lower := hroot_lo,
    root_upper := hroot_hi

/-- Sequence endpoint for the `(1+X)(1+2X)P'` window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lo : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_one_add_two_window_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lo,
    root_upper := hroot_hi,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the `(1+X)(1+2X)P'` sequence shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lo : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_one_add_two_window_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lo,
    root_upper := hroot_hi,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hc : 0 ≤ c)
    (hdeg_lo : f.natDegree ≤ (u * f + C (-c) * f.derivative).natDegree)
    (hdeg_hi : (u * f + C (-c) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + C (-c) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + C (-c) * f.derivative) := by
  rr_mw_derivative_neg_const using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    coeff_nonneg := hc

/-- Automatic negative-constant derivative shell for active scalar
certificates. -/
example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤ (u * f + C (-((3 : ℝ) + 1)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + C (-((3 : ℝ) + 1)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + C (-((3 : ℝ) + 1)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + C (-((3 : ℝ) + 1)) * f.derivative) := by
  rr_mw_derivative_neg_const_auto using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hc : 0 ≤ c)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C c) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C c) * X ^ 2) * f.derivative) := by
  rr_mw_derivative_neg_X_sq using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    coeff_nonneg := hc

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤
        (u * f + (-(C ((3 : ℝ) + 1)) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C ((3 : ℝ) + 1)) * X ^ 2) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff (u * f + (-(C ((3 : ℝ) + 1)) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C ((3 : ℝ) + 1)) * X ^ 2) * f.derivative) := by
  rr_mw_derivative_neg_X_sq_auto using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos


end Tactic
end RealRooted
