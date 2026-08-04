import RealRooted.Tactic.MaWang

/-!
# `rr_ma_wang` examples

Abstract smoke tests for the Ma-Wang dispatcher tactics.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {n : Nat} : 0 ≤ (n : ℝ) + 1 := by
  rr_mw_active_nonneg_at n

example {n : Nat} : (n : ℝ) + 2 ≠ 0 := by
  rr_mw_active_den_at n

example : ∀ n : Nat, (n : ℝ) + 2 ≠ 0 := by
  rr_mw_active_den_all

example {n : Nat} : 1 - ((n : ℝ) + 3) ≠ 0 := by
  rr_scalar_active_den_at n

example : ∀ n : Nat, 1 - ((n : ℝ) + 3) ≠ 0 := by
  rr_scalar_active_den_all

/-- A supplied recurrence fixes the hidden target before atomic lookup. -/
example {f F u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hrec : F = u * f + v * f.derivative)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_mw_derivative_nonpos_step using
    splits := hf,
    degree_two := hdegf,
    target_pos_lc := hF_pos,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    source_pos_lc := hf_pos,
    coeff_nonpos := hv_nonpos

/-- Recurrence normalization completes before certificate lookup starts. -/
example {f F u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hrec : F = u * f + v * f.derivative)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_mw_derivative_nonpos_step using recurrence := hrec

example {f F u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hraw : F = v * f.derivative + u * f)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_mw_derivative_nonpos_step using recurrence :=
    (by simpa [add_comm] using hraw : F = u * f + v * f.derivative)

/-- The inferred step instantiates indexed local certificate families. -/
example {P U V : Nat → ℝ[X]} {n : Nat}
    (hsplits : ∀ k, (P (k + 1)).Splits)
    (hdeg_two : ∀ k, 2 ≤ (P (k + 1)).natDegree)
    (hrec : ∀ k,
      P (k + 2) = U k * P (k + 1) + V k * (P (k + 1)).derivative)
    (hpos : ∀ k, HasPosLeadingCoeff (P k))
    (hdeg_lo : ∀ k, (P (k + 1)).natDegree ≤ (P (k + 2)).natDegree)
    (hdeg_hi : ∀ k, (P (k + 2)).natDegree ≤ (P (k + 1)).natDegree + 1)
    (hcoeff : ∀ k r, (P (k + 1)).IsRoot r → (V k).eval r ≤ 0) :
    Prec (P (n + 1))
      (U n * P (n + 1) + V n * (P (n + 1)).derivative) := by
  rr_mw_derivative_nonpos_step using recurrence := hrec n

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang using
    hf, hdegf, hdeg_lo, hdeg_hi, hF_pos, hf_pos, hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_sign := hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_same using
    hf, hdegf, hdeg, hF_pos, hf_pos, hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_same using
    splits := hf,
    degree_two := hdegf,
    degree := hdeg,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_sign := hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_succ using
    hf, hdegf, hdeg, hF_pos, hf_pos, hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_succ using
    splits := hf,
    degree_two := hdegf,
    degree := hdeg,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_sign := hroot_sign

example {f u v g a b : ℝ[X]}
    (_hg : g.Splits)
    (_hdegg : 2 ≤ g.natDegree)
    (_hdeg_g_lo : g.natDegree ≤ (a * g + b * g.derivative).natDegree)
    (_hdeg_g_hi : (a * g + b * g.derivative).natDegree ≤ g.natDegree + 1)
    (_hG_pos : HasPosLeadingCoeff (a * g + b * g.derivative))
    (_hg_pos : HasPosLeadingCoeff g)
    (_hroot_sign_g :
      ∀ r, g.IsRoot r → b.eval r * (g.derivative.eval r) ^ 2 < 0)
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_same

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_succ

example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  rr_prec_evalCoeff_nonpos using
    interlaces := hgf,
    source_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    coeff_nonpos := hb_nonpos

example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  rr_prec_evalCoeff_nonpos using
    interlaces := hgf,
    source_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    coeff_nonpos := hb_nonpos

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_mw_derivative_nonpos using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    coeff_nonpos := hv_nonpos

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_mw_derivative_nonpos using
    splits := hf,
    degree_two := hdegf,
    degree := hdeg,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    coeff_nonpos := hv_nonpos

/-- The bare derivative form selects indexed certificates for the displayed
target despite unrelated local families. -/
example {P Q U V : Nat → ℝ[X]} {n : Nat}
    (_hQ_splits : ∀ k, (Q k).Splits)
    (hP_splits : ∀ k, (P k).Splits)
    (hP_degree : ∀ k, 2 ≤ (P k).natDegree)
    (hdeg_lo : ∀ k,
      (P k).natDegree ≤ (U k * P k + V k * (P k).derivative).natDegree)
    (hdeg_hi : ∀ k,
      (U k * P k + V k * (P k).derivative).natDegree ≤ (P k).natDegree + 1)
    (htarget_pos : ∀ k,
      HasPosLeadingCoeff (U k * P k + V k * (P k).derivative))
    (hsource_pos : ∀ k, HasPosLeadingCoeff (P k))
    (hcoeff : ∀ k r, (P k).IsRoot r → (V k).eval r ≤ 0) :
    Prec (P n) (U n * P n + V n * (P n).derivative) := by
  rr_mw_derivative_nonpos

/-- A successor-degree equality supplies both derivative-step degree bounds. -/
example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_mw_derivative_nonpos using degree := hdeg

/-- The generic bare form selects the displayed indexed interlacer despite an
unrelated local family. -/
example {P G H A B : Nat → ℝ[X]} {n : Nat}
    (_hdecoy : ∀ k, Interlaces (H k) (P k))
    (hinterlaces : ∀ k, Interlaces (G k) (P k))
    (hsource_pos : ∀ k, HasPosLeadingCoeff (G k))
    (hdeg_lo : ∀ k,
      (P k).natDegree ≤ (A k * P k + B k * G k).natDegree)
    (hdeg_hi : ∀ k,
      (A k * P k + B k * G k).natDegree ≤ (P k).natDegree + 1)
    (htarget_pos : ∀ k, HasPosLeadingCoeff (A k * P k + B k * G k))
    (hcoeff : ∀ k r, (P k).IsRoot r → (B k).eval r ≤ 0) :
    Prec (P n) (A n * P n + B n * G n) := by
  rr_prec_evalCoeff_nonpos

/-- A same-degree equality supplies both generic evaluation-step bounds. -/
example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  rr_prec_evalCoeff_nonpos using degree := hdeg

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

/-- Full sequence shell for weak Ma--Wang derivative recurrences with a
sequence-supplied coefficient sign certificate. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- A Ma--Wang `Prec` sequence feeds the generic finish tail directly. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
    rr_mw_derivative_nonpos_sequence using
      base := hbase,
      pos_lc := hpos,
      degree_two := hdeg_two,
      coeff_nonpos := hV,
      recurrence := hrec,
      degree_lower := hdeg_lo,
      degree_upper := hdeg_hi
  rr_finish using hprec

/-- The generic weak Ma--Wang sequence shell also closes real-rootedness of all
rows. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- A globally nonpositive derivative factor needs no root-window certificate. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the generic weak Ma--Wang sequence shell. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Family D shell: globally nonpositive negative-constant derivative term. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + C (-(c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_const_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Negative-constant derivative shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + C (-((n : ℝ) + 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_const_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the negative-constant derivative shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + C (-(c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_const_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the negative-constant shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + C (-((n : ℝ) + 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_const_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic negative-constant shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + C (-((n : ℝ) + 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_mw_derivative_neg_const_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Family D shell: globally nonpositive `-c_n X^2 P'` derivative term. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_X_sq_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The `-c_n X^2 P'` shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_X_sq_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the `-c_n X^2 P'` derivative shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_X_sq_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the `-c_n X^2 P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Strict-degree shortcut for the automatic `-c_n X^2 P'` real-rootedness
endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ

/-- Projection endpoint for the strict-degree `-c_n X^2 P'` shortcut. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_neg_X_sq_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ

/-- Projection endpoint for the automatic `-c_n X^2 P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Affine one-sided shell: `c_n(1+X)P'` on roots at most `-1`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_one_add_X_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The `c_n(1+X)P'` shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_one_add_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the `c_n(1+X)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_one_add_X_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the `c_n(1+X)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic `c_n(1+X)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Affine one-sided shell: `c_n(X-1)P'` on roots at most `1`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_sub_one_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The `c_n(X-1)P'` shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_sub_one_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the `c_n(X-1)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the `c_n(X-1)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic `c_n(X-1)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: the negative-constant sequence tactic accepts `-(C c_n)`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (-(C (c n))) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_const_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: the `-X^2` sequence tactic accepts `C(-c_n) * X^2`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (-(c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_X_sq_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: the `-X^2` sequence tactic accepts a negated product. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n) * X ^ 2)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_X_sq_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: unscaled `(1+X)P'` gets its own sequence wrapper. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (1 + X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_one_add_X_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the unscaled `(1+X)P'` sequence wrapper. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (1 + X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_one_add_X_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: scalar affine factors may appear with the scalar on the right. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + ((1 + X) * C (c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_one_add_X_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: unscaled `(X-1)P'` gets its own sequence wrapper. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X - 1) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_X_sub_one_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the unscaled `(X-1)P'` sequence wrapper. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X - 1) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_X_sub_one_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Regression: scalar `(X-1)` factors may appear with the scalar on the right. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + ((X - 1) * C (c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- OEIS Family A/B sequence shell:
`P_{n+2}=U_n P_{n+1}+c_n X(1-X)P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    roots_nonpos := hroots,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The same `X(1-X)` derivative shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    roots_nonpos := hroots,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic coefficient positivity also handles shifted quadratic factors
that occur after scalar recurrence normalization. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) - 1) * X * (1 - X)) *
            (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    roots_nonpos := hroots,
    recurrence := hrec,
    degree_succ := hdeg

/-- Real-rootedness endpoint for the `X(1-X)` derivative shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    roots_nonpos := hroots,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the `X(1-X)` derivative shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    roots_nonpos := hroots,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The generic sequence shell can derive the half-line root bound internally
from nonnegative coefficients of the current row. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonpos_of_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The nonnegative-coefficient generic shell also gives the row
real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonpos_of_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the nonnegative-coefficient generic shell. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonpos_of_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The generic nonnegative-coefficient shell can synthesize the derivative
factor sign condition. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the synthesized-sign generic shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The root-aware generic sequence shell allows the coefficient sign to use
both the root predicate and the internally derived `r <= 0` bound. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_on_roots using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonpos_on_roots := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the root-aware generic sequence shell. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonpos_on_roots := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Denominator-fused generic Ma--Wang shell with nonnegative coefficients. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := c,
    coeff_nonneg := hc,
    coeff_nonpos_of_nonpos := hV,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic coefficient side-goal for the denominator-fused generic
Ma--Wang shell. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := fun n : Nat => (n : ℝ) + 1,
    coeff_nonpos_of_nonpos := hV,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the denominator-fused generic Ma--Wang shell
with an explicit coefficient certificate. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := c,
    coeff_nonneg := hc,
    coeff_nonpos_of_nonpos := hV,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Sign-auto endpoint for a denominator-fused nonpositive derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := fun n : Nat => (n : ℝ) + 1,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Split-form sign-auto endpoint for a denominator-fused nonpositive
derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 - X),
    coeff := fun n : Nat => (n : ℝ) + 1,
    den := d,
    raw_coeff := b,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the sign-auto denominator-fused nonpositive
derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := fun n : Nat => (n : ℝ) + 1,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Split-form real-rootedness endpoint for the sign-auto denominator-fused
nonpositive derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 - X),
    coeff := fun n : Nat => (n : ℝ) + 1,
    den := d,
    raw_coeff := b,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the denominator-fused generic
Ma--Wang shell. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := (fun n : Nat => (n : ℝ) + 1),
    coeff_nonpos_of_nonpos := hV,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- OEIS Family B shell: `P_{n+2}=U_nP_{n+1}+X Q_n P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_X_mul_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the `X Q_n P'` shell. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_X_mul_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Touchard/Bell base shell: `P_{n+2}=U_nP_{n+1}+X P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the `X P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_X_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Strict-degree shortcut for the `X P'` Ma--Wang sequence shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ

/-- The strict-degree Ma--Wang shell feeds the generic interlacing finish. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
    rr_mw_derivative_X_sequence_nonneg using
      base := hbase,
      pos_lc := hpos,
      nonneg_coeffs := hnonneg,
      degree_two := hdeg_two,
      recurrence := hrec,
      degree_succ := hdeg_succ
  rr_finish using hprec, hdeg_succ

/-- Strict-degree real-rootedness endpoint for the `X P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_X_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ

/-- Projection endpoint for the `X P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_mw_derivative_X_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Positive-constant MW2 shell:
`P_{n+2}=U_nP_{n+1}+c_n X P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (C (c n) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Positive-constant MW2 shell with automatic scalar positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C ((n : ℝ) + 2) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the positive-constant MW2 shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (C (c n) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the positive-constant MW2 shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C ((n : ℝ) + 2) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic positive-constant MW2 shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C ((n : ℝ) + 2) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Scalar Family B shell:
`P_{n+2}=U_nP_{n+1}+c_n X Q_n P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_mul_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the scalar Family B shell with an explicit
coefficient-positivity certificate. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The scalar Family B shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the scalar Family B shell. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic scalar Family B shell. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Denominator-fused scalar Family B shell. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := c,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic coefficient side-goal for the denominator-fused scalar
Family B shell. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := fun n : Nat => (n : ℝ) + 1,
    factor_nonneg := hQ,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the denominator-fused scalar Family B shell
with an explicit coefficient certificate. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := c,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic denominator-fused scalar Family B endpoint. -/
example {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := (fun n : Nat => (n : ℝ) + 1),
    factor_nonneg := hQ,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Inner-window shell:
`P_{n+2}=U_nP_{n+1}+X(1+X)P'_{n+1}`, with roots in `[-1,0]`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_X_one_add_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the inner-window `X(1+X)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_X_one_add_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Scalar inner-window shell:
`P_{n+2}=U_nP_{n+1}+c_n X(1+X)P'_{n+1}`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Scalar inner-window shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the scalar inner-window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the scalar inner-window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic scalar inner-window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Outer-window shell:
`P_{n+2}=U_nP_{n+1}-c_n X(1+X)P'_{n+1}`, with roots in `(-∞,-1]`. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_X_one_add_outer_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Outer-window shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C ((n : ℝ) + 1)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_neg_X_one_add_outer_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the outer-window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Automatic real-rootedness endpoint for the outer-window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C ((n : ℝ) + 1)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic outer-window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C ((n : ℝ) + 1)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Streamlined OEIS Family A/B shell:
`P_{n+2}=U_n P_{n+1}+c_n X(1-X)P'_{n+1}`, with the root interval derived
from row nonnegative coefficients. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- The streamlined `X(1-X)` shell with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the streamlined `X(1-X)` shell with an
explicit coefficient-positivity certificate. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- `A008517`: real-rootedness endpoint for the `c_n X(1-X)P'` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- `A059340`: a globally nonpositive shifted-square derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-((1 + X : ℝ[X]) ^ 2)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_global_nonpos_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => -((1 + X : ℝ[X]) ^ 2),
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the automatic streamlined `X(1-X)` shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C ((n : ℝ) + 1) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

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

/-- Combined Ma--Wang/Liu--Wang sequence shell with automatic nonnegative-root
sign side-goals. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Root-upper combined Ma--Wang/Liu--Wang sequence shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (1 + X) * (P (n + 1)).derivative +
          (1 + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the combined nonnegative-root shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the root-upper combined shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (1 + X) * (P (n + 1)).derivative +
          (1 + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Root-window combined Ma--Wang/Liu--Wang sequence shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative +
          (X * (1 + C (4 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the root-window combined shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative +
          (X * (1 + C (4 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized combined Ma--Wang/Liu--Wang shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the denominator-normalized combined shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Root-window denominator-normalized combined shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) *
            ((X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 1) * ((X * (1 + C (4 : ℝ) * X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    lag_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 3),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 1,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the root-window denominator-normalized
combined shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) *
            ((X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 1) * ((X * (1 + C (4 : ℝ) * X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    lag_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 3),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 1,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

end Tactic
end RealRooted
