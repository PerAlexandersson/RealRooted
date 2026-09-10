import RealRooted.Tactic.MaWang.Steps

/-!
# Ma--Wang direct-step regression examples

Atomic, strict, same-degree, successor-degree, and two-term direct dispatcher
tests, including active coefficient and factor normalizations.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {n : Nat} : 0 ≤ (n : ℝ) + 1 := by rr_mw_active_nonneg_at n

example {n : Nat} : (n : ℝ) + 2 ≠ 0 := by rr_mw_active_den_at n

example : ∀ n : Nat, (n : ℝ) + 2 ≠ 0 := by rr_mw_active_den_all

example {n : Nat} : 1 - ((n : ℝ) + 3) ≠ 0 := by rr_scalar_active_den_at n

example : ∀ n : Nat, 1 - ((n : ℝ) + 3) ≠ 0 := by rr_scalar_active_den_all

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


end Tactic
end RealRooted
