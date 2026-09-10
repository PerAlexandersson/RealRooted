import RealRooted.Tactic.MaWang.Sequences

/-!
# OEIS test-bed Ma--Wang step examples

Regression examples for Ma--Wang step frontends in the OEIS test bed.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Ma--Wang Family A: Eulerian one-step differential factors -/

-- `A008517`: `v_n(t)=t(1-t)`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A120434`: permutations by big descents, again `v_n(t)=t(1-t)`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A156919`: Dirichlet-eta related table, `v_n(t)=2t(1-t)`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

/-! ## Ma--Wang Family B: half-line first-derivative factors -/

-- `A321966`: OEIS-stated conjecture target, `v_n(t)=2t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A322944`: OEIS-stated conjecture target, `v_n(t)=3t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (3 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A321966`: root-sign package once the current row has nonnegative coefficients.
example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

-- `A021009`/Family B: generic `t R(t)` once `R` is nonnegative at roots.
example {p q : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hq : ∀ r, p.IsRoot r → 0 ≤ q.eval r) :
    ∀ r, p.IsRoot r → (X * q : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_with_factor using hrr, hpnn, hq

/-! ## Ma--Wang Family C/D: signed and window first-derivative factors -/

-- `A049020`: `v_n(t)=1+t`, requiring roots at most `-1`.
example {p : ℝ[X]} (hroots : ∀ r, p.IsRoot r → r ≤ -1) :
    ∀ r, p.IsRoot r → (1 + X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_upper using hroots

-- `A154602`: `v_n(t)=2+2t`.
example {p : ℝ[X]} (hroots : ∀ r, p.IsRoot r → r ≤ -1) :
    ∀ r, p.IsRoot r → (C (2 : ℝ) * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_upper using hroots

-- `A341287`: `v_n(t)=t-1`.
example {p : ℝ[X]} (hroots : ∀ r, p.IsRoot r → r ≤ 1) :
    ∀ r, p.IsRoot r → (X - 1 : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_upper using hroots

-- `A112493`/`A131689`: MW3 inner case `v_n(t)=t+t^2=t(1+t)`.
example {r : ℝ} (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C (1 : ℝ) * X + C 1 * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hlo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hhi : ∀ r, f.IsRoot r → r ≤ 0)
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
    root_lower := hlo,
    root_upper := hhi

-- `A008970`/`A059427`: `v_n(t)=t-t^3=t(1-t)(1+t)` on `[-1,0]`.
example {p : ℝ[X]}
    (hlo : ∀ r, p.IsRoot r → -1 ≤ r)
    (hhi : ∀ r, p.IsRoot r → r ≤ 0) :
    ∀ r, p.IsRoot r → (X - X ^ 3 : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_window using hlo, hhi

-- `A008970`/`A059427`: full Ma--Wang shell for the actual derivative factor.
example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hlo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hhi : ∀ r, f.IsRoot r → r ≤ 0)
    (hdeg_lo : f.natDegree ≤ (u * f + (X - X ^ 3) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X - X ^ 3) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X - X ^ 3) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (X - X ^ 3) * f.derivative) := by
  rr_mw_derivative_sign_window using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_lower := hlo,
    root_upper := hhi

-- Family C2 direct-outer model: after sign normalization, `v_n(t)=-c*t*(1+t)`.
example {p : ℝ[X]} (hroots : ∀ r, p.IsRoot r → r ≤ -1) :
    ∀ r, p.IsRoot r → (-(C (2 : ℝ)) * X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_upper using hroots

-- Family C2 direct-outer Ma--Wang shell for the `A108426`/`A181996` bucket.
example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ≤ -1)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C (1 : ℝ)) * X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C (1 : ℝ)) * X * (1 + X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff (u * f + (-(C (1 : ℝ)) * X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C (1 : ℝ)) * X * (1 + X)) * f.derivative) := by
  rr_mw_derivative_neg_X_one_add_outer_auto using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    root_upper := hroots

-- `A106800`/`A021010`: `v_n(t)=-t^2`.
example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (-(C (1 : ℝ)) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C (1 : ℝ)) * X ^ 2) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C (1 : ℝ)) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C (1 : ℝ)) * X ^ 2) * f.derivative) := by
  rr_mw_derivative_neg_X_sq_auto using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos

-- `A395972`: `v_n(t)=-2t^2`.
example {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (-(C (2 : ℝ)) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C (2 : ℝ)) * X ^ 2) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C (2 : ℝ)) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    Prec f (u * f + (-(C (2 : ℝ)) * X ^ 2) * f.derivative) := by
  rr_mw_derivative_neg_X_sq_auto using
    splits := hf,
    degree_two := hdegf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos


end Tactic
end RealRooted
