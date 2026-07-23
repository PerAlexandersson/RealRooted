import RealRooted.Tactic.Favard
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.MaWang
import RealRooted.Tactic.RootBounds
import RealRooted.Tactic.SecondDerivative

/-!
# OEIS recurrence test bed

Executable side-condition tests for selected OEIS recurrences from the
`real-rooted-oeis` project.  These are not full sequence formalizations yet:
they record the certificate fragments that the tactic layer should dispatch
once each OEIS family exposes its recurrence identity, degree data, root
interval, and base cases.
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

/-! ## Ma--Wang sequence-level OEIS smoke tests -/

-- `A145901`/`A186695`: inner-window shape `2t(1+t)P'`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + C (2 : ℝ) * X) * P (n + 1) +
          (C (2 : ℝ) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg

-- `A284861`: same inner-window proof path, but with `3t(1+t)P'`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + C (3 : ℝ) * X) * P (n + 1) +
          (C (3 : ℝ) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg

-- `A111999`: unscaled inner-window shape `t(1+t)P'`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (1 - 2 * ((n : ℝ) + 2)) +
            C (2 - 2 * ((n : ℝ) + 2)) * X) * P (n + 1) +
          (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_X_one_add_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg

-- `A194649`: window shape `(1+t)(1+2t)P'`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (3 : ℝ) + C (4 : ℝ) * X) * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_one_add_two_window_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg

-- `A102365`: half-line factor `2t-t^2=t(2-t)` with no denominator.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (C (2 : ℝ) - X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A142963`: half-line factor `t-4t^2=t(1-4t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (C (1 : ℝ) - C (4 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A156920`: half-line factor `t-2t^2=t(1-2t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (C (1 : ℝ) - C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A290315`: half-line factor `2t-4t^2=2t(1-2t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (C (1 : ℝ) - C (2 : ℝ) * X)) *
            (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A290316`: half-line factor `3t-9t^2=3t(1-3t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (3 : ℝ) * X * (C (1 : ℝ) - C (3 : ℝ) * X)) *
            (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A257608`: half-line factor `9t-9t^2=9t(1-t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (C (9 : ℝ) - C (9 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A257614`: half-line factor `5t-5t^2=5t(1-t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (C (5 : ℝ) - C (5 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A257621`: half-line factor `4t-4t^2=4t(1-t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (4 : ℝ) * X * (C (1 : ℝ) - X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A257626`: half-line factor `3t-3t^2=3t(1-t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (C (3 : ℝ) - C (3 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A156366`: half-line factor `t-3t^2=t(1-3t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (C (1 : ℝ) - C (3 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A257620`: half-line factor `3t-3t^2=3t(1-t)`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (3 : ℝ) * X * (C (1 : ℝ) - X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A062190`: negative scalar denominator after the active shift.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C (1 - (3 / 4 : ℝ) * ((n : ℝ) + 2) -
          (1 / 4 : ℝ) * ((n : ℝ) + 2) ^ 2) * P (n + 2) =
        C (1 - (3 / 4 : ℝ) * ((n : ℝ) + 2) -
          (1 / 4 : ℝ) * ((n : ℝ) + 2) ^ 2) *
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

-- `A062196`: quadratic scalar denominator with `t(1-t)P'`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((((n : ℝ) + 3) * ((n : ℝ) + 5) / 3)) * P (n + 2) =
        C ((((n : ℝ) + 3) * ((n : ℝ) + 5) / 3)) * (U n * P (n + 1)) +
          C (2 * ((n : ℝ) + 4) / 3) *
            ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 - X),
    coeff := fun n => (2 * ((n : ℝ) + 4)) / (((n : ℝ) + 3) * ((n : ℝ) + 5)),
    den := fun n => (((n : ℝ) + 3) * ((n : ℝ) + 5) / 3),
    raw_coeff := fun n => 2 * ((n : ℝ) + 4) / 3,
    raw_recurrence := hraw,
    degree_succ := hdeg

-- `A357613`: positive scalar denominator, leaving the derivative sign
-- certificate as a separate family-specific obligation.
example {P RHS : Nat → ℝ[X]}
    (hraw : ∀ n : Nat,
      C (1 + 3 * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) * P (n + 1) =
        C (1 + 3 * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) * RHS n) :
    ∀ n : Nat, P (n + 1) = RHS n := by
  intro n
  rr_mw_den_norm using
    recurrence := hraw n,
    den_nonzero := rr_mw_active_den_at_term n

-- `A361893`: split scalar denominator normalizing into `-c_n t^2 P'`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C (1 - (1 / 2 : ℝ) * ((n : ℝ) + 3)) * P (n + 2) =
        C (1 - (1 / 2 : ℝ) * ((n : ℝ) + 3)) * (U n * P (n + 1)) +
          C (((n : ℝ) + 2) / 2) * (X ^ 2 * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  have hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-(C (((n : ℝ) + 2) / ((n : ℝ) + 1))) * X ^ 2) *
            (P (n + 1)).derivative := by
    intro n
    have hden : 1 - (1 / 2 : ℝ) * ((n : ℝ) + 3) ≠ 0 := by
      rr_mw_active_den_at n
    have hscalar :
        (1 - (1 / 2 : ℝ) * ((n : ℝ) + 3))⁻¹ * (((n : ℝ) + 2) / 2) =
          -(((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      rr_scalar_coeff_at n
    have hrec0 :
        P (n + 2) =
          U n * P (n + 1) +
            C (-(((n : ℝ) + 2) / ((n : ℝ) + 1))) *
              (X ^ 2 * (P (n + 1)).derivative) := by
      rr_mw_den_norm_coeff using
        recurrence := hraw n,
        den_nonzero := hden,
        coeff_eq := hscalar
    simpa [mul_assoc, C_neg] using hrec0
  rr_mw_derivative_neg_X_sq_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg

-- `A375853`: active shift of
-- `(n-1)P_n=(n+2+(3n-2)t)P_{n-1}+2t(1-t)P'_{n-1}`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) * (U n * P (n + 1)) +
          C (2 : ℝ) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := fun n => (2 : ℝ) / ((n : ℝ) + 1),
    raw_recurrence := hraw,
    degree_succ := hdeg

-- `A114655`: active shift of
-- `(n+1)P_n=(3nt+2n-3t+2)P_{n-1}+2t(2-t)P'_{n-1}`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) * ((X * (C (2 : ℝ) - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    raw_recurrence := hraw,
    degree_succ := hdeg

/-! ## Ma--Wang plus Liu--Wang derivative-lag recurrences -/

-- Direct root-sign route for the combined wrapper, independent of
-- nonnegative-coefficient root bounds.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroots,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- Real-rooted projection endpoint for the same direct root-sign route.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_upper := hroots,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- Root-window route for I2-type derivative-lag recurrences.
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

-- Denominator-fused root-window route for the same I2 sign pattern.
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

-- `A144438`: `P_n=(1-t+nt)P_{n-1}+t(1-t)P'_{n-1}+tP_{n-2}`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative +
          X * P n)
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

-- Scalar-denominator presentation of the `A144438` derivative-lag shape.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) * ((X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * (X * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 - X),
    lag_factor := fun _ => X,
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- Reordered raw denominator recurrence with two nontrivial normalized
-- coefficients.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 1) * (X * P n) +
          C (2 : ℝ) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 - X),
    lag_factor := fun _ => X,
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 3),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A144436`: same derivative term with lag coefficient `4t`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative +
          (C (4 : ℝ) * X) * P n)
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

-- `A046739`: active shift gives lag coefficient `(n+4)t`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative +
          (C ((n : ℝ) + 4) * X) * P n)
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

-- `A271697`: the active shift has lag coefficient `nt`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative +
          (C (n : ℝ) * X) * P n)
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

-- `A271698`: one further active shift makes the lag coefficient `nt`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative +
          (C (n : ℝ) * X) * P n)
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

-- `A395454`: active shift gives lag coefficient `2nt`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * (1 - X)) * (P (n + 1)).derivative +
          (C (2 * (n : ℝ)) * X) * P n)
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

/-! ## Liu--Wang Family E: positive `t`-lag factors -/

-- `A049403`: `B_n(t)=(n-1)t`.
example {n : Nat} (hn : 1 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 1) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A049403`: root-sign package with the active-range scalar certificate.
example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    {n : Nat} (hn : 1 ≤ n) :
    ∀ r, p.IsRoot r → (C ((n : ℝ) - 1) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

-- `A061896`: Lucas-polynomial coefficient triangle, `B_n(t)=t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A100862`: matching polynomial triangle, `B_n(t)=(n-2)t`.
example {n : Nat} (hn : 2 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A154227`: triangular-number lag coefficient, `B_n(t)=n(n+1)t/2`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n : ℝ) * ((n : ℝ) + 1)) / 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A154228`: square-pyramidal lag coefficient, `B_n(t)=n(n+1)(2n+1)t/6`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) / 6) * X :
      ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A249248`: shifted positive lag coefficient, `B_n(t)=(n+2)t`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) + 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A154986`: active coefficient `(m-1)(m-2)t`, after the row shift.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (((n : ℝ) + 2) ^ 2 - 3 * ((n : ℝ) + 2) + 2) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_one_add_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A334823`: `P_m=(1+2m)P_{m-1}-t^2P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (1 + 2 * ((n : ℝ) + 2)) * P (n + 1) +
          (-(C (1 : ℝ)) * X ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A334824`: same negative-square lag with current factor `3+2m`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (3 + 2 * ((n : ℝ) + 2)) * P (n + 1) +
          (-(C (1 : ℝ)) * X ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-! ## Liu--Wang Family G: Narayana/Jacobi negative-square lag factors -/

-- `A001263`: Narayana/Catalan rows, `B_n(t)=-(n/(n+3))(1-t)^2`.
example {n : Nat} {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) + 3))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A001263`: denominator-fused Narayana lag after the active row shift.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 5) * P (n + 2) =
        C ((n : ℝ) + 5) * (A n * P (n + 1)) +
          C ((n : ℝ) + 2) * (-((1 - X : ℝ[X]) ^ 2) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 2) / ((n : ℝ) + 5),
    raw_coeff := fun n => (n : ℝ) + 2,
    den := fun n => (n : ℝ) + 5,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A091044`: Pascal odd-entry triangle, `B_n(t)=-(1-t)^2`.
example {r : ℝ} :
    (-(C (1 : ℝ)) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A086645`/`A091042`: expanded `B_n(t)=-1+2t-t^2`.
example {r : ℝ} :
    (C (-1 : ℝ) + C (2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A090181`: denominator-fused Narayana variant with half-scaled denominator.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (((n : ℝ) + 4) / 2) * P (n + 2) =
        C (((n : ℝ) + 1) / 2) * (-((1 - X : ℝ[X]) ^ 2) * P n) +
          C (((n : ℝ) + 4) / 2) * (A n * P (n + 1)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 4),
    raw_coeff := fun n => ((n : ℝ) + 1) / 2,
    den := fun n => ((n : ℝ) + 4) / 2,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A145596`: generalized Narayana rows, `B_n(t)=-(n/(n+3))(1-t)^2`.
example {n : Nat} {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) + 3))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A145596`: denominator-fused generalized Narayana lag.  The active left
-- denominator and raw lag coefficient are both negative.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (-(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3)) * P (n + 2) =
        C (-(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3)) * (A n * P (n + 1)) +
          C (-(((n : ℝ) + 2) * ((n : ℝ) + 1) / 3)) *
            (-((1 - X : ℝ[X]) ^ 2) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 2) / ((n : ℝ) + 5),
    raw_coeff := fun n => -(((n : ℝ) + 2) * ((n : ℝ) + 1) / 3),
    den := fun n => -(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A178343`: beta-binomial rows, `B_n(t)=-(n/(n-1))(1-t)^2`, active for `n>=2`.
example {n : Nat} (hn : 2 ≤ n) {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) - 1))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A178343`: denominator-fused beta-binomial lag after the active row shift.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (((n : ℝ) + 1) ^ 2) * P (n + 2) =
        C (((n : ℝ) + 1) ^ 2) * (A n * P (n + 1)) +
          C (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
            (-((1 - X : ℝ[X]) ^ 2) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 2) / ((n : ℝ) + 1),
    raw_coeff := fun n => ((n : ℝ) + 2) * ((n : ℝ) + 1),
    den := fun n => ((n : ℝ) + 1) ^ 2,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-! ## Favard/Chebyshev Family F dispatcher skeleton -/

-- `A157077`: scalar denominator followed by positive-slope Favard.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        C (1 - ((n : ℝ) + 3)) *
          (((C (((4 * (n.succ : ℝ) + 2) / ((n.succ : ℝ) + 1))) * X -
                C (0 : ℝ)) *
              P (n + 1) -
            C ((4 * (n.succ : ℝ)) / ((n.succ : ℝ) + 1)) * P n))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun _ => (0 : ℝ),
    beta := fun m => (4 * (m : ℝ)) / ((m : ℝ) + 1),
    base_zero := hP0,
    base_one := by
      norm_num
      simpa using hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

-- `A063007`: raw scalar-denominator Favard numerator with nonzero shift.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X - C (-1 : ℝ))
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        (C (6 - 4 * ((n : ℝ) + 3)) * X +
            C (3 - 2 * ((n : ℝ) + 3))) * P (n + 1) +
          C (-2 + ((n : ℝ) + 3)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun m => -((2 * (m : ℝ) + 1) / ((m : ℝ) + 1)),
    beta := fun m => (m : ℝ) / ((m : ℝ) + 1),
    raw_slope := fun n => 6 - 4 * ((n : ℝ) + 3),
    raw_const := fun n => 3 - 2 * ((n : ℝ) + 3),
    raw_lag := fun n => -2 + ((n : ℝ) + 3),
    base_zero := hP0,
    base_one := by simpa using hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

-- `A376467`: same denominator-Favard normalization with a larger shift.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X - C (-3 : ℝ))
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        (C (6 - 4 * ((n : ℝ) + 3)) * X +
            C (9 - 6 * ((n : ℝ) + 3))) * P (n + 1) +
          C (-2 + ((n : ℝ) + 3)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun m => -((6 * (m : ℝ) + 3) / ((m : ℝ) + 1)),
    beta := fun m => (m : ℝ) / ((m : ℝ) + 1),
    raw_slope := fun n => 6 - 4 * ((n : ℝ) + 3),
    raw_const := fun n => 9 - 6 * ((n : ℝ) + 3),
    raw_lag := fun n => -2 + ((n : ℝ) + 3),
    base_zero := hP0,
    base_one := by simpa using hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

-- `A049310`: Chebyshev `S(n,x)=U(n,x/2)` coefficient triangle.
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

-- `A049310`/`A124038`: `P_{n+2}=tP_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat, P (n + 2) = X * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A053122`: `P_{n+2}=(t-2)P_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (2 : ℝ))
    (hstep : ∀ n : Nat, P (n + 2) = (X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A078812`: `P_{n+2}=(t+2)P_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-2 : ℝ))
    (hstep : ∀ n : Nat, P (n + 2) = (X - C (-2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_unit using
    alpha := -2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A124039`: row-sign normalized Chebyshev step `P_{n+2}=-tP_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat, P (n + 2) = -X * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_row_sign_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A124039`: real-rootedness endpoint for the same row-sign normalization.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat, P (n + 2) = -X * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_row_sign_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A053117`/`A053120`: `P_{n+2}=2tP_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat, P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using
    slope := 2,
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A053124`/`A084930`: `P_{n+2}=(4t-2)P_{n+1}-P_n`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (4 : ℝ) * X - C (2 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) = (C (4 : ℝ) * X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_const_unit using
    slope := 4,
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A137286`: parameterized Favard step `P_m=tP_{m-1}-(m+1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) - C (((n + 1 : Nat) : ℝ) + 2) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun _ : Nat => (0 : ℝ),
    beta := fun m : Nat => (m : ℝ) + 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A137338`: parameterized Favard step `P_m=(t+1-m)P_{m-1}-(m-1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
        C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-! ### Family F promoted scalar-lag extension scan -/

-- `A049218`: active scalar-lag Favard shell
-- `P_m=tP_{m-1}-m(m+1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        X * P (n + 1) -
          C (((((n + 1 : Nat) : ℝ) + 1) * (((n + 1 : Nat) : ℝ) + 2))) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun _ : Nat => (0 : ℝ),
    beta := fun m : Nat => ((m : ℝ) + 1) * ((m : ℝ) + 2),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A094816`: shifted active range of
-- `P_m=(t+m-1)P_{m-1}-(m-2)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-1 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (-((((n + 1 : Nat) : ℝ) + 1)))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => -((m : ℝ) + 1),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A136532`: scalar-denominator row-sign Favard raw numerator.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 =
      -(C ((4 : ℝ) / 3) * X - C ((16 : ℝ) / 3)))
    (hraw : ∀ n : Nat,
      C (1 + ((n + 2 : Nat) : ℝ) / 2) * P (n + 2) =
        (C (-((((n : ℝ) + 5) / 2))) * X +
            C (((n : ℝ) + 3) * ((n : ℝ) + 5))) * P (n + 1) +
          C (-((((n : ℝ) + 3) * ((n : ℝ) + 4) * ((n : ℝ) + 5)) / 2)) *
            P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_raw_auto using
    slope := fun m : Nat => ((m : ℝ) + 4) / ((m : ℝ) + 3),
    alpha := fun m : Nat => 2 * ((m : ℝ) + 2) * ((m : ℝ) + 4) / ((m : ℝ) + 3),
    beta := fun m : Nat => ((m : ℝ) + 2) * ((m : ℝ) + 4),
    raw_slope := fun n : Nat => -(((n : ℝ) + 5) / 2),
    raw_const := fun n : Nat => ((n : ℝ) + 3) * ((n : ℝ) + 5),
    raw_lag := fun n : Nat =>
      -((((n : ℝ) + 3) * ((n : ℝ) + 4) * ((n : ℝ) + 5)) / 2),
    base_zero := hP0,
    base_one := by
      norm_num
      simpa using hP1,
    den := fun n : Nat => 1 + ((n + 2 : Nat) : ℝ) / 2,
    raw_recurrence := hraw

-- `A136668`: `P_m=2mtP_{m-1}-(m+1)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 * (((n + 1 : Nat) : ℝ) + 1)) * X) * P (n + 1) -
          C ((((n + 1 : Nat) : ℝ) + 2)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_auto using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun _ : Nat => (0 : ℝ),
    beta := fun m : Nat => (m : ℝ) + 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A181332`: constant affine Favard row `P_m=(t+3)P_{m-1}-2P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-3 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (-3 : ℝ)) * P (n + 1) - C (2 : ℝ) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_auto using
    alpha := -3,
    beta := 2,
    base_zero := hP0,
    base_one := by simpa using hP1,
    step := hstep

-- `A199577`: shifted active shell
-- `P_m=(t-3-2m)P_{m-1}-(m+1)^2P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (5 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (2 * ((n + 1 : Nat) : ℝ) + 5)) * P (n + 1) -
          C (((((n + 1 : Nat) : ℝ) + 2) ^ 2)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => 2 * (m : ℝ) + 5,
    beta := fun m : Nat => ((m : ℝ) + 2) ^ 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A269951`: shifted active range of
-- `P_m=(t+m-1)P_{m-1}-(m-3)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-2 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (-((((n + 1 : Nat) : ℝ) + 2)))) * P (n + 1) -
          C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => -((m : ℝ) + 2),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A285072`: `P_m=(2-t)P_{m-1}-P_{m-2}`, another row-sign Favard case.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (2 : ℝ)))
    (hstep : ∀ n : Nat, P (n + 2) = -(X - C (2 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_row_sign_unit using
    alpha := 2,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A327997`: shifted active range of
-- `P_m=(t+m+1)P_{m-1}-3(m-2)P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (-3 : ℝ))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (X - C (-((((n + 1 : Nat) : ℝ) + 3)))) * P (n + 1) -
          C (3 * ((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_auto using
    alpha := fun m : Nat => -((m : ℝ) + 3),
    beta := fun m : Nat => 3 * (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- `A137338`-shaped row-sign surface for n-dependent Favard coefficients.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat,
      P (n + 2) = -(X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
        C (((n + 1 : Nat) : ℝ)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

-- Unit-lag shortcut for A124039-type row-sign Favard shifts.
example {P : Nat → ℝ[X]} {α : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(X - C (α (n + 1))) * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_unit using
    alpha := α,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-! ## Fresh promoted-sequence batch: positive `t`-lag rows -/

-- `A026729`/`A370173`: `P_n=tP_{n-1}+tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = X * P (n + 1) + (C (1 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A099089`: `P_n=2tP_{n-1}+tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (C (1 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_CX_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A099091`: `P_n=2tP_{n-1}+3tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (C (3 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_current_CX_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A099092`: `P_n=2tP_{n-1}+4tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (C (4 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_CX_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A099093`: `P_n=3tP_{n-1}+3tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (3 : ℝ) * X) * P (n + 1) + (C (3 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_current_CX_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A099095`: `P_n=3tP_{n-1}+2tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (3 : ℝ) * X) * P (n + 1) + (C (2 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_CX_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A099097`: `P_n=3tP_{n-1}+tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (3 : ℝ) * X) * P (n + 1) + (C (1 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_current_CX_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A153520`: `P_n=(1+t)P_{n-1}+7tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (7 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_one_add_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A153521`: `P_n=(1+t)P_{n-1}+11tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (11 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_current_one_add_X_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A179900`: `P_n=(5-t)P_{n-1}-P_{n-2}`, a negative-slope Favard row-sign case.
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (5 : ℝ)))
    (hstep : ∀ n : Nat, P (n + 2) = -(X - C (5 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_const_row_sign_unit using
    alpha := 5,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-! ## LS4 second-derivative factorization shells -/

-- `A271703`: unsigned Lah shape
-- `P_{n+2}=X f+2X f'+X f''=(1+D)((X-1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        X * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A271704`/`A271705`: unsigned Lah LS4 shell plus the current row
-- `(1+X)f+2Xf'+Xf''=f+(1+D)((X-1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (houter_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (C (1 : ℝ) *
            ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X - C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (houter_prec : ∀ n : Nat,
      Prec (P (n + 1))
        (C (1 : ℝ) *
            ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X - C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_ls4_plus_current_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    tail := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_pos_lc := houter_pos,
    outer_prec := houter_prec,
    recurrence := hrec

-- `A105278`: Lah-type row
-- `P_{n+2}=(2+X)f+(2+2X)f'+Xf''=(1+D)((X+1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) + X) * P (n + 1) +
          (C (2 : ℝ) + C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A079640`: Stirling-first/Lah product, LS4 shell plus an indexed current row
-- `(n+3+X)f+(2+2X)f'+Xf''=(n+1)f+(1+D)((X+1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (houter_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (C (1 : ℝ) *
            ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X + C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (houter_prec : ∀ n : Nat,
      Prec (P (n + 1))
        (C (1 : ℝ) *
            ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X + C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C ((n : ℝ) + 3) + X) * P (n + 1) +
          (C (2 : ℝ) + C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_ls4_plus_current_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    tail := fun n => (n : ℝ) + 1,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_pos_lc := houter_pos,
    outer_prec := houter_prec,
    recurrence := hrec

-- `A048854`: generalized Lah `L[4,1]`
-- `(2+X)f+(8+8X)f'+16Xf''=(1/4+D)(4(X-2)f+16Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (4 : ℝ) * (X - C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) + X) * P (n + 1) +
          (C (8 : ℝ) + C (8 : ℝ) * X) * (P (n + 1)).derivative +
            (C (16 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (4 : ℝ) * (X - C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (4 : ℝ) * (X - C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 4),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A088729`: doubled derivative branch
-- `(3+X)f+(4+3X)f'+2Xf''=(1+D)((X+2)f+2Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((X + C (2 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (3 : ℝ)) * P (n + 1) +
          (C (4 : ℝ) + C (3 : ℝ) * X) * (P (n + 1)).derivative +
            (C (2 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((X + C (2 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((X + C (2 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A286724`: half-step Lah branch
-- `(2+X)f+(4+4X)f'+4Xf''=(1/2+D)(2Xf+4Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (2 : ℝ) * X) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (2 : ℝ)) * P (n + 1) +
          (C (4 : ℝ) + C (4 : ℝ) * X) * (P (n + 1)).derivative +
            (C (4 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (2 : ℝ) * X) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (2 : ℝ) * X) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 2),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A290596`: third-step Lah branch with translated inner factor
-- `(2+X)f+(6+6X)f'+9Xf''=(1/3+D)(3(X-1)f+9Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (3 : ℝ) * (X - C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (2 : ℝ)) * P (n + 1) +
          (C (6 : ℝ) + C (6 : ℝ) * X) * (P (n + 1)).derivative +
            (C (9 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (3 : ℝ) * (X - C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (3 : ℝ) * (X - C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 3),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A290598`: third-step Lah branch with positive translated inner factor
-- `(4+X)f+(12+6X)f'+9Xf''=(1/3+D)(3(X+1)f+9Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (3 : ℝ) * (X + C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (4 : ℝ)) * P (n + 1) +
          (C (12 : ℝ) + C (6 : ℝ) * X) * (P (n + 1)).derivative +
            (C (9 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (3 : ℝ) * (X + C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (3 : ℝ) * (X + C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 3),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A292219`: fourth-step Lah branch
-- `(6+X)f+(24+8X)f'+16Xf''=(1/4+D)(4(X+2)f+16Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (4 : ℝ) * (X + C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (6 : ℝ)) * P (n + 1) +
          (C (24 : ℝ) + C (8 : ℝ) * X) * (P (n + 1)).derivative +
            (C (16 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (4 : ℝ) * (X + C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (4 : ℝ) * (X + C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 4),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A059110`: shifted Lah window
-- `(1+X)f+(2+2X)f'+(1+X)f''=(1+D)(Xf+(1+X)f')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_le_neg_one : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (X * P (n + 1) + (1 + X : ℝ[X]) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (2 : ℝ) + C (2 : ℝ) * X) * (P (n + 1)).derivative +
            (1 + X : ℝ[X]) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (X * P (n + 1) + (1 + X : ℝ[X]) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (X * P (n + 1) + (1 + X : ℝ[X]) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_upper := hroots_le_neg_one,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A111596`: inverse-Lah stage recurrence
-- `Xf-2Xf'+Xf''=(-1+D)(-(X+1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ r)
    (hinner_neg : ∀ n : Nat,
      HasPosLeadingCoeff
        (-((-(X + C (1 : ℝ))) * P (n + 1) + X * (P (n + 1)).derivative)))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        X * P (n + 1) -
          (C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((-(X + C (1 : ℝ))) * P (n + 1) + X * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((-(X + C (1 : ℝ))) * P (n + 1) + X * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_neg_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (-1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_neg_lc := hinner_neg,
    root_nonneg := hroots_nonneg,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A176231`: even Hermite coefficient triangle
-- `(X-1)f+(2-4X)f'+4Xf''=(-1/2+D)(-2(X+1)f+4Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ r)
    (hinner_neg : ∀ n : Nat,
      HasPosLeadingCoeff
        (-((-(C (2 : ℝ) * (X + C (1 : ℝ)))) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative)))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X - C (1 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) - C (4 : ℝ) * X) * (P (n + 1)).derivative +
            (C (4 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((-(C (2 : ℝ) * (X + C (1 : ℝ)))) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((-(C (2 : ℝ) * (X + C (1 : ℝ)))) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_neg_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (-(1 : ℝ) / 2),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_neg_lc := hinner_neg,
    root_nonneg := hroots_nonneg,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

end Tactic
end RealRooted
