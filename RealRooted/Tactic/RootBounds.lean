import RealRooted.Tactic.Sign
import RealRooted.Derivative
import RealRooted.WagnerX

/-!
# Root-bound certificate tactics

The common OEIS recurrence route uses nonnegative coefficients to propagate
the root interval `(-∞, 0]`.  This file packages the repeated step from
`p ≠ 0 ∧ p.Splits` and `HasNonnegCoeffs p` to nonpositive roots, and combines
it with `rr_sign` for coefficient-sign goals at roots.
-/

open Polynomial

namespace RealRooted

lemma root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs {p : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hp_splits hpnn r ((mem_roots hp_ne).mpr hr)

lemma root_nonpos_of_realrooted_of_nonneg_coeffs {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 :=
  root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs hrr.1 hrr.2 hpnn hr

/-- Shifted nonnegative coefficients give a left root bound in the original
variable.  If `p(t-a)` has nonnegative coefficients, then every real root of
`p(t)` is at most `-a`. -/
lemma root_le_neg_of_realrooted_of_shift_nonneg_coeffs {p : ℝ[X]} {a r : ℝ}
    (hrr : p ≠ 0 ∧ p.Splits) (hshift_nonneg : HasNonnegCoeffs (p.comp (X - C a)))
    (hr : p.IsRoot r) :
    r ≤ -a := by
  have hshift_rr : p.comp (X - C a) ≠ 0 ∧ (p.comp (X - C a)).Splits := by
    simpa [sub_eq_add_neg] using isRealRooted_comp_X_add_C hrr.1 hrr.2 (-a)
  have hshift_root : (p.comp (X - C a)).IsRoot (r + a) := by
    rw [Polynomial.IsRoot.def] at hr ⊢
    simpa [Polynomial.eval_comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hr
  have hnonpos :
      r + a ≤ 0 :=
    root_nonpos_of_realrooted_of_nonneg_coeffs hshift_rr hshift_nonneg hshift_root
  linarith

lemma roots_nonpos_derivative_of_splits_of_nonneg_coeffs {p : ℝ[X]}
    (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r ∈ p.derivative.roots, r ≤ 0 :=
  roots_nonpos_derivative_of_roots_nonpos hp_splits
    (roots_nonpos_of_nonneg_coeffs hp_splits hpnn)

lemma derivative_root_nonpos_of_splits_of_nonneg_coeffs {p : ℝ[X]}
    (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    (hp_der_ne : p.derivative ≠ 0) {r : ℝ}
    (hr : p.derivative.IsRoot r) :
    r ≤ 0 :=
  roots_nonpos_derivative_of_splits_of_nonneg_coeffs hp_splits hpnn r
    ((mem_roots hp_der_ne).mpr hr)

lemma derivative_root_nonpos_of_realrooted_of_nonneg_coeffs {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hp_der_ne : p.derivative ≠ 0) {r : ℝ}
    (hr : p.derivative.IsRoot r) :
    r ≤ 0 :=
  derivative_root_nonpos_of_splits_of_nonneg_coeffs hrr.2 hpnn hp_der_ne hr

namespace Tactic

syntax (name := rr_root_nonpos_realrooted)
  "rr_root_nonpos" " using " term ", " term ", " term : tactic

syntax (name := rr_root_nonpos_ne_splits)
  "rr_root_nonpos" " using " term ", " term ", " term ", " term : tactic

syntax (name := rr_root_nonpos_named)
  "rr_root_nonpos" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "root" ":=" term :
  tactic

syntax (name := rr_root_nonpos_auto) "rr_root_nonpos" : tactic

syntax (name := rr_root_le_neg_shift_named)
  "rr_root_le_neg_shift" " using "
    "realrooted" ":=" term ","
    "shift_nonneg" ":=" term ","
    "root" ":=" term :
  tactic

syntax (name := rr_derivative_root_nonpos_named)
  "rr_derivative_root_nonpos" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "derivative_ne" ":=" term ","
    "root" ":=" term :
  tactic

syntax (name := rr_derivative_root_nonpos_auto) "rr_derivative_root_nonpos" : tactic

syntax (name := rr_sign_at_roots)
  "rr_sign_at_roots" " using " term ", " term : tactic

syntax (name := rr_sign_at_roots_named)
  "rr_sign_at_roots" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_auto) "rr_sign_at_roots" : tactic

syntax (name := rr_sign_at_roots_factor)
  "rr_sign_at_roots_with_factor" " using " term ", " term ", " term : tactic

syntax (name := rr_sign_at_roots_factor_named)
  "rr_sign_at_roots_with_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_factor_auto)
  "rr_sign_at_roots_with_factor" " using "
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_lower)
  "rr_sign_at_roots_lower" " using " term : tactic

syntax (name := rr_sign_at_roots_lower_named)
  "rr_sign_at_roots_lower" " using "
    "root_lower" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_upper)
  "rr_sign_at_roots_upper" " using " term : tactic

syntax (name := rr_sign_at_roots_upper_named)
  "rr_sign_at_roots_upper" " using "
    "root_upper" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_window)
  "rr_sign_at_roots_window" " using " term ", " term : tactic

syntax (name := rr_sign_at_roots_window_named)
  "rr_sign_at_roots_window" " using "
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_root_nonpos using $hrr:term, $hnn:term, $hr:term) =>
      `(tactic|
        exact RealRooted.root_nonpos_of_realrooted_of_nonneg_coeffs
          $hrr $hnn $hr)
  | `(tactic| rr_root_nonpos using $hne:term, $hsplits:term, $hnn:term, $hr:term) =>
      `(tactic|
        exact RealRooted.root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs
          $hne $hsplits $hnn $hr)
  | `(tactic|
      rr_root_nonpos using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        root := $hr:term) =>
      `(tactic|
        rr_root_nonpos using $hrr, $hnn, $hr)
  | `(tactic| rr_root_nonpos) =>
      `(tactic|
        first
          | exact RealRooted.root_nonpos_of_realrooted_of_nonneg_coeffs
              (by assumption) (by assumption) (by assumption)
          | exact RealRooted.root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs
              (by assumption) (by assumption) (by assumption) (by assumption))
  | `(tactic|
      rr_root_le_neg_shift using
        realrooted := $hrr:term,
        shift_nonneg := $hnn:term,
        root := $hr:term) =>
      `(tactic|
        exact RealRooted.root_le_neg_of_realrooted_of_shift_nonneg_coeffs
          $hrr $hnn $hr)
  | `(tactic|
      rr_derivative_root_nonpos using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        derivative_ne := $hder_ne:term,
        root := $hr:term) =>
      `(tactic|
        exact RealRooted.derivative_root_nonpos_of_splits_of_nonneg_coeffs
          ($hrr).2 $hnn $hder_ne $hr)
  | `(tactic| rr_derivative_root_nonpos) =>
      `(tactic|
        exact RealRooted.derivative_root_nonpos_of_realrooted_of_nonneg_coeffs
          (by assumption) (by assumption) (by assumption) (by assumption))
  | `(tactic| rr_sign_at_roots using $hrr:term, $hnn:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_nonpos : r ≤ 0 := by
            rr_root_nonpos using $hrr, $hnn, hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots using
        realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        rr_sign_at_roots using $hrr, $hnn)
  | `(tactic| rr_sign_at_roots) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_nonpos : r ≤ 0 := by
            rr_root_nonpos
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_with_factor using $hrr:term, $hnn:term, $hq:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_nonpos : r ≤ 0 := by
            rr_root_nonpos using $hrr, $hnn, hroot
          have hfactor_nonneg := $hq r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_with_factor using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        factor_nonneg := $hq:term) =>
      `(tactic|
        rr_sign_at_roots_with_factor using $hrr, $hnn, $hq)
  | `(tactic|
      rr_sign_at_roots_with_factor using
        factor_nonneg := $hq:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_nonpos : r ≤ 0 := by
            rr_root_nonpos
          have hfactor_nonneg := $hq r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_lower using $hlo:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_lower := $hlo r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_lower using
        root_lower := $hlo:term) =>
      `(tactic|
        rr_sign_at_roots_lower using $hlo)
  | `(tactic|
      rr_sign_at_roots_upper using $hhi:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_upper := $hhi r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_upper using
        root_upper := $hhi:term) =>
      `(tactic|
        rr_sign_at_roots_upper using $hhi)
  | `(tactic|
      rr_sign_at_roots_window using $hlo:term, $hhi:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_lower := $hlo r hroot
          have hroot_upper := $hhi r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_window using
        root_lower := $hlo:term,
        root_upper := $hhi:term) =>
      `(tactic|
        rr_sign_at_roots_window using $hlo, $hhi)

end Tactic
end RealRooted
