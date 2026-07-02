import RealRooted.Tactic.Sign
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

syntax (name := rr_sign_at_roots)
  "rr_sign_at_roots" " using " term ", " term : tactic

syntax (name := rr_sign_at_roots_named)
  "rr_sign_at_roots" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
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

end Tactic
end RealRooted
