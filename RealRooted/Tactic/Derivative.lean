import RealRooted.Derivative
import RealRooted.Tactic.Finish

/-!
# Derivative tactic frontends

Thin wrappers for derivative interlacing and routine derivative side goals.
-/

open Lean.Elab.Tactic
open Polynomial

namespace RealRooted
namespace Tactic

theorem derivative_sequence_interlaces
    {P : Nat → ℝ[X]}
    (hsplits : ∀ i : Nat, (P i).Splits)
    (hdeg : ∀ i : Nat, 2 ≤ (P i).natDegree) :
    ∀ i : Nat, Interlaces (P i).derivative (P i) := fun i =>
  RealRooted.derivative_interlaces (hsplits i) (hdeg i)

theorem derivative_prec {p : ℝ[X]}
    (hsplits : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Prec p.derivative p :=
  (RealRooted.derivative_interlaces hsplits hdeg).toPrec

theorem derivative_sequence_prec
    {P : Nat → ℝ[X]}
    (hsplits : ∀ i : Nat, (P i).Splits)
    (hdeg : ∀ i : Nat, 2 ≤ (P i).natDegree) :
    ∀ i : Nat, Prec (P i).derivative (P i) := fun i =>
  RealRooted.Tactic.derivative_prec (hsplits i) (hdeg i)

theorem nonnegCoeffs_sequence_derivative
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (P i).derivative := fun i =>
  RealRooted.HasNonnegCoeffs.derivative (hP i)

theorem pos_lc_sequence_derivative
    {P : Nat → ℝ[X]}
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≠ 0) :
    ∀ i : Nat, HasPosLeadingCoeff (P i).derivative := fun i =>
  RealRooted.HasPosLeadingCoeff.derivative (hpos i) (hdeg i)

theorem derivative_sequence_ne_zero
    {P : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (P i).natDegree ≠ 0) :
    ∀ i : Nat, (P i).derivative ≠ 0 := fun i =>
  Polynomial.derivative_ne_zero.mpr (hdeg i)

syntax (name := rr_derivative_interlaces_named)
  "rr_derivative_interlaces" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

syntax (name := rr_derivative_sequence_interlaces_named)
  "rr_derivative_sequence_interlaces" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

syntax (name := rr_derivative_interlaces_auto)
  "rr_derivative_interlaces" " using "
    "splits" ":=" term :
  tactic

syntax (name := rr_derivative_prec_named)
  "rr_derivative_prec" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

syntax (name := rr_derivative_sequence_prec_named)
  "rr_derivative_sequence_prec" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

syntax (name := rr_derivative_prec_auto)
  "rr_derivative_prec" " using "
    "splits" ":=" term :
  tactic

syntax (name := rr_nonneg_coeffs_derivative_named)
  "rr_nonneg_coeffs_derivative" " using "
    "nonneg_coeffs" ":=" term :
  tactic

syntax (name := rr_nonneg_coeffs_sequence_derivative_named)
  "rr_nonneg_coeffs_sequence_derivative" " using "
    "nonneg_coeffs" ":=" term :
  tactic

syntax (name := rr_pos_lc_derivative_named)
  "rr_pos_lc_derivative" " using "
    "pos_lc" ":=" term ","
    "degree_ne_zero" ":=" term :
  tactic

syntax (name := rr_pos_lc_sequence_derivative_named)
  "rr_pos_lc_sequence_derivative" " using "
    "pos_lc" ":=" term ","
    "degree_ne_zero" ":=" term :
  tactic

syntax (name := rr_pos_lc_derivative_auto)
  "rr_pos_lc_derivative" " using "
    "pos_lc" ":=" term :
  tactic

syntax (name := rr_derivative_ne_zero_named)
  "rr_derivative_ne_zero" " using "
    "degree_ne_zero" ":=" term :
  tactic

syntax (name := rr_derivative_sequence_ne_zero_named)
  "rr_derivative_sequence_ne_zero" " using "
    "degree_ne_zero" ":=" term :
  tactic

syntax (name := rr_derivative_ne_zero_auto)
  "rr_derivative_ne_zero" :
  tactic

macro_rules
  | `(tactic|
      rr_derivative_interlaces using
        splits := $hsplits:term,
        degree_two := $hdeg:term) =>
      `(tactic| exact RealRooted.derivative_interlaces $hsplits $hdeg)
  | `(tactic|
      rr_derivative_sequence_interlaces using
        splits := $hsplits:term,
        degree_two := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.derivative_sequence_interlaces $hsplits $hdeg)
  | `(tactic|
      rr_derivative_interlaces using
        splits := $hsplits:term) =>
      `(tactic| exact RealRooted.derivative_interlaces $hsplits (by rr_close_side))
  | `(tactic|
      rr_derivative_prec using
        splits := $hsplits:term,
        degree_two := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.derivative_prec $hsplits $hdeg)
  | `(tactic|
      rr_derivative_sequence_prec using
        splits := $hsplits:term,
        degree_two := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.derivative_sequence_prec $hsplits $hdeg)
  | `(tactic|
      rr_derivative_prec using
        splits := $hsplits:term) =>
      `(tactic|
        exact RealRooted.Tactic.derivative_prec $hsplits (by rr_close_side))
  | `(tactic|
      rr_nonneg_coeffs_derivative using
        nonneg_coeffs := $hnn:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.derivative $hnn)
  | `(tactic|
      rr_nonneg_coeffs_sequence_derivative using
        nonneg_coeffs := $hnn:term) =>
      `(tactic| exact RealRooted.Tactic.nonnegCoeffs_sequence_derivative $hnn)
  | `(tactic|
      rr_pos_lc_derivative using
        pos_lc := $hpos:term,
        degree_ne_zero := $hdeg:term) =>
      `(tactic| exact RealRooted.HasPosLeadingCoeff.derivative $hpos $hdeg)
  | `(tactic|
      rr_pos_lc_sequence_derivative using
        pos_lc := $hpos:term,
        degree_ne_zero := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.pos_lc_sequence_derivative $hpos $hdeg)
  | `(tactic|
      rr_pos_lc_derivative using
        pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.HasPosLeadingCoeff.derivative $hpos (by rr_close_side))
  | `(tactic|
      rr_derivative_ne_zero using
        degree_ne_zero := $hdeg:term) =>
      `(tactic| exact Polynomial.derivative_ne_zero.mpr $hdeg)
  | `(tactic|
      rr_derivative_sequence_ne_zero using
        degree_ne_zero := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.derivative_sequence_ne_zero $hdeg)
  | `(tactic| rr_derivative_ne_zero) =>
      `(tactic|
        exact Polynomial.derivative_ne_zero.mpr (by rr_close_side))

end Tactic
end RealRooted
