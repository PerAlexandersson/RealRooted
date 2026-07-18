import RealRooted.Tactic.Derivative

/-!
# Derivative tactic examples

Small regression examples for derivative interlacing and side goals.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hsplits : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Interlaces p.derivative p := by
  rr_derivative_interlaces using
    splits := hsplits,
    degree_two := hdeg

example {p : ℝ[X]} (hsplits : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Interlaces p.derivative p := by
  rr_derivative_interlaces using
    splits := hsplits

example {p : ℝ[X]} (hsplits : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Prec p.derivative p := by
  rr_derivative_prec using
    splits := hsplits,
    degree_two := hdeg

example {p : ℝ[X]} (hsplits : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Prec p.derivative p := by
  rr_derivative_prec using
    splits := hsplits

example {p : ℝ[X]} (hnn : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.derivative := by
  rr_nonneg_coeffs_derivative using
    nonneg_coeffs := hnn

example {p : ℝ[X]} (hpos : HasPosLeadingCoeff p) (hdeg : p.natDegree ≠ 0) :
    HasPosLeadingCoeff p.derivative := by
  rr_pos_lc_derivative using
    pos_lc := hpos,
    degree_ne_zero := hdeg

example {p : ℝ[X]} (hpos : HasPosLeadingCoeff p) (hdeg : p.natDegree ≠ 0) :
    HasPosLeadingCoeff p.derivative := by
  rr_pos_lc_derivative using
    pos_lc := hpos

example {p : ℝ[X]} (hpos : HasPosLeadingCoeff p) (hdeg : 2 ≤ p.natDegree) :
    HasPosLeadingCoeff p.derivative := by
  rr_pos_lc_derivative using
    pos_lc := hpos

example {p : ℝ[X]} (hdeg : p.natDegree ≠ 0) :
    p.derivative ≠ 0 := by
  rr_derivative_ne_zero using
    degree_ne_zero := hdeg

example {p : ℝ[X]} (hdeg : p.natDegree ≠ 0) :
    p.derivative ≠ 0 := by
  rr_derivative_ne_zero

example {p : ℝ[X]} (hdeg : 2 ≤ p.natDegree) :
    p.derivative ≠ 0 := by
  rr_derivative_ne_zero

end Tactic
end RealRooted
