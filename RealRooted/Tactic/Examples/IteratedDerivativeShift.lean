import RealRooted.Tactic.IteratedDerivativeShift

open Polynomial

namespace RealRooted
namespace Tactic

example {eps : ℝ} {p : ℝ[X]} (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (TDeriv eps p) := by
  rr_TDeriv_pos_lc using pos_lc := hp

example {eps : ℝ} {p : ℝ[X]} (hp0 : p ≠ 0) :
    TDeriv eps p ≠ 0 := by
  rr_TDeriv_ne_zero using nonzero := hp0

example {eps : ℝ} {p : ℝ[X]} (heps : 0 < eps) (hp : p.Splits) :
    (TDeriv eps p).Splits := by
  rr_TDeriv_splits using eps_pos := heps, splits := hp

example {eps : ℝ} {p : ℝ[X]} (heps : 0 < eps) (hp0 : p ≠ 0)
    (hp : p.Splits) :
    Prec p (TDeriv eps p) := by
  rr_TDeriv_prec using eps_pos := heps, nonzero := hp0, splits := hp

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) :
    iterateTDeriv eps k p ≠ 0 := by
  rr_iterateTDeriv_ne_zero using nonzero := hp0

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} (heps : 0 < eps) (hp : p.Splits) :
    (iterateTDeriv eps k p).Splits := by
  rr_iterateTDeriv_splits using eps_pos := heps, splits := hp

example {eps : ℝ} {p : ℝ[X]} {n : ℕ} (heps : 0 < eps) (hp0 : p ≠ 0)
    (hp : p.Splits) :
    Prec (iterateTDeriv eps n p) (iterateTDeriv eps (n + 1) p) := by
  rr_iterateTDeriv_prec_succ using eps_pos := heps, nonzero := hp0, splits := hp

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} :
    (iterateTDeriv eps k p).natDegree = p.natDegree := by
  rr_iterateTDeriv_natDegree

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} :
    (iterateTDeriv eps k p).leadingCoeff = p.leadingCoeff := by
  rr_iterateTDeriv_leadingCoeff

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp : p.Monic) :
    (iterateTDeriv eps k p).Monic := by
  rr_iterateTDeriv_monic using monic := hp

example (eps : ℝ) (p q : ℝ[X]) :
    TDeriv eps (p + q) = TDeriv eps p + TDeriv eps q := by
  rr_TDeriv_add

example (eps c : ℝ) (p : ℝ[X]) :
    TDeriv eps (C c * p) = C c * TDeriv eps p := by
  rr_TDeriv_C_mul

example (eps : ℝ) (n : ℕ) (p q : ℝ[X]) :
    iterateTDeriv eps n (p + q) = iterateTDeriv eps n p + iterateTDeriv eps n q := by
  rr_iterateTDeriv_add

example (eps c : ℝ) (n : ℕ) (p : ℝ[X]) :
    iterateTDeriv eps n (C c * p) = C c * iterateTDeriv eps n p := by
  rr_iterateTDeriv_C_mul

example (eps : ℝ) (p : ℝ[X]) :
    (TDeriv eps p).derivative = TDeriv eps p.derivative := by
  rr_derivative_TDeriv

example (eps : ℝ) (k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (TDeriv eps p) = TDeriv eps ((derivative^[k]) p) := by
  rr_iterate_derivative_TDeriv

example (eps : ℝ) (n k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (iterateTDeriv eps n p) =
      iterateTDeriv eps n ((derivative^[k]) p) := by
  rr_iterate_derivative_iterateTDeriv

end Tactic
end RealRooted
