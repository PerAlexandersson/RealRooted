import RealRooted.IteratedDerivativeShift
import RealRooted.PosCombo

/-!
# Linear combinations with a derivative

Splitting preservation for constant linear combinations of a polynomial and
its derivative. These theorem-facing forms are shared by Hermite--Poulain and
the second-derivative tactic frontend.
-/

open Polynomial

namespace RealRooted

/-- Positive plus-derivative preservation in the form needed by Laguerre/Rolle
style outer steps. -/
theorem splits_add_C_mul_derivative {p : ℝ[X]} (hp : p.Splits) {eps : ℝ}
    (heps : 0 < eps) :
    (p + C eps * p.derivative).Splits := by
  have hT : (TDeriv eps (p.comp (-X))).Splits :=
    splits_tderiv heps hp.comp_neg_X
  have hcomp : ((TDeriv eps (p.comp (-X))).comp (-X)).Splits :=
    hT.comp_neg_X
  convert hcomp using 1
  simp [TDeriv, Polynomial.derivative_comp, comp_assoc]

/-- Negative plus-derivative preservation, directly from the existing
`TDeriv` theorem. -/
theorem splits_add_C_mul_derivative_of_neg {p : ℝ[X]} (hp : p.Splits) {eps : ℝ}
    (heps : eps < 0) :
    (p + C eps * p.derivative).Splits := by
  have hT : (TDeriv (-eps) p).Splits :=
    splits_tderiv (neg_pos.mpr heps) hp
  convert hT using 1
  simp [TDeriv]

/-- Plus-derivative preservation for every real coefficient. -/
theorem splits_add_C_mul_derivative_all {p : ℝ[X]} (hp : p.Splits) (eps : ℝ) :
    (p + C eps * p.derivative).Splits := by
  rcases lt_trichotomy eps 0 with heps | heps | heps
  · exact splits_add_C_mul_derivative_of_neg hp heps
  · subst eps
    simpa using hp
  · exact splits_add_C_mul_derivative hp heps

/-- The scaled outer form `(a + D) p = a p + p'`, for every nonzero `a`. -/
theorem splits_C_mul_add_derivative {p : ℝ[X]} (hp : p.Splits) {a : ℝ}
    (ha : a ≠ 0) :
    (C a * p + p.derivative).Splits := by
  have hscaled : (p + C a⁻¹ * p.derivative).Splits :=
    splits_add_C_mul_derivative_all hp a⁻¹
  have hmul : (C a * (p + C a⁻¹ * p.derivative)).Splits :=
    (Polynomial.Splits.C (R := ℝ) a).mul hscaled
  have hEq : C a * (p + C a⁻¹ * p.derivative) = C a * p + p.derivative := by
    rw [mul_add]
    have hterm : C a * (C a⁻¹ * p.derivative) = p.derivative := by
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
    rw [hterm]
  simpa [hEq] using hmul

end RealRooted
