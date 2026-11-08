module

public import RealRooted.Basic.Coefficients
import RealRooted.Derivative.Algebra
public import RealRooted.Basic.ProperPosition
import RealRooted.Derivative.LinearCombination
import RealRooted.ObreschkoffConverse.DegreeGap
import RealRooted.ObreschkoffConverse.Derivative
import RealRooted.QuadraticInterlacingClosure
import RealRooted.WagnerX.AffineFactors
import RealRooted.Mathlib.Probability.CoeffDistribution

/-!
# A power, derivative shift, and iterated derivative operator

We package the operator

`f ↦ D^m ((D + c) (X^m f))`.

It preserves splitting for nonzero `c`, preserves nonnegative coefficients for
positive `c`, and transports directed weak interlacing.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The operator `f ↦ D^m ((D + c) (X^m f))`. -/
@[expose] def powerDerivativeShift (m : ℕ) (c : ℝ) (f : ℝ[X]) : ℝ[X] :=
  derivative^[m] (C c * (X ^ m * f) + (X ^ m * f).derivative)

/-- For one inserted power of `X`, the operator is the corresponding
second-order differential expression. -/
theorem powerDerivativeShift_one (c : ℝ) (f : ℝ[X]) :
    powerDerivativeShift 1 c f =
      C c * f + (C c * X + 2) * f.derivative + X * f.derivative.derivative := by
  simp [powerDerivativeShift, derivative_add, derivative_mul]
  ring

/-- A nonzero derivative shift followed by as many derivatives as the inserted
power of `X` preserves splitting. -/
theorem powerDerivativeShift_splits {f : ℝ[X]} (hf : f.Splits) (m : ℕ)
    {c : ℝ} (hc : c ≠ 0) :
    (powerDerivativeShift m c f).Splits := by
  apply Polynomial.Splits.iterate_derivative
  exact splits_C_mul_add_derivative ((Polynomial.Splits.X_pow m).mul hf) hc

/-- For positive shift parameter, the power derivative shift preserves
coefficientwise nonnegativity. -/
theorem powerDerivativeShift_hasNonnegCoeffs {f : ℝ[X]}
    (hf : HasNonnegCoeffs f) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    HasNonnegCoeffs (powerDerivativeShift m c f) := by
  apply HasNonnegCoeffs.iterate_derivative
  exact (hasNonnegCoeffs_C_mul hc.le ((hasNonnegCoeffs_X.pow m).mul hf)).add
    ((hasNonnegCoeffs_X.pow m).mul hf).derivative

private lemma C_mul_tDeriv_neg_inv (p : ℝ[X]) {c : ℝ} (hc : c ≠ 0) :
    C c * tDeriv (-c⁻¹) p = C c * p + p.derivative := by
  simp only [tDeriv, C_neg, neg_mul, sub_neg_eq_add, mul_add]
  congr 1
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]

private lemma powerDerivativeShift_source_degree_leadingCoeff
    {f : ℝ[X]} (hf : f ≠ 0) (m : ℕ) {c : ℝ} (hc : c ≠ 0) :
    let q := C c * (X ^ m * f) + (X ^ m * f).derivative
    q ≠ 0 ∧ q.natDegree = f.natDegree + m ∧
      q.leadingCoeff = c * f.leadingCoeff := by
  let r : ℝ[X] := X ^ m * f
  have hr_ne : r ≠ 0 := mul_ne_zero (pow_ne_zero m X_ne_zero) hf
  have hr_degree : r.natDegree = f.natDegree + m := by
    simp [r, natDegree_mul (pow_ne_zero m X_ne_zero) hf, Nat.add_comm]
  have hr_leadingCoeff : r.leadingCoeff = f.leadingCoeff := by
    simp [r]
  let q : ℝ[X] := C c * r + r.derivative
  have hq : q = C c * tDeriv (-c⁻¹) r := by
    change C c * r + r.derivative = C c * tDeriv (-c⁻¹) r
    exact (C_mul_tDeriv_neg_inv r hc).symm
  have hq_ne : q ≠ 0 := by
    rw [hq]
    exact mul_ne_zero (C_ne_zero.mpr hc) (tDeriv_ne_zero hr_ne)
  have hq_degree : q.natDegree = f.natDegree + m := by
    rw [hq, natDegree_C_mul hc, natDegree_tDeriv, hr_degree]
  have hq_leadingCoeff : q.leadingCoeff = c * f.leadingCoeff := by
    rw [hq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_tDeriv,
      hr_leadingCoeff]
  exact ⟨hq_ne, hq_degree, hq_leadingCoeff⟩

/-- The power derivative shift of a nonzero polynomial has the same degree as
the input polynomial. -/
theorem natDegree_powerDerivativeShift {f : ℝ[X]} (hf : f ≠ 0)
    (m : ℕ) {c : ℝ} (hc : c ≠ 0) :
    (powerDerivativeShift m c f).natDegree = f.natDegree := by
  obtain ⟨hq_ne, hq_degree, _⟩ :=
    powerDerivativeShift_source_degree_leadingCoeff hf m hc
  rw [powerDerivativeShift,
    natDegree_iterate_derivative_eq_sub hq_ne (by rw [hq_degree]; lia),
    hq_degree]
  lia

/-- The leading coefficient of the power derivative shift is the input leading
coefficient times `c` and the appropriate falling factorial. -/
theorem leadingCoeff_powerDerivativeShift {f : ℝ[X]} (hf : f ≠ 0)
    (m : ℕ) {c : ℝ} (hc : c ≠ 0) :
    (powerDerivativeShift m c f).leadingCoeff =
      c * ((f.natDegree + m).descFactorial m : ℝ) * f.leadingCoeff := by
  obtain ⟨_, hq_degree, hq_leadingCoeff⟩ :=
    powerDerivativeShift_source_degree_leadingCoeff hf m hc
  rw [leadingCoeff, natDegree_powerDerivativeShift hf m hc,
    powerDerivativeShift, coeff_iterate_derivative, nsmul_eq_mul]
  rw [← hq_degree, coeff_natDegree, hq_leadingCoeff]
  ring

/-- The power derivative shift of a nonzero polynomial is nonzero. -/
theorem powerDerivativeShift_ne_zero {f : ℝ[X]} (hf : f ≠ 0)
    (m : ℕ) {c : ℝ} (hc : c ≠ 0) :
    powerDerivativeShift m c f ≠ 0 := by
  have hfactor : ((f.natDegree + m).descFactorial m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by lia)).ne'
  rw [← leadingCoeff_ne_zero]
  rw [leadingCoeff_powerDerivativeShift hf m hc]
  exact mul_ne_zero (mul_ne_zero hc hfactor) (leadingCoeff_ne_zero.mpr hf)

/-- For positive shift parameter, the power derivative shift preserves a
positive leading coefficient. -/
theorem HasPosLeadingCoeff.powerDerivativeShift {f : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    HasPosLeadingCoeff (powerDerivativeShift m c f) := by
  have hf_ne : f ≠ 0 := leadingCoeff_ne_zero.mp hf.ne'
  have hfactor : 0 < ((f.natDegree + m).descFactorial m : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by lia)
  unfold HasPosLeadingCoeff at hf ⊢
  rw [leadingCoeff_powerDerivativeShift hf_ne m hc.ne']
  exact mul_pos (mul_pos hc hfactor) hf

/-- For positive shift parameter and nonnegative input coefficients, every
root of the power derivative shift is nonpositive. -/
theorem powerDerivativeShift_roots_nonpos {f : ℝ[X]}
    (hf : HasNonnegCoeffs f) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ r ∈ (powerDerivativeShift m c f).roots, r ≤ 0 := by
  intro r hr
  exact Polynomial.roots_nonpos_of_coeff_nonneg
    (powerDerivativeShift_hasNonnegCoeffs hf m hc) hr

/-- Applying the same power derivative shift to both members of an oriented
interlacing pair preserves the orientation. -/
theorem StrictInterl.powerDerivativeShift {f g : ℝ[X]}
    (hfg : StrictInterl f g) (m : ℕ) {c : ℝ} (hc : c ≠ 0) :
    StrictInterl (powerDerivativeShift m c f)
      (powerDerivativeShift m c g) := by
  have hX : StrictInterl (X ^ m * f) (X ^ m * g) :=
    hfg.mul_common_factor (pow_ne_zero m X_ne_zero) (Polynomial.Splits.X_pow m)
  have hshift := hX.tDeriv_common (-c⁻¹)
  have hscaled :
      StrictInterl (C c * tDeriv (-c⁻¹) (X ^ m * f))
        (C c * tDeriv (-c⁻¹) (X ^ m * g)) :=
    hshift.mul_common_factor (C_ne_zero.mpr hc) (Polynomial.Splits.C c)
  have hdegree : m ≤ (C c * tDeriv (-c⁻¹) (X ^ m * f)).natDegree := by
    rw [natDegree_C_mul hc, natDegree_tDeriv,
      natDegree_mul (pow_ne_zero m X_ne_zero) hfg.1.1, natDegree_X_pow]
    lia
  have hderivative :=
    StrictInterl.iterate_derivative_of_le_natDegree hscaled m hdegree
  rw [C_mul_tDeriv_neg_inv (X ^ m * f) hc,
    C_mul_tDeriv_neg_inv (X ^ m * g) hc] at hderivative
  exact hderivative

end RealRooted
