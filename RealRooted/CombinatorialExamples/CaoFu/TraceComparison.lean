/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.MinimumMatrix
public import RealRooted.CombinatorialExamples.CaoFu.TracePolynomial
import RealRooted.CombinatorialExamples.CaoFu.FormalCosine
import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerTraceSeries
import Mathlib.Tactic

/-!
# The trace comparison in the Cao--Fu representation

We identify the polynomial `E_r` with the power traces of the existing
minimum-entry transfer matrix, as in Cao--Fu, arXiv:2610.40496v1,
Lemmas 3.1--3.2. Newton's identity and the formal cosine identity reduce
the comparison to the checked Lagrange coefficient formula.
-/

public section
noncomputable section
open PowerSeries RealRooted.CenteredEulerian
namespace RealRooted.CaoFu

private abbrev tangentProduct (m : ℝ) : ℝ⟦X⟧ :=
  C m * (sinS * secS) * rescale m (sinS * secS)

private theorem cosine_squared_mul_tangentProduct_one :
    cosS ^ 2 * tangentProduct 1 = sinS ^ 2 := by
  simp only [tangentProduct, map_one, rescale_one, RingHom.id_apply, one_mul]
  have h := cosS_mul_secS
  linear_combination (cosS * secS + 1) * sinS ^ 2 * h

private theorem determinant_mul_cosine_squared_mul_tangentProduct (N : ℕ) :
    (traceDenominator N).eval₂ PowerSeries.C (4 * sinS ^ 2) * cosS ^ 2 *
        tangentProduct (2 * (N : ℝ) + 1) =
      C (2 * (N : ℝ) + 1) * sinS * rescale (2 * (N : ℝ) + 1) sinS := by
  let m : ℝ := 2 * N + 1
  have hcos := traceDenominator_eval_sinS_sq_mul_cosS N
  have hunit : rescale m cosS * rescale m secS = 1 := by
    rw [← map_mul, cosS_mul_secS, map_one]
  change (traceDenominator N).eval₂ PowerSeries.C (4 * sinS ^ 2) * cosS =
    rescale m cosS at hcos
  simp only [tangentProduct, map_mul]
  change _ = C m * sinS * rescale m sinS
  calc
    _ = C m * sinS *
        ((traceDenominator N).eval₂ PowerSeries.C (4 * sinS ^ 2) * cosS) *
        (cosS * secS) * rescale m sinS * rescale m secS := by ring
    _ = C m * sinS * rescale m sinS * (rescale m cosS * rescale m secS) := by
      rw [hcos, cosS_mul_secS]
      ring
    _ = _ := by rw [hunit, mul_one]

private theorem two_mul_traceSeries_subst (N : ℕ) :
    2 * (PowerSeries.mk (fun r => if r = 0 then 0 else
      Matrix.trace (minimumMatrix N ^ r))).subst (4 * sinS ^ 2) =
      tangentProduct (2 * (N : ℝ) + 1) - tangentProduct 1 := by
  let P : ℝ⟦X⟧ := traceDenominator N
  let T : ℝ⟦X⟧ := PowerSeries.mk (fun r => if r = 0 then 0 else
    Matrix.trace (minimumMatrix N ^ r))
  let z : ℝ⟦X⟧ := 4 * sinS ^ 2
  let F : ℝ⟦X⟧ := P.subst z
  have hz0 : constantCoeff z = 0 := by simp [z, constantCoeff_sinS]
  have hz := hasSubst_of_cc_zero hz0
  have hn := Matrix.det_mul_powerTraceSeries (minimumMatrix N)
  rw [det_one_sub_X_smul_minimumMatrix] at hn
  change P * T = -X * derivative P at hn
  have hnew := congrArg (substAlgHom hz) hn
  simp only [map_mul, map_neg, substAlgHom_X, coe_substAlgHom] at hnew
  change F * T.subst z = -z * (derivative P).subst z at hnew
  have hcos : F * cosS = rescale (2 * (N : ℝ) + 1) cosS := by
    simpa only [F, P, subst_coe hz, Polynomial.aeval_def, PowerSeries.algebraMap_eq, z] using
      traceDenominator_eval_sinS_sq_mul_cosS N
  have dz : derivative z = 8 * sinS * cosS := by
    dsimp [z]
    rw [show (4 : ℝ⟦X⟧) = C (4 : ℝ) by norm_num only [map_ofNat], derivative.leibniz,
      derivative_C, derivative_pow, derivative_sinS]
    norm_num [smul_eq_mul, map_ofNat]
    ring
  have hd := congrArg derivative hcos
  simp only [derivative.leibniz, smul_eq_mul, derivative_cosS,
    derivative_rescale_cosS] at hd
  rw [show derivative F = (derivative P).subst z * derivative z by
    exact derivative_subst hz, dz] at hd
  have hfm : F * cosS ^ 2 * tangentProduct (2 * (N : ℝ) + 1) =
      C (2 * (N : ℝ) + 1) * sinS * rescale (2 * (N : ℝ) + 1) sinS := by
    simpa only [F, P, subst_coe hz, Polynomial.aeval_def, PowerSeries.algebraMap_eq, z] using
      determinant_mul_cosine_squared_mul_tangentProduct N
  have hF : F ≠ 0 := by
    intro h
    have h0 := congrArg constantCoeff h
    rw [show constantCoeff F = 1 by
      change constantCoeff (PowerSeries.subst z (traceDenominator N : ℝ⟦X⟧)) = 1
      rw [constantCoeff_subst_eq hz0, Polynomial.constantCoeff_coe]
      exact traceDenominator_coeff_zero N] at h0
    norm_num at h0
  have hC : cosS ≠ 0 := by
    intro h
    have h0 := congrArg constantCoeff h
    rw [constantCoeff_cosS] at h0
    norm_num at h0
  apply mul_left_cancel₀ (mul_ne_zero hF (pow_ne_zero _ hC))
  change (F * cosS ^ 2) * (2 * T.subst z) =
    (F * cosS ^ 2) * (tangentProduct (2 * (N : ℝ) + 1) - tangentProduct 1)
  change F * T.subst z = -(4 * sinS ^ 2) * (derivative P).subst z at hnew
  linear_combination 2 * cosS ^ 2 * hnew - sinS * hd - hfm +
    F * cosine_squared_mul_tangentProduct_one

private theorem coeff_subst_four_X_sq (T : ℝ⟦X⟧) (r : ℕ) :
    coeff (2 * r) (T.subst (4 * X ^ 2)) = (4 : ℝ) ^ r * coeff r T := by
  have hz : constantCoeff (4 * X ^ 2 : ℝ⟦X⟧) = 0 := by simp
  rw [coeff_subst_eq_sum hz T (le_refl (2 * r)), Finset.sum_eq_single r]
  · rw [mul_pow, ← pow_mul, show (4 : ℝ⟦X⟧) = C (4 : ℝ) by norm_num only [map_ofNat],
      ← map_pow, coeff_C_mul_X_pow, ite_eq_left rfl]
    ring
  · intro j _ hj
    rw [mul_pow, ← pow_mul, show (4 : ℝ⟦X⟧) = C (4 : ℝ) by norm_num only [map_ofNat],
      ← map_pow, coeff_C_mul_X_pow, ite_eq_right (by intro h; apply hj; lia), mul_zero]
  · simp only [Finset.mem_range, not_lt]
    intro hr
    have : r ≤ 2 * r := by lia
    exfalso
    lia

/-- The centered polynomial evaluated at an odd integer is the corresponding matrix power trace. -/
theorem centeredTracePolynomial_eval_eq_trace (n N : ℕ) :
    (centeredTracePolynomial n).eval (2 * (N : ℝ) + 1) =
      Matrix.trace (minimumMatrix N ^ (n + 1)) := by
  have h := two_mul_traceSeries_subst N
  have hf := hasSubst_of_cc_zero constantCoeff_fS
  have hz0 : constantCoeff (4 * sinS ^ 2 : ℝ⟦X⟧) = 0 := by simp [constantCoeff_sinS]
  have hsub := congrArg (substAlgHom hf) h
  rw [map_mul, map_ofNat, map_sub] at hsub
  simp only [coe_substAlgHom] at hsub
  rw [subst_comp_subst_apply (hasSubst_of_cc_zero hz0) hf] at hsub
  have hz : (4 * sinS ^ 2 : ℝ⟦X⟧).subst fS = 4 * X ^ 2 := by
    rw [subst_mul hf, subst_pow hf, sinS_subst_fS]
    simp only [← coe_substAlgHom hf, map_ofNat]
  rw [hz] at hsub
  have hc := congrArg (coeff (2 * (n + 1))) hsub
  rw [coeff_ofNat_mul, coeff_subst_four_X_sq, coeff_mk] at hc
  simp only [Nat.add_one_ne_zero, ite_false, map_sub] at hc
  rw [← cosecantPolynomial_eval_eq_coeff_tangent_subst_arcsin n (2 * (N : ℝ) + 1),
    ← cosecantPolynomial_eval_eq_coeff_tangent_subst_arcsin n 1,
    cosecantPolynomial_eval_one] at hc
  simp only [centeredTracePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_one]
  rw [one_div_mul_eq_div]
  apply (div_eq_iff (by positivity : (2 * (4 : ℝ) ^ (n + 1)) ≠ 0)).mpr
  linear_combination -hc

/-- The polynomial representation applies to the existing Cao--Fu transfer trace. -/
theorem transferTrace_eq_centeredTracePolynomial (r q : ℕ) (hr : r ≠ 0) :
    transferTrace r q = (centeredTracePolynomial (r - 1)).eval (2 * (q : ℝ) + 3) := by
  rw [transferTrace_eq_trace_minimumMatrix_pow]
  have h := centeredTracePolynomial_eval_eq_trace (r - 1) (q + 1)
  rw [show r - 1 + 1 = r by lia] at h
  convert h.symm using 1
  congr 1
  push_cast
  ring

end RealRooted.CaoFu
