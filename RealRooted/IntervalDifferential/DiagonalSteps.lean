/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.EndpointWeight
public import RealRooted.Basic.ProperPosition
public import RealRooted.Basic.Coefficients
import RealRooted.Interlacing.OuterDifference
import RealRooted.Interlacing.Residue
import RealRooted.Interlacing.Multiplicity
import RealRooted.SimpleRoots
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.MaWang.StrictSigns.Assembly
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Universal diagonal first-order interlacing steps

We prove the sufficient direction of Theorem 3 in Section 2 of the unpublished
manuscript `long-cycle-eulerian-compat/NOTES.md` (RealRooted issue #2669).
For `T = (X² - 1) ∂ + c X - a` and `R = (X² - 1) ∂ + d X - b`,
the condition `|c s - a - (d s - b) - s| ≤ 1` on `(-1, 1)` transports
strict interlacing of interval-rooted polynomials from `(F, E)` to `(T F, R E)`.

The library predicate `Interlaces` permits common and repeated roots. We pair
it with `IsCoprime` to express strict interlacing; together these imply simple
roots. The proof uses positive Lagrange residues and signs at the roots of
`R E`, rather than stability of an operator on a larger polynomial domain.
-/

public noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- Linear insertion multiplies the leading coefficient by `degree + c`. -/
theorem intervalLinearFactor_leadingCoeff (c a : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F ≠ 0) :
    (intervalLinearFactor c a F).leadingCoeff =
      ((F.natDegree : ℝ) + c) * F.leadingCoeff := by
  have ht : (1 * (F.natDegree : ℝ) + c) * F.leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hF)
  have hd := natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
    F (-F.derivative) 0 1 (-a) c
    (by rw [natDegree_neg]; exact (natDegree_derivative_le F).trans (Nat.sub_le _ _)) ht
  have heq :
      (C 0 * X + C 1 * X ^ 2) * F.derivative +
        (C (-a) + C c * X) * F + -F.derivative = intervalLinearFactor c a F := by
    simp only [intervalLinearFactor, intervalOperator_apply, map_zero, map_one, map_neg,
      zero_mul, zero_add, one_mul]
    ring
  simpa only [heq, one_mul] using hd.2

/-- Positive endpoint weight preserves positive leading coefficient. -/
theorem intervalLinearFactor_hasPosLeadingCoeff (c a : ℝ) {F : ℝ[X]} (hc : 0 < c)
    (hF : HasPosLeadingCoeff F) : HasPosLeadingCoeff (intervalLinearFactor c a F) := by
  change 0 < (intervalLinearFactor c a F).leadingCoeff
  rw [intervalLinearFactor_leadingCoeff c a F hc hF.ne_zero]
  exact mul_pos (by positivity) hF

/-- The endpoint bounds make the residue kernel strictly positive for interior roots. -/
private theorem diagonal_kernel_pos {s r w : ℝ}
    (hs : -1 < s ∧ s < 1) (hr : -1 < r ∧ r < 1) (hw : |w - s| ≤ 1) :
    0 < 1 - s ^ 2 + w * (s - r) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hw
  by_cases hsr : r ≤ s
  · have hprod := mul_nonneg (show 0 ≤ w - (s - 1) by linarith)
      (sub_nonneg.mpr hsr)
    have hpos := mul_pos (show 0 < 1 - s by linarith) (show 0 < 1 + r by linarith)
    nlinarith
  · have hprod := mul_nonneg (show 0 ≤ s + 1 - w by linarith)
      (show 0 ≤ r - s by linarith)
    have hpos := mul_pos (show 0 < 1 + s by linarith) (show 0 < 1 - r by linarith)
    nlinarith

/-- Evaluation of a root-deleted input gives the first-order diagonal kernel. -/
private theorem cofactor_diagonal_identity (c a d b s r : ℝ) {E : ℝ[X]}
    (hr : E.IsRoot r) :
    (s - r) ^ 2 * (intervalLinearFactor c a (E /ₘ (X - C r))).eval s =
      (s - r) * (intervalLinearFactor d b E).eval s +
        E.eval s * (1 - s ^ 2 + (c * s - a - (d * s - b)) * (s - r)) := by
  have hfactor := mul_divByMonic_eq_iff_isRoot.mpr hr
  conv_rhs => rw [← hfactor]
  simp only [intervalLinearFactor_eval, eval_mul, eval_sub, eval_X, eval_C,
    derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    one_mul, eval_add]
  ring

/-- A positive diagonal kernel makes every root-deletion image have the old value's sign. -/
private theorem cofactor_diagonal_mul_pos (c a d b s r : ℝ) {E : ℝ[X]}
    (hs : -1 < s ∧ s < 1) (hr : -1 < r ∧ r < 1)
    (hw : |c * s - a - (d * s - b) - s| ≤ 1)
    (hEr : E.IsRoot r) (hEs : E.eval s ≠ 0)
    (hR : (intervalLinearFactor d b E).eval s = 0) :
    0 < (intervalLinearFactor c a (E /ₘ (X - C r))).eval s * E.eval s := by
  have hid := cofactor_diagonal_identity c a d b s r hEr
  rw [hR, mul_zero, zero_add] at hid
  have hk := diagonal_kernel_pos hs hr hw
  have hpos := mul_pos (sq_pos_of_ne_zero hEs) hk
  have heq : (s - r) ^ 2 *
      ((intervalLinearFactor c a (E /ₘ (X - C r))).eval s * E.eval s) =
      E.eval s ^ 2 * (1 - s ^ 2 + (c * s - a - (d * s - b)) * (s - r)) := by
    linear_combination E.eval s * hid
  rw [← heq] at hpos
  exact pos_of_mul_pos_right hpos (sq_nonneg (s - r))

/-- Insertion commutes with the finite Lagrange residue expansion. -/
private theorem intervalLinearFactor_lagInterp (c a : ℝ) (E F : ℝ[X]) :
    intervalLinearFactor c a (lagInterp E F) =
      ∑ r ∈ E.roots.toFinset, C (F.eval r / E.derivative.eval r) *
        intervalLinearFactor c a (E /ₘ (X - C r)) := by
  classical
  have hscalar (t : ℝ) (P : ℝ[X]) :
      intervalOperator c (C t * P) = C t * intervalOperator c P := by
    rw [← smul_eq_C_mul, (intervalOperator c).map_smul, smul_eq_C_mul]
  simp only [intervalLinearFactor, lagInterp, map_sum, Finset.mul_sum, hscalar,
    ← Finset.sum_sub_distrib, mul_sub]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Positive input residues and kernels give the required strict sign at every new root. -/
private theorem diagonal_eval_mul_pos (c a d b s : ℝ) {F E : ℝ[X]}
    (hFE : Interlaces F E) (hcop : IsCoprime F E)
    (hFpos : HasPosLeadingCoeff F) (hEpos : HasPosLeadingCoeff E)
    (hEi : ∀ r ∈ E.roots, -1 < r ∧ r < 1)
    (hs : -1 < s ∧ s < 1) (hEs : E.eval s ≠ 0)
    (hw : |c * s - a - (d * s - b) - s| ≤ 1)
    (hR : (intervalLinearFactor d b E).eval s = 0) :
    0 < (intervalLinearFactor c a F).eval s * E.eval s := by
  classical
  have hsimple := hFE.toStrictInterl.hasSimpleRoots_of_isCoprime hcop
  have hdegree : F.degree < E.natDegree :=
    (degree_le_natDegree).trans_lt (by
      have hd : F.natDegree < E.natDegree := by have he := hFE.2.2.1; lia
      exact_mod_cast hd)
  have hEdegree : 1 ≤ E.natDegree := by have hd := hFE.2.2.1; lia
  have hexp := lagInterp_eq_g hFE.1.2 hsimple.2.roots_nodup hEdegree hdegree
  rw [← hexp, intervalLinearFactor_lagInterp]
  rw [eval_finsetSum, Finset.sum_mul]
  apply Finset.sum_pos
  · intro r hr
    have hEr : E.IsRoot r := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    have hresprod := hFE.toStrictInterl.eval_mul_derivative_pos_of_right_root_of_isCoprime
      hFpos hEpos hcop hEr
    have hres : 0 < F.eval r / E.derivative.eval r :=
      (div_pos_iff).mpr (mul_pos_iff.mp hresprod)
    have hk := cofactor_diagonal_mul_pos c a d b s r hs
      (hEi r (Multiset.mem_toFinset.mp hr)) hw hEr hEs hR
    rw [eval_mul, eval_C, mul_assoc]
    exact mul_pos hres hk
  · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero
      (hFE.1.2.roots_ne_zero (by lia))
    exact ⟨r, Multiset.mem_toFinset.mpr hr⟩

/-- The sufficient diagonal criterion: affine interval steps preserve coprime
successor-degree interlacing and keep every root strictly in `(-1, 1)`.
Coprimeness with interlacing implies simplicity of both input and output roots.
This is Theorem 3, sufficient direction, in the unpublished manuscript cited above. -/
theorem intervalLinearFactor_interlaces (c a d b : ℝ) {F E : ℝ[X]}
    (ha : |a| < c) (hb : |b| < d)
    (hbound : ∀ s : ℝ, -1 < s → s < 1 → |c * s - a - (d * s - b) - s| ≤ 1)
    (hFE : Interlaces F E) (hcop : IsCoprime F E)
    (hFpos : HasPosLeadingCoeff F) (hEpos : HasPosLeadingCoeff E)
    (hFi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hEi : ∀ r ∈ E.roots, -1 < r ∧ r < 1) :
    Interlaces (intervalLinearFactor c a F) (intervalLinearFactor d b E) ∧
      IsCoprime (intervalLinearFactor c a F) (intervalLinearFactor d b E) ∧
      (∀ r ∈ (intervalLinearFactor c a F).roots, -1 < r ∧ r < 1) ∧
      ∀ r ∈ (intervalLinearFactor d b E).roots, -1 < r ∧ r < 1 := by
  have hc : 0 < c := (abs_nonneg a).trans_lt ha
  have hd : 0 < d := (abs_nonneg b).trans_lt hb
  have hsimple := hFE.toStrictInterl.hasSimpleRoots_of_isCoprime hcop
  have hTgood := intervalLinearFactor_roots c a F hc hFE.2.1.2 hFE.2.1.1
    hsimple.1.roots_nodup hFi (abs_lt.mp ha)
  have hRgood := intervalLinearFactor_roots d b E hd hFE.1.2 hFE.1.1
    hsimple.2.roots_nodup hEi (abs_lt.mp hb)
  have hTpos := intervalLinearFactor_hasPosLeadingCoeff c a hc hFpos
  have hRpos := intervalLinearFactor_hasPosLeadingCoeff d b hd hEpos
  have hdegree : (intervalLinearFactor c a F).natDegree <
      (intervalLinearFactor d b E).natDegree := by
    rw [intervalLinearFactor_natDegree c a F hc hFE.2.1.1,
      intervalLinearFactor_natDegree d b E hd hFE.1.1]
    have he := hFE.2.2.1
    lia
  have hsign (s : ℝ) (hRs : (intervalLinearFactor d b E).IsRoot s) :
      0 < (intervalLinearFactor c a F).eval s *
        (intervalLinearFactor d b E).derivative.eval s := by
    have hs := hRgood.2.2 s ((mem_roots hRpos.ne_zero).mpr hRs)
    have hEs := intervalLinearFactor_eval_base_ne_zero d b s E hFE.1.1
      hsimple.2.roots_nodup hEi hRs
    have hval := diagonal_eval_mul_pos c a d b s hFE hcop hFpos hEpos hEi hs hEs
      (hbound s hs.1 hs.2) hRs
    have hder := intervalLinearFactor_eval_derivative_mul_pos d b s E hd
      hFE.1.2 hEi hEs hRs
    have hprod : 0 < ((intervalLinearFactor c a F).eval s *
        (intervalLinearFactor d b E).derivative.eval s) * E.eval s ^ 2 := by
      nlinarith [mul_pos hval hder]
    exact pos_of_mul_pos_left hprod (sq_nonneg (E.eval s))
  have hout := (interlaces_and_isCoprime_iff_eval_mul_derivative_pos
    hRgood.1 hTpos hRpos hdegree).mpr hsign
  exact ⟨hout.1, hout.2, hTgood.2.2, hRgood.2.2⟩

/-- The unshifted long-cycle and Eulerian steps `(L, M)` transport strict
interval interlacing, where `L = (X² - 1) ∂ + 4 X` and `M = (X² - 1) ∂ + 2 X`. -/
theorem intervalOperator_four_interlaces_two {F E : ℝ[X]}
    (hFE : Interlaces F E) (hcop : IsCoprime F E)
    (hFpos : HasPosLeadingCoeff F) (hEpos : HasPosLeadingCoeff E)
    (hFi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hEi : ∀ r ∈ E.roots, -1 < r ∧ r < 1) :
    Interlaces (intervalOperator 4 F) (intervalOperator 2 E) ∧
      IsCoprime (intervalOperator 4 F) (intervalOperator 2 E) ∧
      (∀ r ∈ (intervalOperator 4 F).roots, -1 < r ∧ r < 1) ∧
      ∀ r ∈ (intervalOperator 2 E).roots, -1 < r ∧ r < 1 := by
  have hbound (s : ℝ) (hsL : -1 < s) (hsR : s < 1) :
      |4 * s - 0 - (2 * s - 0) - s| ≤ 1 := by
    rw [show 4 * s - 0 - (2 * s - 0) - s = s by ring]
    exact (abs_lt.mpr ⟨hsL, hsR⟩).le
  simpa only [intervalLinearFactor, map_zero, zero_mul, sub_zero] using
    intervalLinearFactor_interlaces 4 0 2 0 (by norm_num) (by norm_num) hbound
      hFE hcop hFpos hEpos hFi hEi

end RealRooted.IntervalDifferential
