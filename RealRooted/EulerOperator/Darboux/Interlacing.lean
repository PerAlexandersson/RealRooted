/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.EulerOperator.Darboux.Basic
import RealRooted.MaWang.DerivativeStep
import Mathlib.Tactic

/-!
# Interlacing consequences of unit-interval Darboux operators

This file separates the ordered real-root theory from the coefficient-ring
algebra in `RealRooted.EulerOperator.Darboux.Basic`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A sign-normalized Darboux output is in proper position when the input is
real-rooted on `[0,1]` and the expected degree and leading-coefficient data
hold. -/
theorem prec_neg_darbouxOperator_of_roots_mem_Icc
    {a b : ℝ} {p : ℝ[X]}
    (hp : p.Splits) (hdegp : 1 ≤ p.natDegree)
    (hp_pos : HasPosLeadingCoeff p)
    (houtput_pos : HasPosLeadingCoeff (-darbouxOperator a b p))
    (hdeg_lo : p.natDegree ≤ (-darbouxOperator a b p).natDegree)
    (hdeg_hi : (-darbouxOperator a b p).natDegree ≤ p.natDegree + 1)
    (hroots : ∀ r ∈ p.roots, 0 ≤ r ∧ r ≤ 1) :
    Prec p (-darbouxOperator a b p) := by
  have hrecur :
      -darbouxOperator a b p =
        (C (-a) + C b * X) * p + (-X * (1 - X)) * p.derivative := by
    apply Polynomial.funext
    intro x
    simp [darbouxOperator]
    ring
  rw [hrecur] at houtput_pos hdeg_lo hdeg_hi ⊢
  apply prec_mw_derivative_of_nonpos_of_pos_natDegree hp hdegp
      hdeg_lo hdeg_hi houtput_pos hp_pos
  intro r hr
  have hr_mem : r ∈ p.roots := (mem_roots hp_pos.ne_zero).mpr hr
  have hr_window := hroots r hr_mem
  simp only [eval_mul, eval_neg, eval_X, eval_sub, eval_one]
  nlinarith

/-- A degree-raising Darboux output weakly interlaces its input under the same
unit-interval sign hypotheses. -/
theorem darbouxOperator_interlaces_of_roots_mem_Icc
    {a b : ℝ} {p : ℝ[X]}
    (hp : p.Splits) (hdegp : 1 ≤ p.natDegree)
    (hp_pos : HasPosLeadingCoeff p)
    (houtput_pos : HasPosLeadingCoeff (-darbouxOperator a b p))
    (hdeg : (darbouxOperator a b p).natDegree = p.natDegree + 1)
    (hroots : ∀ r ∈ p.roots, 0 ≤ r ∧ r ≤ 1) :
    Interlaces p (darbouxOperator a b p) := by
  have hprec_neg : Prec p (-darbouxOperator a b p) :=
    prec_neg_darbouxOperator_of_roots_mem_Icc hp hdegp hp_pos houtput_pos
      (by rw [natDegree_neg, hdeg]; lia)
      (by rw [natDegree_neg, hdeg]) hroots
  have hprec : Prec p (darbouxOperator a b p) := by
    simpa using prec_C_mul_right hprec_neg (a := (-1 : ℝ)) (by norm_num)
  exact hprec.toInterlaces (by rw [hdeg])

/-- Moving both Darboux parameters by a nonnegative shift orients the two
outputs once the shifted output interlaces the input and has roots at most
one. -/
theorem darbouxOperator_shift_prec
    {a b s : ℝ} {p : ℝ[X]}
    (hs : 0 ≤ s)
    (hinter : Interlaces p (darbouxOperator (a + s) (b + s) p))
    (hp_pos : HasPosLeadingCoeff p)
    (hbase_pos : HasPosLeadingCoeff (darbouxOperator a b p))
    (hdeg : (darbouxOperator a b p).natDegree =
      (darbouxOperator (a + s) (b + s) p).natDegree)
    (hroots : ∀ r ∈ (darbouxOperator (a + s) (b + s) p).roots, r ≤ 1) :
    Prec (darbouxOperator (a + s) (b + s) p) (darbouxOperator a b p) := by
  let shifted := darbouxOperator (a + s) (b + s) p
  let base := darbouxOperator a b p
  have hrecur : base = C 1 * shifted + (C s * (X - C 1)) * p := by
    apply Polynomial.funext
    intro x
    simp [shifted, base, darbouxOperator]
    ring
  change Prec shifted base
  rw [hrecur]
  apply prec_of_interlaces_evalCoeff_nonpos
  · exact hinter
  · exact hp_pos
  · simpa [hrecur, base] using hbase_pos
  · rw [← hrecur, hdeg]
  · rw [← hrecur, hdeg]
    exact Nat.le_succ _
  · intro r hr
    have hshifted_ne := hinter.1.1
    have hr_mem : r ∈ shifted.roots := (mem_roots hshifted_ne).mpr hr
    have hr_upper : r ≤ 1 := by
      simpa [shifted] using hroots r hr_mem
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    nlinarith

end RealRooted
