/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.Numerator
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.CombinatorialExamples.CaoFu.Disk
import RealRooted.IntervalDifferential.CenteredTransfer
import Mathlib.Tactic

/-!
# Distinct negative roots of the crown polynomial

We prove Cao--Fu, arXiv:2610.40496v1, Theorem 1.1, for the existing crown
polynomial. Its parameter `n` denotes paper rank minus two. The trace comparison
and numerator identification put the polynomial in the centered basis, and
the centered disk theorem transfers its roots to distinct negative real roots.
-/

public section
noncomputable section
open Polynomial Finset
open RealRooted.IntervalDifferential
namespace RealRooted.CaoFu

private theorem exists_centered_quotient (n : ℕ) :
    ∃ Q : Polynomial ℝ, Q.natDegree = 2 * (n + 1) ∧ Q.comp (-X) = Q ∧
      (X ^ 2 - 1) * Q =
        C ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) *
          centeredTracePolynomial (n + 1) := by
  let E := centeredTracePolynomial (n + 1)
  have hroot1 : X - C (1 : ℝ) ∣ E := by
    rw [dvd_iff_isRoot]
    exact centeredTracePolynomial_eval_one _
  obtain ⟨U, hU⟩ := hroot1
  have hUneg : U.eval (-1) = 0 := by
    have h := congrArg (Polynomial.eval (-1)) hU
    simp only [E, centeredTracePolynomial_eval_neg_one, eval_mul, eval_sub,
      eval_X, eval_C] at h
    nlinarith
  obtain ⟨V, hV⟩ := (dvd_iff_isRoot.mpr hUneg : X - C (-1 : ℝ) ∣ U)
  have hE : E = (X ^ 2 - 1) * V := by
    rw [hU, hV]
    norm_num
    ring
  have hEdeg : E.natDegree = 2 * (n + 2) := by
    exact centeredTracePolynomial_natDegree (n + 1)
  have hE0 : E ≠ 0 := by intro h; rw [h, natDegree_zero] at hEdeg; lia
  have hV0 : V ≠ 0 := by intro h; rw [h, mul_zero] at hE; exact hE0 hE
  have hF0 : (X ^ 2 - 1 : Polynomial ℝ) ≠ 0 := by
    exact (monic_X_pow_sub_C (1 : ℝ) (by decide : (2 : ℕ) ≠ 0)).ne_zero
  have hVdeg : V.natDegree = 2 * (n + 1) := by
    have h := congrArg Polynomial.natDegree hE
    rw [hEdeg, natDegree_mul hF0 hV0,
      show (1 : Polynomial ℝ) = C 1 by rfl, natDegree_X_pow_sub_C] at h
    lia
  let a : ℝ := (4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  let Q := C a * V
  have hfactor : (X ^ 2 - 1) * Q = C a * E := by rw [hE]; dsimp [Q]; ring
  refine ⟨Q, ?_, ?_, hfactor⟩
  · change (C a * V).natDegree = _
    rw [natDegree_C_mul ha, hVdeg]
  · apply mul_left_cancel₀ hF0
    have h := congrArg (fun P : Polynomial ℝ => P.comp (-X)) hfactor
    simp only [mul_comp, sub_comp, pow_comp, X_comp, one_comp, neg_sq, C_comp,
      show E.comp (-X) = E from centeredTracePolynomial_comp_neg_X _] at h
    exact h.trans hfactor.symm

/-- The rank-`n+2` crown polynomial has its full degree and distinct negative real roots. -/
theorem crownPolynomial_roots {n : ℕ} (hn : n ≠ 0) :
    (crownPolynomial n).natDegree = 2 * (n + 1) ∧
      (crownPolynomial n).Splits ∧ (crownPolynomial n).roots.Nodup ∧
      ∀ x ∈ (crownPolynomial n).roots, x < 0 := by
  obtain ⟨Q, hdegree, hpar, hfactor⟩ := exists_centered_quotient n
  have hcoeff := crownPolynomial_centered_coeff_sum_eq n Q hdegree.le hpar hfactor
  have hdisk (c : ℂ) (hc : (Q.map (algebraMap ℝ ℂ)).eval c = 0) :
      Complex.normSq c ≤ 13 / 3 := by
    have h := congrArg (fun P : Polynomial ℝ => (P.map (algebraMap ℝ ℂ)).eval c) hfactor
    simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, hc, mul_zero] at h
    have ha : (algebraMap ℝ ℂ)
        ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) ≠ 0 :=
      (_root_.map_ne_zero (algebraMap ℝ ℂ)).mpr (by positivity)
    have he : ((centeredTracePolynomial (n + 1)).map (algebraMap ℝ ℂ)).eval c = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left ha
    exact (centeredTracePolynomial_normSq_lt (by lia : 2 ≤ n + 1) he).le
  exact transfer_of_centered_disk (2 * (n + 1)) (by lia) (crownPolynomial n) Q
    (crownPolynomial_monic_natDegree n).1.ne_zero
    (crownPolynomial_monic_natDegree n).2.le hcoeff.symm hdegree (Or.inl hpar) hdisk

/-- The crown polynomial has exactly its degree many distinct real roots. -/
theorem crownPolynomial_roots_card {n : ℕ} (hn : n ≠ 0) :
    (crownPolynomial n).roots.card = 2 * (n + 1) := by
  obtain ⟨hdegree, hsplit, _, _⟩ := crownPolynomial_roots hn
  rw [← hsplit.natDegree_eq_card_roots, hdegree]

/-- Cao--Fu Theorem 1.1 in paper-rank indices: the rank-`r` crown numerator
has degree `2r-2` and all its roots are distinct, real and negative. -/
theorem crownPolynomial_rank_roots (r : ℕ) (hr : 3 ≤ r) :
    (crownPolynomial (r - 2)).natDegree = 2 * r - 2 ∧
      (crownPolynomial (r - 2)).Splits ∧ (crownPolynomial (r - 2)).roots.Nodup ∧
      ∀ x ∈ (crownPolynomial (r - 2)).roots, x < 0 := by
  have h := crownPolynomial_roots (n := r - 2) (by lia)
  simpa only [show 2 * (r - 2 + 1) = 2 * r - 2 by lia] using h

end RealRooted.CaoFu
