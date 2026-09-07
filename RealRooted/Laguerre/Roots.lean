/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.DerivativeRecurrence.GeneralizedLaguerreInterlacing
import RealRooted.Favard
import RealRooted.Laguerre.Favard
import RealRooted.SimpleRoots

import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Roots of generalized Laguerre polynomials

For `-1 ≤ α`, the sign-reversed generalized Laguerre family has nonnegative
coefficients, nonpositive real roots, and consecutive interlacing.  Favard's
recurrence gives the strict and simple-root theory when `-1 < α`; the boundary
case follows from its explicit factorization by `X`.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem generalizedLaguerre_second_derivative_recurrence_real
    (α : ℝ) : ∀ n,
      generalizedLaguerre (n + 1) α =
        (C (α + 1) + X) * generalizedLaguerre n α +
          (C (1 * (α + 1)) + C (2 * 1) * X) *
            (generalizedLaguerre n α).derivative +
            C (1 ^ 2) * X *
              (generalizedLaguerre n α).derivative.derivative := by
  intro n
  simpa using generalizedLaguerre_second_derivative_recurrence n α

private theorem generalizedLaguerre_bilinear_recurrence_real (α : ℝ) : ∀ n,
    generalizedLaguerre (n + 1) α =
      (C 1 * X + C (-0) * X ^ 2) *
          (generalizedLaguerre n α).derivative +
        (C (α + 1 + 1 * (n : ℝ)) + C (1 + 0 * (n : ℝ)) * X) *
          generalizedLaguerre n α :=
  generalized_laguerre_second_derivative_bilinear
    (P := fun n => generalizedLaguerre n α) (m := 1) (c := α + 1)
    (generalizedLaguerre_zero α)
    (generalizedLaguerre_second_derivative_recurrence_real α)

/-- Generalized Laguerre polynomials have nonnegative coefficients throughout
the closed classical parameter range. -/
theorem generalizedLaguerre_hasNonnegCoeffs (n : ℕ) {α : ℝ}
    (hα : -1 ≤ α) : HasNonnegCoeffs (generalizedLaguerre n α) := by
  exact hasNonnegCoeffs_of_quadratic_derivative_bilinear
    (fun k => generalizedLaguerre k α) 1 0 (α + 1) 1 1 0
    (generalizedLaguerre_zero α)
    (generalizedLaguerre_bilinear_recurrence_real α)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
    (by norm_num) (by norm_num) n

/-- Consecutive generalized Laguerre polynomials are in proper position. -/
theorem generalizedLaguerre_prec_succ (n : ℕ) {α : ℝ} (hα : -1 ≤ α) :
    Prec (generalizedLaguerre n α) (generalizedLaguerre (n + 1) α) :=
  prec_of_generalized_laguerre_second_derivative
    (P := fun k => generalizedLaguerre k α) (m := 1) (c := α + 1)
    (generalizedLaguerre_zero α)
    (generalizedLaguerre_second_derivative_recurrence_real α)
    (by norm_num) (by linarith) n

/-- Consecutive generalized Laguerre polynomials interlace. -/
theorem generalizedLaguerre_interlaces_succ (n : ℕ) {α : ℝ}
    (hα : -1 ≤ α) :
    Interlaces (generalizedLaguerre n α) (generalizedLaguerre (n + 1) α) :=
  interlaces_of_generalized_laguerre_second_derivative
    (P := fun k => generalizedLaguerre k α) (m := 1) (c := α + 1)
    (generalizedLaguerre_zero α)
    (generalizedLaguerre_second_derivative_recurrence_real α)
    (by norm_num) (by linarith) n

/-- Every generalized Laguerre polynomial splits over the reals in the closed
classical parameter range. -/
theorem generalizedLaguerre_splits (n : ℕ) {α : ℝ} (hα : -1 ≤ α) :
    (generalizedLaguerre n α).Splits :=
  (isRealRooted_of_generalized_laguerre_second_derivative_sequence
    (P := fun k => generalizedLaguerre k α) (m := 1) (c := α + 1)
    (generalizedLaguerre_zero α)
    (generalizedLaguerre_second_derivative_recurrence_real α)
    (by norm_num) (by linarith) n).2

/-- All roots are nonpositive in the closed classical parameter range. -/
theorem generalizedLaguerre_roots_nonpos (n : ℕ) {α : ℝ} (hα : -1 ≤ α) :
    ∀ r ∈ (generalizedLaguerre n α).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs
    (generalizedLaguerre_hasNonnegCoeffs n hα)

/-- All roots are strictly negative in the open classical parameter range. -/
theorem generalizedLaguerre_roots_neg (n : ℕ) {α : ℝ} (hα : -1 < α) :
    ∀ r ∈ (generalizedLaguerre n α).roots, r < 0 := by
  intro r hr
  have hr_le := generalizedLaguerre_roots_nonpos n hα.le r hr
  have hr_ne : r ≠ 0 := by
    intro hr_zero
    subst r
    have hroot := (Polynomial.mem_roots
      (monic_generalizedLaguerre n α).ne_zero).mp hr
    rw [Polynomial.IsRoot.def, generalizedLaguerre_eval_zero] at hroot
    have hpos := ascPochhammer_pos n (α + 1) (by linarith)
    linarith
  exact lt_of_le_of_ne hr_le hr_ne

/-- Consecutive polynomials have no common root in the open parameter range. -/
theorem generalizedLaguerre_noCommonRoot_succ (n : ℕ) {α : ℝ}
    (hα : -1 < α) (r : ℝ) (hr : (generalizedLaguerre n α).IsRoot r) :
    ¬(generalizedLaguerre (n + 1) α).IsRoot r :=
  noCommonRoot_succ_of_favard
    (generalizedLaguerre_satisfiesFavardRecurrence α)
    (fun k => generalizedLaguerreSubdiag_pos (k + 1) (by simp) hα)
    n r hr

/-- Roots are duplicate-free in the open classical parameter range. -/
theorem generalizedLaguerre_roots_nodup_of_neg_one_lt (n : ℕ) {α : ℝ}
    (hα : -1 < α) : (generalizedLaguerre n α).roots.Nodup :=
  roots_nodup_of_favard
    (generalizedLaguerre_satisfiesFavardRecurrence α)
    (fun k => generalizedLaguerreSubdiag_pos (k + 1) (by simp) hα) n

/-- The reversed finite prefix satisfies the project's weak Sturm-sequence
predicate on the full closed classical parameter range.  `IsSturmSeq` records
consecutive `Interlaces` and does not impose coprimality, so at `α = -1`
positive-index neighbors may share the root zero. -/
theorem generalizedLaguerre_isSturmSeq (n : ℕ) {α : ℝ} (hα : -1 ≤ α) :
    IsSturmSeq
      ((List.range (n + 1)).reverse.map
        (fun k => generalizedLaguerre k α)) := by
  induction n with
  | zero => simp [IsSturmSeq]
  | succ n ih =>
      have hinter := generalizedLaguerre_interlaces_succ n hα
      simpa [IsSturmSeq, List.range_succ] using And.intro hinter ih

/-- The reversed finite prefix is, in particular, a generalized Sturm
sequence. -/
theorem generalizedLaguerre_isGeneralizedSturmSeq (n : ℕ) {α : ℝ}
    (hα : -1 ≤ α) :
    IsGeneralizedSturmSeq
      ((List.range (n + 1)).reverse.map
        (fun k => generalizedLaguerre k α)) :=
  (generalizedLaguerre_isSturmSeq n hα).toGeneralizedSturmSeq

/-- Roots are duplicate-free throughout the closed classical parameter
range, including the factored boundary `α = -1`. -/
theorem generalizedLaguerre_roots_nodup (n : ℕ) {α : ℝ} (hα : -1 ≤ α) :
    (generalizedLaguerre n α).roots.Nodup := by
  by_cases hα_strict : -1 < α
  · exact generalizedLaguerre_roots_nodup_of_neg_one_lt n hα_strict
  · have hα_eq : α = -1 := by linarith
    subst α
    cases n with
    | zero => simp
    | succ n =>
        rw [generalizedLaguerre_succ_neg_one]
        rw [Polynomial.roots_mul
          (mul_ne_zero X_ne_zero (monic_generalizedLaguerre n 1).ne_zero),
          Polynomial.roots_X, Multiset.nodup_add]
        refine ⟨by simp,
          generalizedLaguerre_roots_nodup_of_neg_one_lt n (by norm_num), ?_⟩
        rw [Multiset.singleton_disjoint]
        intro hzero
        have := generalizedLaguerre_roots_neg n (by norm_num : -1 < (1 : ℝ))
          0 hzero
        norm_num at this

/-- Generalized Laguerre polynomials have simple roots throughout the closed
classical parameter range. -/
theorem generalizedLaguerre_hasSimpleRoots (n : ℕ) {α : ℝ} (hα : -1 ≤ α) :
    HasSimpleRoots (generalizedLaguerre n α) :=
  HasSimpleRoots.of_roots_nodup
    (monic_generalizedLaguerre n α).ne_zero
    (generalizedLaguerre_roots_nodup n hα)

end RealRooted
