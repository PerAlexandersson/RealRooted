/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import RealRooted.Mathlib.Algebra.Polynomial.Moment.FiniteAtoms
public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact norm boundary for finitely supported moments

Distinct nodes with positive weights give positive definite moment matrices
up to the support size. At that size the monic orthogonal polynomial is the
nodal polynomial, so its norm and all its pairings vanish. These are the
finite-rank boundaries needed for terminating Stieltjes fractions.
-/

public section

namespace Polynomial

variable {ι : Type*}

/-- Positive weights on distinct nodes make the finite moment matrix positive
definite at every size no larger than the number of nodes. -/
theorem momentHankelMatrix_finset_sum_posDef
    (s : Finset ι) (x w : ι → ℝ) (hx : Set.InjOn x s)
    (hw : ∀ i ∈ s, 0 < w i) (n : ℕ) (hn : n ≤ s.card) :
    (momentHankelMatrix (fun k => ∑ i ∈ s, w i * x i ^ k) n).PosDef := by
  classical
  apply momentHankelMatrix_posDef_of_pos
  intro p hp hdeg
  have hex : ∃ i ∈ s, p.eval (x i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply eq_zero_of_degree_lt_of_eval_index_eq_zero s hx
      (lt_of_lt_of_le hdeg (by exact_mod_cast hn)) h
  obtain ⟨i, hi, hpi⟩ := hex
  rw [momentPairing_finset_sum]
  apply Finset.sum_pos'
  · intro j hj
    simpa only [pow_two, mul_assoc] using
      mul_nonneg (hw j hj).le (sq_nonneg (p.eval (x j)))
  · refine ⟨i, hi, ?_⟩
    simpa only [pow_two, mul_assoc] using mul_pos (hw i hi) (sq_pos_of_ne_zero hpi)

/-- At the full support size, the monic moment polynomial is exactly the nodal polynomial. -/
theorem monicMomentPolynomial_finset_sum_card
    (s : Finset ι) (x w : ι → ℝ) (hx : Set.InjOn x s)
    (hw : ∀ i ∈ s, 0 < w i) :
    monicMomentPolynomial (fun k => ∑ i ∈ s, w i * x i ^ k) s.card =
      Lagrange.nodal s x := by
  classical
  have hpd := momentHankelMatrix_finset_sum_posDef s x w hx hw s.card le_rfl
  symm
  apply eq_monicMomentPolynomial _ (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
  · exact ⟨Lagrange.natDegree_nodal, Lagrange.nodal_monic⟩
  · intro i
    rw [momentPairing_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Lagrange.eval_nodal_at_node hj, mul_zero]

/-- The full-support monic moment polynomial has zero pairing against every polynomial. -/
theorem momentPairing_finset_sum_card_eq_zero
    (s : Finset ι) (x w : ι → ℝ) (hx : Set.InjOn x s)
    (hw : ∀ i ∈ s, 0 < w i) (p : ℝ[X]) :
    momentPairing (fun k => ∑ i ∈ s, w i * x i ^ k) p
      (monicMomentPolynomial (fun k => ∑ i ∈ s, w i * x i ^ k) s.card) = 0 := by
  classical
  rw [monicMomentPolynomial_finset_sum_card s x w hx hw, momentPairing_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Lagrange.eval_nodal_at_node hi, mul_zero]

/-- The first vanishing norm occurs at the number of distinct positively
weighted nodes, including the empty-support boundary. -/
theorem momentNormSq_finset_sum_card_eq_zero
    (s : Finset ι) (x w : ι → ℝ) (hx : Set.InjOn x s)
    (hw : ∀ i ∈ s, 0 < w i) :
    momentNormSq (fun k => ∑ i ∈ s, w i * x i ^ k) s.card = 0 :=
  momentPairing_finset_sum_card_eq_zero s x w hx hw _

/-- Every norm strictly below the support size is positive. -/
theorem momentNormSq_finset_sum_pos
    (s : Finset ι) (x w : ι → ℝ) (hx : Set.InjOn x s)
    (hw : ∀ i ∈ s, 0 < w i) {n : ℕ} (hn : n < s.card) :
    0 < momentNormSq (fun k => ∑ i ∈ s, w i * x i ^ k) n :=
  momentNormSq_pos _ n
    (momentHankelMatrix_finset_sum_posDef s x w hx hw (n + 1) (by lia))

end Polynomial
