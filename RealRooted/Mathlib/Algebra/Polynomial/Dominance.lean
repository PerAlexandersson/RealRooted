import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Root exclusion from coefficient dominance

Upstream-shaped coefficient estimates which rule out a negative real root when
one coefficient term dominates all the others at a positive evaluation point.
-/

open Finset

namespace Polynomial

/-- If one term strictly exceeds the sum of the absolute values of the others,
the polynomial does not vanish at the corresponding negative point. -/
theorem eval_neg_ne_zero_of_abs_coeff_term_dominates {p : ℝ[X]} {s : ℝ} (hs : 0 < s)
    {j N : ℕ} (hdegree : p.natDegree < N) (hindex : j < N)
    (hdominates :
      ∑ k ∈ (range N).erase j, |p.coeff k| * s ^ k < |p.coeff j| * s ^ j) :
    p.eval (-s) ≠ 0 := by
  have hsum : p.eval (-s) = ∑ k ∈ range N, p.coeff k * (-s) ^ k := by
    rw [Polynomial.eval_eq_sum_range' hdegree]
  intro hzero
  rw [hzero] at hsum
  have hindex_mem : j ∈ range N := mem_range.mpr hindex
  have hsplit : p.coeff j * (-s) ^ j
      + ∑ k ∈ (range N).erase j, p.coeff k * (-s) ^ k = 0 := by
    rw [Finset.add_sum_erase (range N) (fun k => p.coeff k * (-s) ^ k) hindex_mem]
    exact hsum.symm
  have habs : |p.coeff j * (-s) ^ j|
      ≤ ∑ k ∈ (range N).erase j, |p.coeff k * (-s) ^ k| := by
    have hterm : p.coeff j * (-s) ^ j
        = -(∑ k ∈ (range N).erase j, p.coeff k * (-s) ^ k) := by
      linarith [hsplit]
    rw [hterm, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hleft : |p.coeff j * (-s) ^ j| = |p.coeff j| * s ^ j := by
    rw [abs_mul, abs_pow, abs_neg, abs_of_pos hs]
  have hright : ∀ k, |p.coeff k * (-s) ^ k| = |p.coeff k| * s ^ k := by
    intro k
    rw [abs_mul, abs_pow, abs_neg, abs_of_pos hs]
  rw [hleft] at habs
  rw [Finset.sum_congr rfl (fun k _ => hright k)] at habs
  linarith

/-- If a polynomial is nonzero at every negative point in an interval, no root
lies in the corresponding negative interval. -/
theorem no_root_in_neg_interval_of_eval_ne_zero {p : ℝ[X]} {s₁ s₂ : ℝ}
    (h : ∀ s, s₁ ≤ s → s ≤ s₂ → p.eval (-s) ≠ 0) :
    ∀ ξ ∈ p.roots, ¬ (-s₂ ≤ ξ ∧ ξ ≤ -s₁) := by
  intro ξ hξ ⟨hleft, hright⟩
  have hroot : p.eval ξ = 0 := Polynomial.isRoot_of_mem_roots hξ
  have hrewrite : ξ = -(-ξ) := by ring
  refine h (-ξ) (by linarith) (by linarith) ?_
  rw [← hrewrite]
  exact hroot

end Polynomial
