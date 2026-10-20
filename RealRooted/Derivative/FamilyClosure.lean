import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort
import RealRooted.Derivative.Algebra
import RealRooted.Derivative.Interlacing
import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial

open Polynomial Set

noncomputable section

namespace RealRooted

/-- Splitting is preserved by differentiation in the zero-aware convention. -/
theorem eq_zero_or_splits_derivative {p : ℝ[X]}
    (hp : p = 0 ∨ p.Splits) :
    p.derivative = 0 ∨ p.derivative.Splits := by
  rcases hp with rfl | hp
  · simp
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hdeg0 : p.natDegree = 0
  · exact Or.inl (Polynomial.derivative_eq_zero.mpr hdeg0)
  by_cases hdeg1 : p.natDegree = 1
  · exact Or.inr (Splits.of_natDegree_eq_zero (by rw [p.natDegree_derivative, hdeg1]))
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact Or.inr (derivative_interlaces_of_natDegree_ne_zero hp (by lia)).2.1.2

/-- Iterating the zero-aware derivative closure preserves splitting. -/
theorem iterate_derivative_eq_zero_or_splits {p : ℝ[X]} (hsplit : p.Splits)
    (n : ℕ) :
    (derivative^[n]) p = 0 ∨ ((derivative^[n]) p).Splits := by
  induction n with
  | zero => exact Or.inr hsplit
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using eq_zero_or_splits_derivative ih

@[deprecated Polynomial.Splits.derivative (since := "2026-10-11")]
alias splits_derivative := Polynomial.Splits.derivative

/-- Strict real-rootedness is preserved by differentiation unless the
derivative vanishes. -/
theorem derivative_eq_zero_or_ne_zero_and_splits {p : ℝ[X]}
    (hp_splits : p.Splits) :
    p.derivative = 0 ∨ (p.derivative ≠ 0 ∧ p.derivative.Splits) := by
  by_cases hdeg0 : p.natDegree = 0
  · left
    exact Polynomial.derivative_eq_zero.mpr hdeg0
  by_cases hdeg1 : p.natDegree = 1
  · right
    have hder_ne : p.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hdeg0
    have hder_splits : p.derivative.Splits :=
      Splits.of_natDegree_eq_zero (by rw [p.natDegree_derivative, hdeg1])
    exact ⟨hder_ne, hder_splits⟩
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact Or.inr (derivative_interlaces_of_natDegree_ne_zero hp_splits (by lia)).2.1

/-- If all roots of a real-rooted polynomial are nonpositive, then all roots of
its derivative are nonpositive. -/
theorem roots_nonpos_derivative_of_roots_nonpos {p : ℝ[X]}
    (hp_splits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    ∀ r ∈ p.derivative.roots, r ≤ 0 := by
  by_cases hdeg0 : p.natDegree = 0
  · simp [Polynomial.derivative_eq_zero.mpr hdeg0]
  by_cases hdeg1 : p.natDegree = 1
  · have hderdeg : p.derivative.natDegree = 0 := by rw [p.natDegree_derivative, hdeg1]
    have hderC : p.derivative = C (p.derivative.coeff 0) :=
      eq_C_of_natDegree_eq_zero hderdeg
    rw [hderC]
    simp
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact (derivative_interlaces_of_natDegree_ne_zero hp_splits
      (by lia)).toStrictInterl.roots_le_of_right hroots

end RealRooted
