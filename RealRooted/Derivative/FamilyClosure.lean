module

public import RealRooted.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Multiset.Sort
public import RealRooted.Derivative.Algebra
public import RealRooted.Derivative.Interlacing
public import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial

public noncomputable section

open Polynomial Set

namespace RealRooted

/-- Splitting is preserved by differentiation in the zero-aware convention. -/
@[deprecated Polynomial.Splits.derivative +typeChanged (since := "2026-10-21")]
theorem eq_zero_or_splits_derivative {p : ℝ[X]}
    (hp : p = 0 ∨ p.Splits) :
    p.derivative = 0 ∨ p.derivative.Splits := by
  rcases hp with rfl | hp
  · simp
  · exact Or.inr hp.derivative

/-- Iterating the zero-aware derivative closure preserves splitting. -/
@[deprecated Polynomial.Splits.iterate_derivative +typeChanged (since := "2026-10-21")]
theorem iterate_derivative_eq_zero_or_splits {p : ℝ[X]} (hsplit : p.Splits)
    (n : ℕ) :
    (derivative^[n]) p = 0 ∨ ((derivative^[n]) p).Splits :=
  Or.inr (hsplit.iterate_derivative n)

@[deprecated Polynomial.Splits.derivative (since := "2026-10-11")]
alias splits_derivative := Polynomial.Splits.derivative

/-- Strict real-rootedness is preserved by differentiation unless the
derivative vanishes. -/
theorem derivative_eq_zero_or_ne_zero_and_splits {p : ℝ[X]}
    (hp_splits : p.Splits) :
    p.derivative = 0 ∨ (p.derivative ≠ 0 ∧ p.derivative.Splits) :=
  (eq_or_ne p.derivative 0).imp_right fun h => ⟨h, hp_splits.derivative⟩

/-- If all roots of a real-rooted polynomial are nonpositive, then all roots of
its derivative are nonpositive. -/
theorem roots_nonpos_derivative_of_roots_nonpos {p : ℝ[X]}
    (hp_splits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    ∀ r ∈ p.derivative.roots, r ≤ 0 := by
  intro r hr
  by_cases hdeg0 : p.natDegree = 0
  · simp [Polynomial.derivative_eq_zero.mpr hdeg0] at hr
  · exact (derivative_interlaces_of_natDegree_ne_zero hp_splits hdeg0).toStrictInterl
      |>.roots_le_of_right hroots r hr

end RealRooted
