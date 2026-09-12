/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol.Interlacing
import RealRooted.GammaPencil.SymbolStability

/-!
# The gamma operator preserves real-rootedness in its degree box

The stable finite symbol of `gammaOperator n` gives a real-rootedness
preserver on polynomials of degree at most `n / 2`.  The pair form below is
the induction interface for transporting both components of the gamma pencil.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The rank-`n` gamma operator preserves real-rootedness, allowing the zero
output, throughout its canonical degree box. -/
theorem gammaOperator_preservesRealRootedUpTo (n : ℕ) (hn : 2 ≤ n) :
    BorceaBranden.PreservesRealRootedUpTo (n / 2) (gammaOperator n) := by
  apply BorceaBranden.finiteSymbol_preservesRealRootedUpTo
  exact finiteAlgebraicSymbol_gammaOperator_stable n hn

/-- Direct split-or-zero form of the gamma-operator preserver. -/
theorem gammaOperator_splits_or_zero
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]}
    (hdeg : p.natDegree ≤ n / 2) (hp : p.Splits) :
    gammaOperator n p = 0 ∨ (gammaOperator n p).Splits :=
  gammaOperator_preservesRealRootedUpTo n hn hdeg hp

/-- The gamma operator transports an all-real-combination pair when both
inputs lie in its canonical degree box. -/
theorem gammaOperator_allComboRealRooted
    {n : ℕ} (hn : 2 ≤ n) {p q : ℝ[X]}
    (hpdeg : p.natDegree ≤ n / 2)
    (hqdeg : q.natDegree ≤ n / 2)
    (hall : AllComboRealRooted p q) :
    AllComboRealRooted (gammaOperator n p) (gammaOperator n q) := by
  apply BorceaBranden.linearMap_allComboRealRooted_of_finiteSymbol_stable
  · exact finiteAlgebraicSymbol_gammaOperator_stable n hn
  · exact hpdeg
  · exact hqdeg
  · exact hall

/-- Proper position is transported up to the two possible orientations and
the zero-output boundary.  Coefficient invariants resolve this ambiguity for
the recursive gamma components in the final pencil theorem. -/
theorem gammaOperator_prec0_or_revPrec0
    {n : ℕ} (hn : 2 ≤ n) {p q : ℝ[X]}
    (hpdeg : p.natDegree ≤ n / 2)
    (hqdeg : q.natDegree ≤ n / 2)
    (hpq : Prec p q) :
    Prec0 (gammaOperator n p) (gammaOperator n q) ∨
      Prec0 (gammaOperator n q) (gammaOperator n p) := by
  apply BorceaBranden.linearMap_prec0_or_revPrec0_of_finiteSymbol_stable
  · exact finiteAlgebraicSymbol_gammaOperator_stable n hn
  · exact hpdeg
  · exact hqdeg
  · exact hpq

end RealRooted
