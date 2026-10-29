/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential

/-!
# Monic Laguerre polynomials and their finite combinations

The classical monic normalization `(-1)^n n! L_n^(α)(X)` of the generalized Laguerre polynomials,
and the bandwidth-one combinations `L_n + γ L_{n-1}` and auxiliary polynomial `X - γ` of
Durán, *Zeros of linear combinations of Laguerre polynomials* (arXiv:2507.22425), Theorem 1.3.
The zero-location theorem is `RealRooted.laguerreCombinationOne_splits_simple_roots_pos`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The classical monic generalized Laguerre polynomial
`(-1)^n n! L_n^(α)(X)`. -/
noncomputable def monicLaguerre (n : ℕ) (α : R) : R[X] :=
  C ((-1 : R) ^ n) * (generalizedLaguerre n α).comp (-X)

/-- The zeroth classical monic Laguerre polynomial is one. -/
@[simp] theorem monicLaguerre_zero (α : R) :
    monicLaguerre 0 α = 1 := by
  simp [monicLaguerre]

/-- The first classical monic Laguerre polynomial is `X - (α + 1)`. -/
@[simp] theorem monicLaguerre_one (α : R) :
    monicLaguerre 1 α = X - C (α + 1) := by
  simp [monicLaguerre]
  ring

/-- The degree-one auxiliary polynomial in Durán's criterion. -/
noncomputable def laguerreAuxiliaryOne (γ : R) : R[X] :=
  X - C γ

/-- The degree-one Durán auxiliary polynomial has the unique root `γ`. -/
@[simp] theorem laguerreAuxiliaryOne_isRoot_iff [IsDomain R] (γ x : R) :
    (laguerreAuxiliaryOne γ).IsRoot x ↔ x = γ := by
  simp only [laguerreAuxiliaryOne, IsRoot.def, eval_sub, eval_X, eval_C]
  exact sub_eq_zero

/-- A combination of two consecutive classical monic Laguerre polynomials,
the `K = 1` family in Durán's Theorem 1.3. -/
noncomputable def laguerreCombinationOne (n : ℕ) (α γ : R) : R[X] :=
  monicLaguerre n α + C γ * monicLaguerre (n - 1) α

end Polynomial

end
