/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Favard.Orthogonality
public import RealRooted.Hermite.Favard

import Mathlib.Tactic.Positivity

/-!
# Algebraic orthogonality for probabilists' Hermite polynomials

The normalized Favard functional gives the real Hermite family an algebraic
orthogonality pairing with squared norm `n!`.  The Gaussian integral
realization belongs in `RealRooted.Hermite.Orthogonality.Integral`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- For the Hermite subdiagonal `β n = n`, the Favard squared norm is `n!`. -/
@[simp] theorem hermiteReal_favardNormSq_eq_factorial (n : ℕ) :
    favardNormSq (fun k : ℕ ↦ (k : ℝ)) n = (n.factorial : ℝ) :=
  favardNormSq_natCast n

/-- The normalized Hermite Favard functional extracts the constant Hermite
coordinate. -/
@[simp] theorem hermiteReal_favardFunctional_apply (n : ℕ) :
    hermiteReal_satisfiesFavardRecurrence.functional (hermiteReal n) =
      if n = 0 then 1 else 0 :=
  hermiteReal_satisfiesFavardRecurrence.functional_apply_basis n

/-- The generic Favard pairing makes the real Hermite family orthogonal. -/
theorem hermiteReal_favardPairing_iIsOrtho :
    hermiteReal_satisfiesFavardRecurrence.pairing.iIsOrtho hermiteReal :=
  hermiteReal_satisfiesFavardRecurrence.pairing_iIsOrtho

/-- The normalized Favard pairing of two real Hermite polynomials is diagonal,
with diagonal entry `n!`. -/
@[simp] theorem hermiteReal_favardPairing_apply (i j : ℕ) :
    hermiteReal_satisfiesFavardRecurrence.pairing
        (hermiteReal i) (hermiteReal j) =
      if i = j then (i.factorial : ℝ) else 0 := by
  rw [hermiteReal_satisfiesFavardRecurrence.pairing_apply_basis]
  split_ifs with hij
  · exact hermiteReal_favardNormSq_eq_factorial i
  · rfl

/-- The normalized Hermite Favard pairing is positive definite. -/
theorem hermiteReal_favardPairing_posDef :
    hermiteReal_satisfiesFavardRecurrence.pairing.toQuadraticMap.PosDef := by
  exact hermiteReal_satisfiesFavardRecurrence.pairing_posDef
    hermiteReal_subdiag_pos

/-- The normalized Hermite Favard pairing is nondegenerate. -/
theorem hermiteReal_favardPairing_nondegenerate :
    hermiteReal_satisfiesFavardRecurrence.pairing.Nondegenerate := by
  apply hermiteReal_satisfiesFavardRecurrence.pairing_nondegenerate
  intro n
  positivity

/-- The normalized Hermite Favard functional is strictly positive on every
nonzero polynomial square. -/
theorem hermiteReal_favardFunctional_mul_self_pos {p : ℝ[X]} (hp : p ≠ 0) :
    0 < hermiteReal_satisfiesFavardRecurrence.functional (p * p) := by
  apply hermiteReal_satisfiesFavardRecurrence.functional_mul_self_pos
  · exact hermiteReal_subdiag_pos
  · exact hp

end RealRooted
