/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.Favard
import RealRooted.Hermite.Favard
import RealRooted.SimpleRoots

import Mathlib.Tactic.Positivity

/-!
# Roots of probabilists' Hermite polynomials

The proper-position orientation is

`Prec (hermiteReal n) (hermiteReal (n + 1))`.

Thus the lower-degree polynomial is on the left, and its roots lie
between consecutive roots of the polynomial on the right.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Real probabilists' Hermite polynomials have positive leading
coefficient. -/
theorem hermiteReal_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (hermiteReal n) :=
  hasPosLeadingCoeff_of_monic (hermiteReal_monic n)

/-- Consecutive real probabilists' Hermite polynomials are in proper
position, with the lower-degree polynomial first. -/
theorem hermiteReal_prec_succ (n : ℕ) :
    Prec (hermiteReal n) (hermiteReal (n + 1)) :=
  favardInterlacing hermiteReal_satisfiesFavardRecurrence
    hermiteReal_subdiag_pos n

/-- Consecutive real probabilists' Hermite polynomials interlace. -/
theorem hermiteReal_interlaces_succ (n : ℕ) :
    Interlaces (hermiteReal n) (hermiteReal (n + 1)) :=
  (hermiteReal_prec_succ n).toInterlaces (by simp)

/-- Every real probabilists' Hermite polynomial is nonzero and splits over
`ℝ`. -/
theorem hermiteReal_isRealRooted (n : ℕ) :
    hermiteReal n ≠ 0 ∧ (hermiteReal n).Splits :=
  isRealRooted_of_favard hermiteReal_satisfiesFavardRecurrence
    hermiteReal_subdiag_pos n

/-- Every real probabilists' Hermite polynomial is nonzero. -/
theorem hermiteReal_ne_zero (n : ℕ) : hermiteReal n ≠ 0 :=
  (hermiteReal_isRealRooted n).1

/-- Every real probabilists' Hermite polynomial splits over `ℝ`. -/
theorem hermiteReal_splits (n : ℕ) : (hermiteReal n).Splits :=
  (hermiteReal_isRealRooted n).2

/-- Consecutive real probabilists' Hermite polynomials have no common root. -/
theorem hermiteReal_noCommonRoot_succ (n : ℕ) (r : ℝ)
    (hr : (hermiteReal n).IsRoot r) :
    ¬ (hermiteReal (n + 1)).IsRoot r :=
  noCommonRoot_succ_of_favard hermiteReal_satisfiesFavardRecurrence
    hermiteReal_subdiag_pos n r hr

/-- Every root of a real probabilists' Hermite polynomial has multiplicity
one. -/
theorem hermiteReal_rootMultiplicity_eq_one (n : ℕ) {r : ℝ}
    (hr : (hermiteReal n).IsRoot r) :
    (hermiteReal n).rootMultiplicity r = 1 :=
  rootMultiplicity_eq_one_of_favard hermiteReal_satisfiesFavardRecurrence
    hermiteReal_subdiag_pos n hr

/-- The root multiset of every real probabilists' Hermite polynomial has no
duplicates. -/
theorem hermiteReal_roots_nodup (n : ℕ) :
    (hermiteReal n).roots.Nodup :=
  roots_nodup_of_favard hermiteReal_satisfiesFavardRecurrence
    hermiteReal_subdiag_pos n

/-- Every real probabilists' Hermite polynomial has simple roots. -/
theorem hermiteReal_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots (hermiteReal n) :=
  fun _ hr ↦ hermiteReal_rootMultiplicity_eq_one n hr

/-- Reversed finite prefixes of the real Hermite family are Sturm
sequences. -/
theorem hermiteReal_isSturmSeq (n : ℕ) :
    IsSturmSeq ((List.range (n + 1)).reverse.map hermiteReal) :=
  isSturmSeq_reverse_range_map_of_favard
    hermiteReal_satisfiesFavardRecurrence hermiteReal_subdiag_pos n

/-- Reversed finite prefixes of the real Hermite family are generalized
Sturm sequences. -/
theorem hermiteReal_isGeneralizedSturmSeq (n : ℕ) :
    IsGeneralizedSturmSeq
      ((List.range (n + 1)).reverse.map hermiteReal) :=
  isGeneralizedSturmSeq_reverse_range_map_of_favard
    hermiteReal_satisfiesFavardRecurrence hermiteReal_subdiag_pos n

example : Prec (X : ℝ[X]) (X ^ 2 - 1) := by
  simpa using hermiteReal_prec_succ 1

end RealRooted
