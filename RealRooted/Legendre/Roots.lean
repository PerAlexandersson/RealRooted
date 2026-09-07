/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.Basic.AffineInterlacing
import RealRooted.Jacobi
import RealRooted.Legendre.Basic

/-!
# Roots of shifted Legendre polynomials

Mathlib's shifted Legendre normalization `Pₙ(1 - 2X)` has simple roots in
`(0, 1)`. Its reflection `Pₙ(1 + 2X)` has positive leading coefficient and
simple roots in `(-1, 0)`. Consecutive polynomials interlace in both
orientations.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Every real shifted Legendre polynomial is nonzero and splits over `ℝ`. -/
theorem shiftedLegendreReal_isRealRooted (n : ℕ) :
    shiftedLegendreReal n ≠ 0 ∧ (shiftedLegendreReal n).Splits := by
  rw [shiftedLegendreReal_eq_shiftedJacobi]
  exact ⟨shiftedJacobi_ne_zero n (by norm_num) (by norm_num),
    shiftedJacobi_splits n (by norm_num) (by norm_num)⟩

/-- Every real shifted Legendre polynomial is nonzero. -/
theorem shiftedLegendreReal_ne_zero (n : ℕ) :
    shiftedLegendreReal n ≠ 0 :=
  (shiftedLegendreReal_isRealRooted n).1

/-- Every real shifted Legendre polynomial splits over `ℝ`. -/
theorem shiftedLegendreReal_splits (n : ℕ) :
    (shiftedLegendreReal n).Splits :=
  (shiftedLegendreReal_isRealRooted n).2

/-- Consecutive real shifted Legendre polynomials satisfy `Prec`. -/
theorem shiftedLegendreReal_prec_succ (n : ℕ) :
    Prec (shiftedLegendreReal n) (shiftedLegendreReal (n + 1)) := by
  simpa only [shiftedLegendreReal_eq_shiftedJacobi] using
    shiftedJacobi_prec_succ n (by norm_num) (by norm_num)

/-- Consecutive real shifted Legendre polynomials interlace. -/
theorem shiftedLegendreReal_interlaces_succ (n : ℕ) :
    Interlaces (shiftedLegendreReal n) (shiftedLegendreReal (n + 1)) := by
  simpa only [shiftedLegendreReal_eq_shiftedJacobi] using
    shiftedJacobi_interlaces_succ n (by norm_num) (by norm_num)

/-- Every root of a real shifted Legendre polynomial lies in `(0, 1)`. -/
theorem shiftedLegendreReal_isRoot_mem_Ioo (n : ℕ) {r : ℝ}
    (hr : (shiftedLegendreReal n).IsRoot r) :
    r ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [shiftedLegendreReal_eq_shiftedJacobi] at hr
  exact shiftedJacobi_isRoot_mem_Ioo n (by norm_num) (by norm_num) hr

/-- The roots of every real shifted Legendre polynomial are duplicate-free. -/
theorem shiftedLegendreReal_roots_nodup (n : ℕ) :
    (shiftedLegendreReal n).roots.Nodup := by
  rw [shiftedLegendreReal_eq_shiftedJacobi]
  exact shiftedJacobi_roots_nodup n (by norm_num) (by norm_num)

/-- Every real shifted Legendre polynomial has only simple real roots. -/
theorem shiftedLegendreReal_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots (shiftedLegendreReal n) := by
  rw [shiftedLegendreReal_eq_shiftedJacobi]
  exact shiftedJacobi_hasSimpleRoots n (by norm_num) (by norm_num)

/-- Reflecting a real shifted Legendre polynomial through the origin preserves
its degree. -/
@[simp] theorem shiftedLegendreReal_comp_neg_X_natDegree (n : ℕ) :
    ((shiftedLegendreReal n).comp (-X)).natDegree = n := by
  simp [Polynomial.natDegree_comp, shiftedLegendreReal_natDegree]

/-- The reflected real shifted Legendre polynomial has central binomial
leading coefficient. -/
@[simp] theorem shiftedLegendreReal_comp_neg_X_leadingCoeff (n : ℕ) :
    ((shiftedLegendreReal n).comp (-X)).leadingCoeff =
      (Nat.choose (2 * n) n : ℝ) := by
  rw [Polynomial.comp_neg_X_leadingCoeff_eq,
    shiftedLegendreReal_natDegree, shiftedLegendreReal_leadingCoeff,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The reflected real shifted Legendre polynomial has positive leading
coefficient. -/
theorem shiftedLegendreReal_comp_neg_X_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff ((shiftedLegendreReal n).comp (-X)) := by
  rw [HasPosLeadingCoeff, shiftedLegendreReal_comp_neg_X_leadingCoeff]
  exact_mod_cast Nat.choose_pos (by lia : n ≤ 2 * n)

/-- The reflected real shifted Legendre polynomial is nonzero. -/
theorem shiftedLegendreReal_comp_neg_X_ne_zero (n : ℕ) :
    (shiftedLegendreReal n).comp (-X) ≠ 0 := by
  exact Polynomial.comp_neg_X_eq_zero_iff.not.mpr
    (shiftedLegendreReal_ne_zero n)

/-- The reflected real shifted Legendre polynomial splits over `ℝ`. -/
theorem shiftedLegendreReal_comp_neg_X_splits (n : ℕ) :
    ((shiftedLegendreReal n).comp (-X)).Splits :=
  (shiftedLegendreReal_splits n).comp_neg_X

/-- Every root of the reflected real shifted Legendre polynomial lies in
`(-1, 0)`. -/
theorem shiftedLegendreReal_comp_neg_X_isRoot_mem_Ioo (n : ℕ) {r : ℝ}
    (hr : ((shiftedLegendreReal n).comp (-X)).IsRoot r) :
    r ∈ Set.Ioo (-1 : ℝ) 0 := by
  have hraw : (shiftedLegendreReal n).IsRoot (-r) := by
    simpa [Polynomial.IsRoot.def] using hr
  rcases shiftedLegendreReal_isRoot_mem_Ioo n hraw with
    ⟨hzero, hone⟩
  exact ⟨by linarith, by linarith⟩

/-- The reflected real shifted Legendre polynomial has duplicate-free roots. -/
theorem shiftedLegendreReal_comp_neg_X_roots_nodup (n : ℕ) :
    ((shiftedLegendreReal n).comp (-X)).roots.Nodup := by
  rw [Polynomial.roots_comp_neg_X]
  exact (shiftedLegendreReal_roots_nodup n).map
    (fun a b h => by linarith [h])

/-- The reflected real shifted Legendre polynomial has only simple real
roots. -/
theorem shiftedLegendreReal_comp_neg_X_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots ((shiftedLegendreReal n).comp (-X)) :=
  HasSimpleRoots.of_roots_nodup
    (shiftedLegendreReal_comp_neg_X_ne_zero n)
    (shiftedLegendreReal_comp_neg_X_roots_nodup n)

/-- Consecutive reflected real shifted Legendre polynomials interlace. -/
theorem shiftedLegendreReal_comp_neg_X_interlaces_succ (n : ℕ) :
    Interlaces ((shiftedLegendreReal n).comp (-X))
      ((shiftedLegendreReal (n + 1)).comp (-X)) :=
  interlaces_comp_neg_X (shiftedLegendreReal_interlaces_succ n)

/-- Consecutive reflected real shifted Legendre polynomials satisfy `Prec`. -/
theorem shiftedLegendreReal_comp_neg_X_prec_succ (n : ℕ) :
    Prec ((shiftedLegendreReal n).comp (-X))
      ((shiftedLegendreReal (n + 1)).comp (-X)) :=
  (shiftedLegendreReal_comp_neg_X_interlaces_succ n).toPrec

example : Prec (1 + 2 * X) (1 + 6 * X + 6 * X ^ 2) := by
  simpa using shiftedLegendreReal_comp_neg_X_prec_succ 1

end RealRooted
