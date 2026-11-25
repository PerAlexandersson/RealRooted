module

public import RealRooted.ExponentialRows.SubstitutionRows
import RealRooted.ExponentialRows.Substitution
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import Mathlib.Tactic

/-!
# Composition of exponential substitution operators

Composing the outer formal series composes their kernel operators in the same
order. This is an exact identity, without positivity or splitting assumptions.
It permits already proved substitution preservers to be iterated.

Source: unpublished manuscript, *Degree-raising substitutions for exponential rows*,
Section 1, RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- With zero unmarked series, the insertion rows are the kernel rows. -/
theorem insertionRow_affine_zero_eq_kernelRow {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    insertionRow (affineBlockWeights 0 B) n = exponentialKernelRow B n := by
  rw [insertionRow_affineBlockWeights_eq_exponential (map_zero _) hB]
  simp only [map_zero, zero_add, exponentialKernelRow, exponentialKernel]

/-- The exponential substitution operator acts on every kernel row by
substituting its marked series. -/
theorem exponentialSubstitution_kernelRow {B P : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (hP : PowerSeries.constantCoeff P = 0)
    (n : ℕ) :
    exponentialSubstitution P (exponentialKernelRow B n) =
      exponentialKernelRow (P.subst B) n := by
  have hPB : PowerSeries.constantCoeff (P.subst B) = 0 := by
    rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hB]
    exact hP
  rw [← insertionRow_affine_zero_eq_kernelRow hB,
    exponentialSubstitution_insertionRow (map_zero _) hB hP,
    insertionRow_affine_zero_eq_kernelRow hPB]

/-- Formal series composition is carried to composition of the exponential
substitution operators, on every input polynomial. -/
theorem exponentialSubstitution_subst {B P : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (hP : PowerSeries.constantCoeff P = 0)
    (p : ℝ[X]) :
    exponentialSubstitution (P.subst B) p =
      exponentialSubstitution P (exponentialSubstitution B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [exponentialSubstitution, basisTransformₗ_apply, basisTransform_monomial]
    change C c * exponentialKernelRow (P.subst B) n =
      exponentialSubstitution P (C c * exponentialKernelRow B n)
    rw [Polynomial.linearMap_C_mul, exponentialSubstitution_kernelRow hB hP]


/-- Substitution fixes the constant coefficient of every exponential row. -/
theorem insertionRow_coeff_zero_subst {A B P : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : PowerSeries.constantCoeff P = 0) (n : ℕ) :
    (insertionRow (affineBlockWeights A (P.subst B)) n).coeff 0 =
      (insertionRow (affineBlockWeights A B) n).coeff 0 := by
  rw [← exponentialSubstitution_insertionRow hA hB hP, coeff_zero_exponentialSubstitution hP]

/-- Every row of `exp(z + t B(z))` has constant coefficient one, even for
signed marked series. In particular, all the rows in the original problem
are nonzero independently of a splitting hypothesis. -/
theorem insertionRow_affine_X_coeff_zero {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    (insertionRow (affineBlockWeights PowerSeries.X B) n).coeff 0 = 1 := by
  have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℝ) = 0 :=
    PowerSeries.constantCoeff_X
  have h := insertionRow_coeff_zero_subst hX hX hB n
  rw [PowerSeries.X_subst, insertionRow_affine_X_X] at h
  simpa only [coeff_zero_eq_eval_zero, eval_pow, eval_add, eval_one, eval_X,
    add_zero, one_pow] using h

/-- A unit singleton activity makes every exponential row nonzero. -/
theorem insertionRow_affine_X_ne_zero {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    insertionRow (affineBlockWeights PowerSeries.X B) n ≠ 0 := by
  intro hzero
  have h := insertionRow_affine_X_coeff_zero hB n
  simp only [hzero, coeff_zero, zero_ne_one] at h

end RealRooted.ExponentialRows
