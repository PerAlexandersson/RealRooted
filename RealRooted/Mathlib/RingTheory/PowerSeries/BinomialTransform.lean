/-
Copyright (c) 2026 RealRooted contributors, Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors, Tau Ceti contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Step
public import RealRooted.Mathlib.Algebra.Polynomial.MomentTranslation
import RealRooted.Mathlib.Algebra.Polynomial.MomentTranslationSucc
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Binomial translation of formal power series

The formal substitution `G * f(X * G)`, with `G = (1 - c X)⁻¹`, is the
binomial transform of the coefficient sequence. A shift recurrence proves
the coefficient formula over any commutative ring, without convergence or
division by integers. The coefficient-shift argument follows
`PowerSeries.coeff_succ_subst_X_mul` in Tau Ceti (Apache 2.0).
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The binomial transform, expressed by a formal fractional-linear substitution. -/
@[expose] noncomputable def binomialTransform (c : R) (f : R⟦X⟧) : R⟦X⟧ :=
  stieltjesStep c 1 * f.subst (X * stieltjesStep c 1)

/-- The geometric factor in the binomial transform inverts `1 - c X`. -/
theorem one_sub_mul_binomialTransform (c : R) (f : R⟦X⟧) :
    (1 - C c * X) * binomialTransform c f =
      f.subst (X * stieltjesStep c 1) := by
  rw [binomialTransform, ← mul_assoc]
  have h : (1 - C c * X) * stieltjesStep c 1 = 1 := by
    simpa only [mul_one] using one_sub_mul_stieltjesStep c (1 : R⟦X⟧)
  rw [h, one_mul]

/-- A binomial transform preserves the constant coefficient. -/
@[simp] theorem constantCoeff_binomialTransform (c : R) (f : R⟦X⟧) :
    constantCoeff (binomialTransform c f) = constantCoeff f := by
  rw [binomialTransform, map_mul, constantCoeff_stieltjesStep, one_mul]
  have h := constantCoeff_subst_of_constantCoeff_zero
    (R := R) (a := X * stieltjesStep c (1 : R⟦X⟧))
    (by rw [← constantCoeff_eq]; simp) f
  simpa only [← constantCoeff_eq, Algebra.algebraMap_self, RingHom.id_apply] using h

/-- The next coefficient is determined by the transform of the shifted input. -/
theorem coeff_succ_binomialTransform (c : R) (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (binomialTransform c f) =
      c * coeff n (binomialTransform c f) +
        coeff n (binomialTransform c (mk fun k => coeff (k + 1) f)) := by
  have hP : HasSubst (X * stieltjesStep c (1 : R⟦X⟧)) :=
    .of_constantCoeff_zero' (by simp)
  have hshift : coeff (n + 1) (f.subst (X * stieltjesStep c 1)) =
      coeff n (binomialTransform c (mk fun k => coeff (k + 1) f)) := by
    conv_lhs => rw [f.eq_X_mul_shift_add_const]
    rw [subst_add hP, subst_mul hP, subst_X hP, subst_C, ← C_apply,
      mul_assoc, map_add, coeff_succ_X_mul]
    simp only [coeff_C, Nat.add_one_ne_zero, ite_false, add_zero, binomialTransform]
  have h := congrArg (coeff (n + 1)) (one_sub_mul_binomialTransform c f)
  simp only [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul,
    coeff_succ_X_mul, hshift] at h
  change coeff (n + 1) (binomialTransform c f) -
      c * coeff n (binomialTransform c f) =
      coeff n (binomialTransform c (mk fun k => coeff (k + 1) f)) at h
  linear_combination h

/-- Formal binomial substitution translates the coefficient moment sequence. -/
theorem coeff_binomialTransform (c : R) (f : R⟦X⟧) (n : ℕ) :
    coeff n (binomialTransform c f) =
      Polynomial.momentTranslate c (fun k => coeff k f) n := by
  induction n generalizing f with
  | zero =>
      rw [Polynomial.momentTranslate_zero, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_binomialTransform, coeff_zero_eq_constantCoeff_apply]
  | succ n ih =>
      rw [coeff_succ_binomialTransform, ih, ih, Polynomial.momentTranslate_succ]
      simp only [coeff_mk]

/-- The ordinary series of translated moments is the formal binomial transform. -/
theorem binomialTransform_mk (c : R) (m : ℕ → R) :
    binomialTransform c (mk m) = mk (Polynomial.momentTranslate c m) := by
  ext n
  simp only [coeff_binomialTransform, coeff_mk]

/-- Constant outer mass factors commute with the binomial transform. -/
theorem binomialTransform_C_mul (c a : R) (f : R⟦X⟧) :
    binomialTransform c (C a * f) = C a * binomialTransform c f := by
  have hy : HasSubst (X * stieltjesStep c (1 : R⟦X⟧)) :=
    .of_constantCoeff_zero' (by simp)
  simp only [binomialTransform, subst_mul hy, subst_C, ← C_apply]
  ring

/-- Successive formal binomial transforms add their parameters. -/
theorem binomialTransform_binomialTransform (b c : R) (f : R⟦X⟧) :
    binomialTransform b (binomialTransform c f) = binomialTransform (b + c) f := by
  ext n
  simp only [coeff_binomialTransform, Polynomial.momentTranslate_momentTranslate]

end PowerSeries
