/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import RealRooted.Mathlib.LinearAlgebra.Matrix.RankOneExpectation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic
/-!
# Power traces and the characteristic determinant

We prove Newton's matrix trace identity in formal power series over an arbitrary
commutative ring. A polynomial translation extends the existing determinant
pencil derivative formula, and the formal matrix geometric series supplies the
inverse. This is used for Cao--Fu, arXiv:2610.40496v1, Lemma 3.2.
-/

public section
noncomputable section
open Polynomial Matrix
namespace Matrix
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

private theorem eval_zero_derivative_translate (p : R[X]) :
    ((p.map C).comp (C (X : R[X]) + X)).derivative.eval 0 = p.derivative := by
  rw [Polynomial.derivative_comp, Polynomial.derivative_map]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_X,
    zero_add, one_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, add_zero]
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_C_X

/-- Differentiating the determinant of a constant matrix pencil gives its adjugate trace. -/
theorem derivative_det_one_sub_X_smul (M : Matrix ι ι R) :
    ((1 - (X : R[X]) • M.map C).det).derivative =
      -((1 - (X : R[X]) • M.map C).adjugate * M.map C).trace := by
  let A : Matrix ι ι R[X] := 1 - (X : R[X]) • M.map C
  have h := Matrix.eval_derivative_det_add_X_smul A (-(M.map C))
  have heq : A.map C + (X : R[X][X]) • (-(M.map C)).map C =
      (1 - (X : R[X]) • M.map C).map
        ((Polynomial.compRingHom (C (X : R[X]) + X)).comp (Polynomial.mapRingHom C)) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · simp [A, hij, Matrix.map_apply]
      ring
    · simp [A, hij, Matrix.map_apply]
      ring
  have hdet := (((Polynomial.compRingHom (C (X : R[X]) + X)).comp
    (Polynomial.mapRingHom C)).map_det A).symm
  change ((1 - (X : R[X]) • M.map C).map
    ((Polynomial.compRingHom (C (X : R[X]) + X)).comp (Polynomial.mapRingHom C))).det =
    ((A.det).map C).comp (C (X : R[X]) + X) at hdet
  rw [heq, hdet] at h
  change (((A.det).map C).comp (C (X : R[X]) + X)).derivative.eval 0 = _ at h
  rw [eval_zero_derivative_translate, Matrix.mul_neg, Matrix.trace_neg] at h
  exact h
private def powerResolvent (M : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  Matrix.of fun i j => PowerSeries.mk (fun r => (M ^ r) i j)

private theorem one_sub_X_mul_powerResolvent (M : Matrix ι ι R) :
    (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C) * powerResolvent M = 1 := by
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro r
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, powerResolvent,
    Matrix.of_apply, map_sub, PowerSeries.coeff_mk, Matrix.mul_apply]
  cases r with
  | zero =>
    by_cases hij : i = j
    · simp [Matrix.one_apply, hij]
    · simp [Matrix.one_apply, hij]
  | succ r =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [map_sum, pow_succ', Matrix.mul_apply]
    simp [Matrix.one_apply, apply_ite]

private theorem X_mul_trace_powerResolvent (M : Matrix ι ι R) :
    PowerSeries.X * (powerResolvent M * M.map PowerSeries.C).trace =
      PowerSeries.mk (fun r => if r = 0 then 0 else Matrix.trace (M ^ r)) := by
  apply PowerSeries.ext
  intro r
  cases r with
  | zero => simp
  | succ r =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [Matrix.trace, Matrix.diag_apply, map_sum, Matrix.mul_apply,
      PowerSeries.coeff_mul_C, Matrix.map_apply, powerResolvent, Matrix.of_apply,
      PowerSeries.coeff_mk, pow_succ, Matrix.mul_apply, Nat.succ_ne_zero, ite_false]

/-- Newton's trace identity for the determinant generating polynomial of a matrix. -/
theorem det_mul_powerTraceSeries (M : Matrix ι ι R) :
    (((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).det : R[X]) : PowerSeries R) *
      PowerSeries.mk (fun r => if r = 0 then 0 else Matrix.trace (M ^ r)) =
      -PowerSeries.X * PowerSeries.derivative
        (((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).det : R[X]) : PowerSeries R) := by
  let A : Matrix ι ι (PowerSeries R) := 1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C
  let G := powerResolvent M
  have hAG : A * G = 1 := one_sub_X_mul_powerResolvent M
  have hGA : G * A = 1 := mul_eq_one_comm.mp hAG
  have hadj : A.adjugate = A.det • G := by
    calc
      _ = (G * A) * A.adjugate := by rw [hGA, Matrix.one_mul]
      _ = G * (A.det • 1) := by rw [Matrix.mul_assoc, Matrix.mul_adjugate]
      _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]
  let f : R[X] →+* PowerSeries R := Polynomial.coeToPowerSeries.ringHom
  have hA : (1 - (Polynomial.X : R[X]) • M.map Polynomial.C).map f = A := by
    apply Matrix.ext
    intro i j
    simp [A, f, Matrix.one_apply, apply_ite]
    ring
  have hdet : (((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).det : R[X]) :
      PowerSeries R) = A.det := by
    have h := f.map_det (1 - (Polynomial.X : R[X]) • M.map Polynomial.C)
    change _ = ((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).map f).det at h
    rw [hA] at h
    exact h
  have hderiv := congrArg f (derivative_det_one_sub_X_smul M)
  have hadjmap : ((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).adjugate).map f =
      A.adjugate := by
    have h := f.map_adjugate (1 - (Polynomial.X : R[X]) • M.map Polynomial.C)
    change _ = ((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).map f).adjugate at h
    rw [hA] at h
    exact h
  have hderiv' : PowerSeries.derivative
      (((1 - (Polynomial.X : R[X]) • M.map Polynomial.C).det : R[X]) : PowerSeries R) =
      -(A.adjugate * M.map PowerSeries.C).trace := by
    rw [PowerSeries.derivative_coe]
    change f _ = _
    rw [hderiv]
    rw [map_neg]
    congr 1
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul,
      Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have ha := congrFun (congrFun hadjmap i) j
    simp only [Matrix.map_apply] at ha
    rw [ha]
    simp [f]
  rw [hderiv', hdet, ← X_mul_trace_powerResolvent M, hadj, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  ring

end Matrix
