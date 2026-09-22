import RealRooted.JacobiDeformation.ImageProductCoordinates
import RealRooted.JacobiDeformation.ImageProductDerivative
import RealRooted.JacobiDeformation.JacobiLowering

/-!
# The nonroot critical image-product boundary condition

This is the finite-product boundary calculation before any identification of
the image product with a deformation polynomial.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- At a nonroot critical point of the image product, the two Jacobi values
in the coordinate identity are nonzero and their preceding-Jacobi ratios
agree.  The complete Jacobi node product is explicit bookkeeping input. -/
theorem imageProduct_critical_boundary_condition
    (n : ℕ) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (t : Fin (n + 1) → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {xi r z U V : ℝ}
    (hnodes : shiftedJacobiMonic (n + 1) α β =
      Finset.univ.prod (fun i : Fin (n + 1) => (X : ℝ[X]) - C (t i)))
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V)
    (himage : (imageProduct U V t).eval xi ≠ 0)
    (hderivative : (imageProduct U V t).derivative.eval xi = 0) :
    (shiftedJacobiMonic (n + 1) α β).eval r ≠ 0 ∧
      (shiftedJacobiMonic (n + 1) α β).eval z ≠ 0 ∧
      (shiftedJacobiMonic n α β).eval r /
          (shiftedJacobiMonic (n + 1) α β).eval r =
        (shiftedJacobiMonic n α β).eval z /
          (shiftedJacobiMonic (n + 1) α β).eval z := by
  let p : ℝ[X] := shiftedJacobiMonic (n + 1) α β
  let prev : ℝ[X] := shiftedJacobiMonic n α β
  let q : ℝ[X] := Finset.univ.prod
    (fun i : Fin (n + 1) => (X : ℝ[X]) - C (t i))
  let N : ℝ := (n : ℝ) + 1
  let A : ℝ := ((2 * N + (α + β + 2)) *
    shiftedJacobiDiag (n + 1) α β - (α + 1)) / 2
  let B : ℝ := (2 * N + (α + β + 2) - 1) *
    shiftedJacobiSubdiag (n + 1) α β
  change p = q at hnodes
  have hqevalr : q.eval r = Finset.univ.prod (fun i : Fin (n + 1) => r - t i) := by
    simp [q, Polynomial.eval_prod]
  have hqevalz : q.eval z = Finset.univ.prod (fun i : Fin (n + 1) => z - t i) := by
    simp [q, Polynomial.eval_prod]
  have hcoordinate_nonzero :
      xi ^ (n + 1) * Finset.univ.prod (fun i : Fin (n + 1) => r - t i) *
        Finset.univ.prod (fun i : Fin (n + 1) => z - t i) ≠ 0 := by
    rw [imageProduct_coordinate_identity t ht hprod hcomp]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (prod_node_mul_one_sub_pos t ht).ne') himage
  have hqr : q.eval r ≠ 0 := by
    intro hzero
    apply hcoordinate_nonzero
    rw [← hqevalr, hzero]
    simp
  have hqz : q.eval z ≠ 0 := by
    intro hzero
    apply hcoordinate_nonzero
    rw [← hqevalz, hzero]
    simp
  have hpr : p.eval r ≠ 0 := by
    rw [hnodes]
    exact hqr
  have hpz : p.eval z ≠ 0 := by
    rw [hnodes]
    exact hqz
  have hboundary := imageProduct_derivative_identity_of_derivative_eval_zero
    t ht hprod hcomp hqr hqz himage hderivative
  change ((n + 1 : ℕ) : ℝ) * (r - z) +
      r * (1 - r) * q.derivative.eval r / q.eval r -
        z * (1 - z) * q.derivative.eval z / q.eval z = 0 at hboundary
  rw [← hnodes] at hboundary
  have hboundaryN : N * (r - z) +
      r * (1 - r) * p.derivative.eval r / p.eval r -
        z * (1 - z) * p.derivative.eval z / p.eval z = 0 := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using hboundary
  have hlowering :
      X * (1 - X) * p.derivative =
        (-C N * X + C A) * p + C B * prev := by
    simpa only [p, prev, N, A, B, Nat.cast_add, Nat.cast_one] using
      shiftedJacobiMonic_lowering_succ n hα hβ
  have hBpos : 0 < B := by
    simpa only [B, N, Nat.cast_add, Nat.cast_one] using
      shiftedJacobiMonic_lowering_succ_subdiag_pos n hα hβ
  have hlr := congrArg (fun f : ℝ[X] => f.eval r) hlowering
  have hlz := congrArg (fun f : ℝ[X] => f.eval z) hlowering
  have hlr' :
      r * (1 - r) * p.derivative.eval r =
        (-N * r + A) * p.eval r + B * prev.eval r := by
    simpa only [eval_add, eval_mul, eval_sub, eval_neg, eval_C, eval_X,
      eval_one] using hlr
  have hlz' :
      z * (1 - z) * p.derivative.eval z =
        (-N * z + A) * p.eval z + B * prev.eval z := by
    simpa only [eval_add, eval_mul, eval_sub, eval_neg, eval_C, eval_X,
      eval_one] using hlz
  have hlrdiv :
      r * (1 - r) * p.derivative.eval r / p.eval r =
        -N * r + A + B * (prev.eval r / p.eval r) := by
    calc
      _ = ((-N * r + A) * p.eval r + B * prev.eval r) / p.eval r := by
        rw [hlr']
      _ = _ := by
        field_simp [hpr]
  have hlzdiv :
      z * (1 - z) * p.derivative.eval z / p.eval z =
        -N * z + A + B * (prev.eval z / p.eval z) := by
    calc
      _ = ((-N * z + A) * p.eval z + B * prev.eval z) / p.eval z := by
        rw [hlz']
      _ = _ := by
        field_simp [hpz]
  refine ⟨hpr, hpz, ?_⟩
  have hratio :
      B * (prev.eval r / p.eval r - prev.eval z / p.eval z) = 0 := by
    linear_combination hboundaryN - hlrdiv + hlzdiv
  exact sub_eq_zero.mp ((mul_eq_zero.mp hratio).resolve_left hBpos.ne')

end RealRooted.JacobiDeformation
