import RealRooted.MultivariateStability.Barrier
import RealRooted.MultivariateStability.MixedCharacteristic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Starting barrier values for the Marcus–Spielman–Srivastava argument

For positive semidefinite `A_1, …, A_m` with `Σ A_i = 1`, let `P(y) = det(Σ y_i A_i)`
(`realDetPencil`).  For `t > 0` the point `t·1` is above the roots of `P`
(`realDetPencil_aboveRoots`), and Jacobi's formula gives `barrier i P (t·1) = tr(A_i)/t`
(`realDetPencil_barrier_eq_trace_div`); hence `barrier i P (t·1) ≤ ε/t` when `tr(A_i) ≤ ε`
(issue #950, step M5).
-/

open Matrix MvPolynomial
open scoped BigOperators MatrixOrder

noncomputable section

namespace RealRooted

private theorem eval_realDetPencil
    (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (z : Fin m → ℝ) :
    MvPolynomial.eval z (realDetPencil 0 B) =
      (∑ k, z k • B k).det := by
  unfold realDetPencil
  erw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change MvPolynomial.eval z
      (MvPolynomial.C (0 : ℝ) + ∑ k, MvPolynomial.X k *
        MvPolynomial.C (B k i j)) = _
  simp [Matrix.sum_apply, Matrix.smul_apply]

/-- Evaluation of the real determinant pencil is the determinant of the
evaluated matrix pencil. -/
theorem realDetPencil_eval
    {n m : ℕ} (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (z : Fin m → ℝ) :
    MvPolynomial.eval z (realDetPencil 0 As) =
      (∑ k, z k • As k).det := by
  exact eval_realDetPencil As z

/-- A normalized PSD determinant pencil is positive above the constant point
`t • 1` for every positive `t`. -/
theorem realDetPencil_aboveRoots
    {n m : ℕ} (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef)
    (hsum : ∑ i, As i = 1) {t : ℝ} (ht : 0 < t) :
    AboveRoots (realDetPencil 0 As) (fun _ => t) := by
  intro v hv
  rw [realDetPencil_eval]
  have hpos : (t • (1 : Matrix (Fin n) (Fin n) ℝ) +
      ∑ i, v i • As i).PosDef := by
    apply Matrix.PosDef.add_posSemidef
    · simpa using Matrix.PosDef.smul Matrix.PosDef.one ht
    · exact Matrix.posSemidef_sum Finset.univ (fun i hi =>
        Matrix.PosSemidef.smul (hAs i) (hv i))
  convert hpos.det_pos using 1
  rw [← hsum]
  congr 1
  simp_rw [Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]

private def coordinateDeterminant {n : ℕ} (t : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  Matrix.det ((Polynomial.C t) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
    (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)

private theorem coordinateRestriction_detPencil
    {n m : ℕ} (As : Fin m → Matrix (Fin n) (Fin n) ℝ) (hsum : ∑ k, As k = 1)
    (i : Fin m) (t : ℝ) :
    coordinateRestriction (fun _ : Fin m => t) i (realDetPencil 0 As) =
      coordinateDeterminant t (As i) := by
  classical
  have hsum_update (s : ℝ) :
      ∑ k, Function.update (fun _ : Fin m => t) i (t + s) k • As k =
        t • (1 : Matrix (Fin n) (Fin n) ℝ) + s • As i := by
    calc
      ∑ k, Function.update (fun _ : Fin m => t) i (t + s) k • As k =
          (∑ k ∈ Finset.univ.erase i,
            Function.update (fun _ : Fin m => t) i (t + s) k • As k) +
            (t + s) • As i := by
        rw [← Finset.sum_erase_add (s := Finset.univ)
          (f := fun k => Function.update (fun _ : Fin m => t) i (t + s) k • As k)
          (Finset.mem_univ i)]
        simp
      _ = (∑ k ∈ Finset.univ.erase i, t • As k) + (t + s) • As i := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_erase] at hk
        simp [hk.1]
      _ = t • ((∑ k ∈ Finset.univ.erase i, As k) + As i) + s • As i := by
        rw [← Finset.smul_sum]
        ext r c
        simp only [Matrix.add_apply, Matrix.smul_apply]
        ring
      _ = t • (∑ k, As k) + s • As i := by
        rw [Finset.sum_erase_add (s := Finset.univ)
          (f := As) (Finset.mem_univ i)]
      _ = t • (1 : Matrix (Fin n) (Fin n) ℝ) + s • As i := by rw [hsum]
  apply Polynomial.funext
  intro s
  rw [eval_coordinateRestriction]
  rw [realDetPencil_eval]
  rw [hsum_update]
  unfold coordinateDeterminant
  change (t • (1 : Matrix (Fin n) (Fin n) ℝ) + s • As i).det =
    (Polynomial.evalRingHom s) (Matrix.det
      ((Polynomial.C t) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
        (Polynomial.X : Polynomial ℝ) • (As i).map Polynomial.C))
  rw [(Polynomial.evalRingHom s).map_det]
  congr 1
  ext r c
  by_cases hrc : r = c <;>
    simp [Matrix.add_apply, Matrix.smul_apply, hrc] <;> ring

private theorem coordinateDeterminant_factor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) :
    coordinateDeterminant t A = Polynomial.C (t ^ n) *
      Matrix.det (1 + (Polynomial.C t⁻¹ * Polynomial.X) • A.map Polynomial.C) := by
  have hct : (Polynomial.C t : Polynomial ℝ) * Polynomial.C t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ht, map_one]
  have hprod (a : ℝ) :
      (Polynomial.C t : Polynomial ℝ) *
          (Polynomial.C t⁻¹ * Polynomial.X * Polynomial.C a) =
        Polynomial.C a * Polynomial.X := by
    calc
      (Polynomial.C t : Polynomial ℝ) *
          (Polynomial.C t⁻¹ * Polynomial.X * Polynomial.C a) =
          (Polynomial.C t * Polynomial.C t⁻¹) *
            (Polynomial.X * Polynomial.C a) := by ring
      _ = Polynomial.C a * Polynomial.X := by rw [hct, one_mul]; ring
  have hmatrix :
      (Polynomial.C t) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C =
        (Polynomial.C t) •
          (1 + (Polynomial.C t⁻¹ * Polynomial.X) • A.map Polynomial.C) := by
    apply Matrix.ext
    intro r c
    by_cases hrc : r = c
    · subst c
      simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, map_apply,
        Polynomial.X_mul_C]
      rw [mul_add, mul_one, hprod]
    · simp only [Matrix.add_apply, Matrix.smul_apply, ne_eq, hrc, not_false_eq_true, one_apply_ne,
        smul_eq_mul, mul_zero, map_apply, Polynomial.X_mul_C, zero_add]
      exact (hprod (A r c)).symm
  unfold coordinateDeterminant
  rw [hmatrix, Matrix.det_smul]
  simp only [Fintype.card_fin, map_pow]

private theorem coordinateDeterminant_derivative_eval_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) :
    (coordinateDeterminant t A).derivative.eval 0 =
      t ^ n * (t⁻¹ * A.trace) := by
  rw [coordinateDeterminant_factor A ht, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_mul]
  have hscaled :
      (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.C t⁻¹ * Polynomial.X) • A.map Polynomial.C =
        (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          ((Polynomial.X : Polynomial ℝ) •
            (((t⁻¹ : ℝ) • A).map Polynomial.C)) := by
    apply Matrix.ext
    intro r c
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
    ring
  rw [hscaled, Matrix.derivative_det_one_add_X_smul]
  simp only [Polynomial.eval_C, Matrix.trace_smul, smul_eq_mul]

private theorem coordinateDeterminant_eval_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (coordinateDeterminant t A).eval 0 = t ^ n := by
  unfold coordinateDeterminant
  change (Polynomial.evalRingHom 0) (Matrix.det _) = _
  erw [RingHom.map_det]
  change ((Polynomial.C t • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).map
        (Polynomial.eval 0)).det = _
  have hmatrix :
      ((Polynomial.C t) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).map
        (Polynomial.eval 0) = t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    apply Matrix.ext
    intro r c
    by_cases hrc : r = c <;>
      simp [Matrix.add_apply, Matrix.smul_apply, hrc]
  rw [hmatrix, Matrix.det_smul]
  rw [Matrix.det_one]
  simp only [Fintype.card_fin, mul_one]

/-- Jacobi's starting-barrier identity for a normalized PSD determinant pencil. -/
theorem realDetPencil_barrier_eq_trace_div {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hsum : ∑ k, As k = 1) (i : Fin m) {t : ℝ} (ht : 0 < t) :
    barrier i (realDetPencil 0 As) (fun _ => t) = (As i).trace / t := by
  rw [barrier_eq_coordinateRestriction]
  unfold univariateBarrier
  rw [coordinateRestriction_detPencil As hsum i t,
    coordinateDeterminant_derivative_eval_zero (As i) ht.ne',
    coordinateDeterminant_eval_zero]
  have htpow : t ^ n ≠ 0 := pow_ne_zero n ht.ne'
  field_simp [ht.ne', htpow]

/-- A trace bound gives the corresponding reciprocal lower-barrier bound. -/
theorem realDetPencil_barrier_le_of_trace_le {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hsum : ∑ k, As k = 1) (i : Fin m) {t ε : ℝ} (ht : 0 < t)
    (hε : (As i).trace ≤ ε) :
    barrier i (realDetPencil 0 As) (fun _ => t) ≤ ε / t := by
  rw [realDetPencil_barrier_eq_trace_div As hsum i ht]
  exact (div_le_div_of_nonneg_right hε ht.le)

end RealRooted
