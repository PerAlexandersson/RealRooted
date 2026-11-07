module

public import RealRooted.PFPolynomial
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.TotallyNonnegPencil.Checkerboard
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.CornerPerturbation
import RealRooted.Compatibility.Three
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-! # Corner perturbations of checkerboard determinant pencils -/

@[expose] public section

open Polynomial

namespace Matrix

/-- The polynomial determinant of a checkerboard-signed matrix pencil. -/
noncomputable def checkerboardPencil {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ[X] :=
  det (A.map C + (X : ℝ[X]) • (checkerboard B).map C)

/-- The constant value of the pencil is the determinant of its constant matrix. -/
@[simp] theorem checkerboardPencil_eval_zero {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) : (checkerboardPencil A B).eval 0 = A.det := by
  simp [checkerboardPencil, eval_det]

/-- Perturbing the constant northwest corner adds the complementary pencil. -/
theorem checkerboardPencil_add_single_left {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ) :
    checkerboardPencil (A + single 0 0 c) B = checkerboardPencil A B +
      C c * checkerboardPencil (A.submatrix Fin.succ Fin.succ)
        (B.submatrix Fin.succ Fin.succ) := by
  have hm : (A + single 0 0 c).map C + (X : ℝ[X]) • (checkerboard B).map C =
      A.map C + (X : ℝ[X]) • (checkerboard B).map C + single 0 0 (C c) := by
    apply Matrix.ext
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [hi, hj, eq_comm, add_comm, add_assoc]
  unfold checkerboardPencil
  rw [hm, det_add_single_zero_zero]
  congr 2
  congr 1
  ext i j
  simp [checkerboard, pow_succ]

/-- Perturbing the variable northwest corner adds `X` times the complementary pencil. -/
theorem checkerboardPencil_add_single_right {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ) :
    checkerboardPencil A (B + single 0 0 c) = checkerboardPencil A B +
      C c * X * checkerboardPencil (A.submatrix Fin.succ Fin.succ)
        (B.submatrix Fin.succ Fin.succ) := by
  have hm : A.map C + (X : ℝ[X]) • (checkerboard (B + single 0 0 c)).map C =
      A.map C + (X : ℝ[X]) • (checkerboard B).map C + single 0 0 (C c * X) := by
    apply Matrix.ext
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [checkerboard, hi, hj, eq_comm]
    ring
  unfold checkerboardPencil
  rw [hm, det_add_single_zero_zero]
  congr 2
  congr 1
  ext i j
  simp [checkerboard, pow_succ]

/-- Nonnegative constant-corner perturbations preserve PF determinant polynomials. -/
theorem IsTotallyNonneg.isPFPolynomial_checkerboardPencil_add_corner {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) (hdet : 0 < A.det)
    {c : ℝ} (hc : 0 ≤ c) :
    RealRooted.IsPFPolynomial (checkerboardPencil A B + C c *
      checkerboardPencil (A.submatrix Fin.succ Fin.succ)
        (B.submatrix Fin.succ Fin.succ)) := by
  rw [← checkerboardPencil_add_single_left]
  apply (hA.add_single_zero_zero hc).isPFPolynomial_det_map_add_X_smul_checkerboard hB
  rw [det_add_single_zero_zero]
  exact add_pos_of_pos_of_nonneg hdet
    (mul_nonneg hc (hA Fin.strictMono_succ Fin.strictMono_succ))

/-- Nonnegative variable-corner perturbations preserve PF determinant polynomials. -/
theorem IsTotallyNonneg.isPFPolynomial_checkerboardPencil_add_X_corner {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) (hdet : 0 < A.det)
    {c : ℝ} (hc : 0 ≤ c) :
    RealRooted.IsPFPolynomial (checkerboardPencil A B + C c * X *
      checkerboardPencil (A.submatrix Fin.succ Fin.succ)
        (B.submatrix Fin.succ Fin.succ)) := by
  rw [← checkerboardPencil_add_single_right]
  exact hA.isPFPolynomial_det_map_add_X_smul_checkerboard
    (hB.add_single_zero_zero hc) hdet

/-- A split endpoint and a nonnegative affine ray give compatibility. -/
private theorem compatible_of_split_ray {f g : ℝ[X]} (hf : f.Splits)
    (hray : ∀ c : ℝ, 0 ≤ c → (g + C c * f).Splits) :
    RealRooted.Compatible f g := by
  intro a b ha hb
  by_cases hzero : C a * f + C b * g = 0
  · exact Or.inl hzero
  refine Or.inr ⟨hzero, ?_⟩
  by_cases hb0 : b = 0
  · simpa [hb0] using hf.C_mul a
  have heq : C a * f + C b * g = C b * (g + C (a / b) * f) := by
    rw [mul_add, ← mul_assoc, ← map_mul, mul_div_cancel₀ a hb0]
    ring
  rw [heq]
  exact (hray (a / b) (div_nonneg ha hb)).C_mul b

/-- Consecutive southeast sections of an invertible TN pencil weakly interlace.
No triangularity is required of the variable matrix. Positive constant
minors exclude the zero polynomial, but repeated and common roots are allowed. -/
theorem IsTotallyNonneg.strictInterl_checkerboardPencil_succ {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) (hdet : 0 < A.det)
    (hminor : 0 < (A.submatrix Fin.succ Fin.succ).det) :
    RealRooted.StrictInterl
      (checkerboardPencil (A.submatrix Fin.succ Fin.succ)
        (B.submatrix Fin.succ Fin.succ)) (checkerboardPencil A B) := by
  let f := checkerboardPencil (A.submatrix Fin.succ Fin.succ)
    (B.submatrix Fin.succ Fin.succ)
  let g := checkerboardPencil A B
  have hAs := hA.submatrix Fin.strictMono_succ Fin.strictMono_succ
  have hf : RealRooted.IsPFPolynomial f :=
    hAs.isPFPolynomial_det_map_add_X_smul_checkerboard
      (hB.submatrix Fin.strictMono_succ Fin.strictMono_succ) hminor
  have hg : RealRooted.IsPFPolynomial g :=
    hA.isPFPolynomial_det_map_add_X_smul_checkerboard hB hdet
  have hf0 : f ≠ 0 := by
    intro hz
    have he := congrArg (fun p : ℝ[X] => p.eval 0) hz
    simp only [f, checkerboardPencil_eval_zero, eval_zero] at he
    exact hminor.ne' he
  have hg0 : g ≠ 0 := by
    intro hz
    have he := congrArg (fun p : ℝ[X] => p.eval 0) hz
    simp only [g, checkerboardPencil_eval_zero, eval_zero] at he
    exact hdet.ne' he
  have hfs := (hf.ne_zero_and_splits hf0).2
  apply RealRooted.strictInterl_of_compatible_and_X_mul_left
    hf0 hg0 hf.hasNonnegCoeffs hg.hasNonnegCoeffs
  · apply compatible_of_split_ray hfs
    intro c hc
    have hp := hA.isPFPolynomial_checkerboardPencil_add_corner hB hdet hc
    exact hp.eq_zero_or_splits.elim (fun hz => hz ▸ Polynomial.Splits.zero) id
  · apply compatible_of_split_ray ((by simp : (X : ℝ[X]).Splits).mul hfs)
    intro c hc
    have hp := hA.isPFPolynomial_checkerboardPencil_add_X_corner hB hdet hc
    simpa only [mul_assoc] using
      hp.eq_zero_or_splits.elim (fun hz => hz ▸ Polynomial.Splits.zero) id

/-- Reversing both index orders preserves a checkerboard pencil determinant. -/
@[simp] theorem checkerboardPencil_submatrix_rev {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    checkerboardPencil (A.submatrix Fin.revPerm Fin.revPerm)
      (B.submatrix Fin.revPerm Fin.revPerm) = checkerboardPencil A B := by
  have hc : checkerboard (B.submatrix Fin.revPerm Fin.revPerm) =
      (checkerboard B).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    have hs : (-1 : ℝ) ^ (i.val + j.val) = (-1 : ℝ) ^ ((Fin.rev i).val + (Fin.rev j).val) := by
      apply neg_one_pow_congr
      simp only [Nat.even_iff, Fin.val_rev]
      lia
    simpa [checkerboard, Fin.revPerm, ← mul_assoc, ← pow_add] using
      congrArg (fun c : ℝ => c * B (Fin.rev i) (Fin.rev j)) hs
  unfold checkerboardPencil
  rw [hc]
  change det ((A.map C + (X : ℝ[X]) • (checkerboard B).map C).submatrix
    Fin.revPerm Fin.revPerm) = _
  exact det_submatrix_equiv_self _ _

/-- Consecutive leading sections of a general TN pencil weakly interlace.
Positive constant determinants exclude zero polynomials; the variable matrix
may be singular and need not be triangular. -/
theorem IsTotallyNonneg.strictInterl_checkerboardPencil_castSucc {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) (hdet : 0 < A.det)
    (hminor : 0 < (A.submatrix Fin.castSucc Fin.castSucc).det) :
    RealRooted.StrictInterl
      (checkerboardPencil (A.submatrix Fin.castSucc Fin.castSucc)
        (B.submatrix Fin.castSucc Fin.castSucc)) (checkerboardPencil A B) := by
  have hAr : (A.submatrix Fin.revPerm Fin.revPerm).IsTotallyNonneg := by
    simpa [Matrix.reindex] using hA.finRev
  have hBr : (B.submatrix Fin.revPerm Fin.revPerm).IsTotallyNonneg := by
    simpa [Matrix.reindex] using hB.finRev
  have hcut (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      (M.submatrix Fin.revPerm Fin.revPerm).submatrix Fin.succ Fin.succ =
        (M.submatrix Fin.castSucc Fin.castSucc).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [Fin.revPerm, Fin.rev_succ]
  have hp := hAr.strictInterl_checkerboardPencil_succ hBr
    (by simpa only [det_submatrix_equiv_self] using hdet)
    (by simpa only [hcut, det_submatrix_equiv_self] using hminor)
  simpa only [hcut, checkerboardPencil_submatrix_rev] using hp

end Matrix
