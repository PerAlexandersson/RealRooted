import RealRooted.JacobiDeformation.ActualKernelExpansion
import RealRooted.JacobiDeformation.AppellPolynomialCoordinates
import RealRooted.JacobiDeformation.ImageProductCoordinates
import RealRooted.JacobiDeformation.QuasiNodes

/-!
# The delta-zero Jacobi deformation product

At `δ = 0`, all but the top Jacobi spectral weight vanish.  The coordinate
identity then identifies the actual deformation with the monic image product.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem kernelWeight_zero_of_lt {m j : ℕ} (hjm : j < m) (s : ℝ) :
    kernelWeight m 0 s j = 0 := by
  have hne : m - j ≠ 0 := by lia
  unfold kernelWeight risingFactorial
  rw [ascPochhammer_eval_zero]
  simp [hne]

/-- At `δ = 0`, the actual Appell kernel is its top normalized Jacobi term. -/
theorem appellJacobiKernel_delta_zero_eq_top
    (m : ℕ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m ((m : ℝ) + c + d - 1) c d z =
      C (kernelWeight m 0 (c + d) m / normalizedJacobiNorm c d m *
        (normalizedShiftedJacobi m c d).eval z) *
        normalizedShiftedJacobi m c d := by
  rw [show (m : ℝ) + c + d - 1 = (m : ℝ) + c + d - 1 + 0 by ring,
    appellJacobiKernel_eq_normalizedShiftedJacobi_sum m 0 hc hd z]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp only [Fin.val_last]
  · intro a _ ha
    have halt : (a : ℕ) < m := by
      have hale : (a : ℕ) ≤ m := Nat.le_of_lt_succ a.isLt
      exact lt_of_le_of_ne hale fun h => ha (Fin.ext (h.trans (Fin.val_last m).symm))
    rw [kernelWeight_zero_of_lt halt]
    simp
  · intro h
    exact absurd (Finset.mem_univ (Fin.last m)) h

private def baseProductScalar (m : ℕ) (c d : ℝ) (t : Fin m → ℝ) : ℝ :=
  kernelWeight m 0 (c + d) m / normalizedJacobiNorm c d m /
      ((shiftedJacobiMonic m (c - 1) (d - 1)).eval 0) ^ 2 *
    Finset.univ.prod (fun i : Fin m => t i * (1 - t i))

private theorem polynomial_zero_eval_eq_scalar_imageProduct
    (m : ℕ) {c d U V : ℝ} (hc : 0 < c) (hd : 0 < d)
    (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    (hnodes : shiftedJacobiMonic m (c - 1) (d - 1) =
      Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i)))
    {xi : ℝ} (hxi : xi < -(Real.sqrt U + Real.sqrt V) ^ 2)
    (hU : 0 < U) (hV : 0 < V) :
    (polynomial m 0 c d U V).eval xi =
      (C (baseProductScalar m c d t) * imageProduct U V t).eval xi := by
  obtain ⟨r, z, hr, hrz, hz, hprod, hcomp⟩ :=
    exists_interior_coordinates_of_lt_neg_sqrt_threshold hU hV hxi
  have hp0 : (shiftedJacobiMonic m (c - 1) (d - 1)).eval 0 ≠ 0 :=
    shiftedJacobiMonic_eval_zero_ne_zero hc hd m
  have hbridge := C_eval_zero_mul_normalizedShiftedJacobi hc hd m
  have hreval := congrArg (fun p : ℝ[X] => p.eval r) hbridge
  have hzeval := congrArg (fun p : ℝ[X] => p.eval z) hbridge
  have hrnorm : (normalizedShiftedJacobi m c d).eval r =
      (shiftedJacobiMonic m (c - 1) (d - 1)).eval r /
        (shiftedJacobiMonic m (c - 1) (d - 1)).eval 0 := by
    simp only [eval_mul, eval_C] at hreval
    exact (eq_div_iff hp0).2 (by simpa [mul_comm] using hreval)
  have hznorm : (normalizedShiftedJacobi m c d).eval z =
      (shiftedJacobiMonic m (c - 1) (d - 1)).eval z /
        (shiftedJacobiMonic m (c - 1) (d - 1)).eval 0 := by
    simp only [eval_mul, eval_C] at hzeval
    exact (eq_div_iff hp0).2 (by simpa [mul_comm] using hzeval)
  have hcoord := imageProduct_coordinate_identity t ht hprod hcomp
  have hpr : (shiftedJacobiMonic m (c - 1) (d - 1)).eval r =
      Finset.univ.prod (fun i : Fin m => r - t i) := by
    rw [hnodes, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hpz : (shiftedJacobiMonic m (c - 1) (d - 1)).eval z =
      Finset.univ.prod (fun i : Fin m => z - t i) := by
    rw [hnodes, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  rw [polynomial_eval_eq_appellJacobiKernel_coordinates m 0 c d U V xi r z
      hprod hcomp,
    show (m : ℝ) + c + d - 1 + 0 = (m : ℝ) + c + d - 1 by ring,
    appellJacobiKernel_delta_zero_eq_top m hc hd z]
  simp only [eval_mul, eval_C]
  rw [hrnorm, hznorm, hpr, hpz]
  unfold baseProductScalar
  have hnorm : normalizedJacobiNorm c d m ≠ 0 :=
    (normalizedJacobiNorm_pos hc hd m).ne'
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by lia, pow_mul]
    norm_num
  have hcoord' :
      (-1 : ℝ) ^ m * xi ^ m * Finset.univ.prod (fun i : Fin m => z - t i) *
          Finset.univ.prod (fun i : Fin m => r - t i) =
        Finset.univ.prod (fun i : Fin m => t i * (1 - t i)) *
          (imageProduct U V t).eval xi := by
    calc
      _ = (-1 : ℝ) ^ m *
          ((xi ^ m * Finset.univ.prod (fun i : Fin m => r - t i)) *
            Finset.univ.prod (fun i : Fin m => z - t i)) := by ring
      _ = (-1 : ℝ) ^ m *
          (((-1 : ℝ) ^ m *
              Finset.univ.prod (fun i : Fin m => t i * (1 - t i))) *
            (imageProduct U V t).eval xi) := by rw [hcoord]
      _ = _ := by
        calc
          _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
              Finset.univ.prod (fun i : Fin m => t i * (1 - t i)) *
                (imageProduct U V t).eval xi := by ring
          _ = _ := by rw [hsign]; ring
  field_simp [hp0, hnorm]
  linear_combination kernelWeight m 0 (c + d) m * hcoord'

private theorem imageProduct_monic {m : ℕ} (U V : ℝ) (t : Fin m → ℝ) :
    (imageProduct U V t).Monic := by
  unfold imageProduct
  exact Polynomial.monic_multiset_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The degree-`m` monic shifted-Jacobi polynomial is the nodal polynomial of
an injective family of points in the open unit interval. -/
theorem exists_shiftedJacobiMonic_interior_nodes
    (m : ℕ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∃ t : Fin m → ℝ, Function.Injective t ∧
      (∀ i, 0 < t i ∧ t i < 1) ∧
        shiftedJacobiMonic m (c - 1) (d - 1) =
          Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i)) := by
  cases m with
  | zero =>
      let t : Fin 0 → ℝ := Fin.elim0
      refine ⟨t, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · simp [shiftedJacobiMonic_zero]
  | succ n =>
      have hα : -1 < c - 1 := by linarith
      have hβ : -1 < d - 1 := by linarith
      obtain ⟨t, _, htinj, hroot, _⟩ :=
        exists_quasiJacobiPolynomial_orderedRoots (q := n + 1) (by lia)
          hα hβ (τ := 0)
      refine ⟨t, htinj, ?_, ?_⟩
      · intro i
        have hmonicRoot :
            (shiftedJacobiMonic (n + 1) (c - 1) (d - 1)).IsRoot (t i) := by
          simpa [quasiJacobiPolynomial] using hroot i
        have hshiftedRoot :
            (shiftedJacobi (n + 1) (c - 1) (d - 1)).IsRoot (t i) := by
          rw [Polynomial.IsRoot.def,
            shiftedJacobi_eq_leading_mul_monic (n + 1) hα hβ]
          simp [Polynomial.IsRoot.def.mp hmonicRoot]
        exact shiftedJacobi_isRoot_mem_Ioo (n + 1) hα hβ hshiftedRoot
      · have hnodal := nodal_eq_quasiJacobiPolynomial (q := n + 1)
          (by lia) hα hβ t htinj hroot
        simpa [Lagrange.nodal, quasiJacobiPolynomial] using hnodal.symm

/-- Equation (18): at `δ = 0`, the actual finite Jacobi deformation is the
monic image product over a complete interior Jacobi node family. -/
theorem polynomial_zero_eq_imageProduct
    (m : ℕ) {c d U V : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hU : 0 < U) (hV : 0 < V)
    (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    (hnodes : shiftedJacobiMonic m (c - 1) (d - 1) =
      Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i))) :
    polynomial m 0 c d U V = imageProduct U V t := by
  let A := baseProductScalar m c d t
  have heval : polynomial m 0 c d U V = C A * imageProduct U V t := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Iio_infinite (-(Real.sqrt U + Real.sqrt V) ^ 2)).mono
    intro xi hxi
    exact polynomial_zero_eval_eq_scalar_imageProduct m hc hd t ht hnodes hxi hU hV
  have hlead := congrArg Polynomial.leadingCoeff heval
  have hA : A = 1 := by
    simpa [monic_polynomial m 0 c d U V, imageProduct_monic U V t] using hlead.symm
  rw [heval, hA, C_1, one_mul]

end RealRooted.JacobiDeformation
