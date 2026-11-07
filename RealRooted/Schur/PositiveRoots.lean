module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.Roots
import RealRooted.Schur.ElementaryPositivity
public import RealRooted.TotallyNonnegPencil.CornerInterlacing
import RealRooted.Basic.Coefficients
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-! # Positive real zeros under odd active-position parity -/

public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- Odd active-position parity negates the direction under checkerboarding. -/
theorem activeMatrix_checkerboard_of_odd {n : ℕ} {a b : Fin n → ℤ} {r : ℤ}
    (hpar : ∀ i j, a i = b j + r → Odd (i.val + j.val)) :
    checkerboard (activeMatrix a b r) = -activeMatrix a b r := by
  ext i j
  by_cases h : a i = b j + r
  · have he := (hpar i j h).neg_one_pow (α := ℝ)
    simpa [checkerboard, activeMatrix, h, ← pow_add] using he
  · simp [checkerboard, activeMatrix, h]

/-- Reflecting the parameter converts odd parity to the TN checkerboard pencil. -/
theorem elementarySubstitution_comp_neg_X_eq_checkerboardPencil {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (h k : Fin n → ℕ) (r : ℤ)
    (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r →
      Odd (i.val + j.val)) :
    (elementarySubstitution s a h k r).comp (-X) =
      checkerboardPencil (elementaryMatrix s a h k)
        (activeMatrix (fun i => (columnIndex h i : ℤ))
          (fun j => (columnIndex k j : ℤ)) r) := by
  unfold elementarySubstitution
  change (compRingHom (-X)) _ = _
  rw [RingHom.map_det]
  unfold checkerboardPencil
  rw [activeMatrix_checkerboard_of_odd hpar]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

variable {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → ℝ)
  (ha : ∀ i ∈ s, 0 ≤ a i) {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
  (hkh : ∀ i, k i ≤ h i)
  (hsize : ∀ i, h i ≤ k i + (s.filter fun j => 0 < a j).card)
  (r : ℤ)
  (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r → Odd (i.val + j.val))

include ha hh hk hkh hsize hpar

/-- The reflected odd-parity specialization is PF. -/
theorem elementarySubstitution_comp_neg_X_isPFPolynomial :
    IsPFPolynomial ((elementarySubstitution s a h k r).comp (-X)) := by
  rw [elementarySubstitution_comp_neg_X_eq_checkerboardPencil s a h k r hpar]
  have hM := elementaryMatrix_isTotallyNonneg s a ha hh hk
  apply hM.isPFPolynomial_det_map_add_X_smul_checkerboard
    (activeMatrix_isTotallyNonneg
      (fun i j hij => Int.ofNat_lt.mpr (columnIndex_strictAnti hh hij))
      (fun i j hij => Int.ofNat_lt.mpr (columnIndex_strictAnti hk hij)) r)
  exact det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize

/-- Odd-parity skew Schur specializations are nonzero and real-rooted. -/
theorem elementarySubstitution_isRealRooted_of_odd :
    elementarySubstitution s a h k r ≠ 0 ∧ (elementarySubstitution s a h k r).Splits := by
  have hd := det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize
  have hp := elementarySubstitution_comp_neg_X_isPFPolynomial s a ha hh hk hkh hsize r hpar
  have hn : elementarySubstitution s a h k r ≠ 0 := by
    intro hz
    have he := congrArg (fun p : ℝ[X] => p.eval 0) hz
    simp only [elementarySubstitution_eval_zero, eval_zero] at he
    exact hd.ne' he
  have hnc : (elementarySubstitution s a h k r).comp (-X) ≠ 0 := by
    intro hz
    apply hn
    have he := congrArg (fun p : ℝ[X] => p.comp (-X)) hz
    simpa [comp_assoc] using he
  refine ⟨hn, ?_⟩
  simpa [comp_assoc] using (hp.ne_zero_and_splits hnc).2.comp_neg_X

/-- Every root of an odd-parity skew Schur specialization is strictly positive. -/
theorem roots_elementarySubstitution_pos_of_odd :
    ∀ x ∈ (elementarySubstitution s a h k r).roots, 0 < x := by
  have hp := elementarySubstitution_comp_neg_X_isPFPolynomial s a ha hh hk hkh hsize r hpar
  have hc : ((elementarySubstitution s a h k r).comp (-X)).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero]
    simpa [eval_comp] using (det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize).ne'
  have hn : (elementarySubstitution s a h k r).comp (-X) ≠ 0 := by
    intro hz
    exact hc (by simp [hz])
  have hneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs hc
  intro x hx
  have hx' : ((elementarySubstitution s a h k r).comp (-X)).IsRoot (-x) := by
    simpa [Polynomial.IsRoot.def, eval_comp] using Polynomial.isRoot_of_mem_roots hx
  have hhx := hneg (-x) ((Polynomial.mem_roots hn).mpr hx')
  linarith

end RealRooted.Schur
