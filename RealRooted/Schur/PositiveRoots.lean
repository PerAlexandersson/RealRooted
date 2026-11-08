module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.Roots
import RealRooted.Schur.ElementaryPositivity
public import RealRooted.TotallyNonnegPencil.CornerInterlacing
import RealRooted.TotallyNonnegPencil.Checkerboard
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-! # Positive real zeros of elementary determinant specializations under odd parity -/

public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- Odd active-position parity negates the direction under checkerboarding. -/
theorem activeMatrix_checkerboard_of_odd {n : ℕ} {a b : Fin n → ℤ} {r : ℤ}
    (hpar : ∀ i j, a i = b j + r → Odd (i.val + j.val)) :
    checkerboard (activeMatrix a b r) = -activeMatrix a b r := by
  simpa using activeMatrix_checkerboard_of_sign (ε := -1) fun i j h => (hpar i j h).neg_one_pow

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
  exact (elementaryMatrix_isTotallyNonneg s a ha hh hk
    ).isPFPolynomial_det_map_add_X_smul_checkerboard
    (activeMatrix_columnIndex_isTotallyNonneg hh hk r)
    (det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize)

omit hpar in
/-- The reflected specialization has nonzero constant term. -/
private theorem comp_neg_X_eval_zero_ne_zero :
    ((elementarySubstitution s a h k r).comp (-X)).eval 0 ≠ 0 := by
  simpa [eval_comp] using elementarySubstitution_eval_zero_ne_zero s a ha hh hk hkh hsize r

/-- Odd-parity elementary-coordinate specializations are nonzero and real-rooted. -/
theorem elementarySubstitution_isRealRooted_of_odd :
    elementarySubstitution s a h k r ≠ 0 ∧ (elementarySubstitution s a h k r).Splits := by
  have hq := (elementarySubstitution_comp_neg_X_isPFPolynomial s a ha hh hk hkh hsize r hpar
    ).ne_zero_and_splits_of_eval_zero_ne_zero
    (comp_neg_X_eval_zero_ne_zero s a ha hh hk hkh hsize r)
  have hn : elementarySubstitution s a h k r ≠ 0 := fun hz =>
    elementarySubstitution_eval_zero_ne_zero s a ha hh hk hkh hsize r (by simp [hz])
  exact ⟨hn, by simpa [comp_assoc] using hq.2.comp_neg_X⟩

/-- Every root of an odd-parity elementary-coordinate specialization is strictly positive. -/
theorem roots_elementarySubstitution_pos_of_odd :
    ∀ x ∈ (elementarySubstitution s a h k r).roots, 0 < x := by
  have hneg := (elementarySubstitution_comp_neg_X_isPFPolynomial s a ha hh hk hkh hsize r hpar
    ).roots_neg_of_eval_zero_ne_zero (comp_neg_X_eval_zero_ne_zero s a ha hh hk hkh hsize r)
  intro x hx
  have hx' : ((elementarySubstitution s a h k r).comp (-X)).IsRoot (-x) := by
    simpa [Polynomial.IsRoot.def, eval_comp] using Polynomial.isRoot_of_mem_roots hx
  have hnc : (elementarySubstitution s a h k r).comp (-X) ≠ 0 := fun hz =>
    comp_neg_X_eval_zero_ne_zero s a ha hh hk hkh hsize r (by simp [hz])
  linarith [hneg (-x) ((Polynomial.mem_roots hnc).mpr hx')]

end RealRooted.Schur
