module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.MinorPositivity

/-! # Strict positivity of elementary skew Jacobi–Trudi determinants -/

public section

open Polynomial Matrix

namespace RealRooted.Schur

/-- Positive elementary factors are positive scalings of monic linear factors. -/
private theorem elementaryPolynomial_eq_scaled_product {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    elementaryPolynomial s a =
      C (∏ i ∈ s, a i) * ∏ i ∈ s, (X - C (-(a i)⁻¹)) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hai := (ha i hi).ne'
  simp only [map_neg, sub_neg_eq_add, mul_add, ← map_mul, mul_inv_cancel₀ hai, map_one]
  ring

/-- Elementary Toeplitz minors are positive throughout the alphabet-size band. -/
theorem det_toeplitz_elementary_pos {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) {n : ℕ}
    (rows cols : Fin n → ℕ) (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hlo : ∀ i, cols i ≤ rows i) (hhi : ∀ i, rows i ≤ cols i + s.card) :
    0 < ((toeplitz (elementaryPolynomial s a).coeff).submatrix rows cols).det := by
  rw [elementaryPolynomial_eq_scaled_product s a ha, toeplitz_const_mul]
  change 0 < ((∏ i ∈ s, a i) •
    (toeplitz (∏ i ∈ s, (X - C (-(a i)⁻¹))).coeff).submatrix rows cols).det
  rw [det_smul]
  apply mul_pos (pow_pos (Finset.prod_pos ha) _)
  exact det_toeplitz_prod_linear_pos s (fun i => (a i)⁻¹)
    (fun i hi => inv_pos.mpr (ha i hi)) rows cols hrows hcols hlo hhi

/-- A positive alphabet at least as large as every skew column gives a positive
constant dual Jacobi–Trudi determinant. The two column boundaries may have repeated heights. -/
theorem det_elementaryMatrix_pos {ι : Type*} {n : ℕ} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
    (hkh : ∀ i, k i ≤ h i) (hsize : ∀ i, h i ≤ k i + s.card) :
    0 < (elementaryMatrix s a h k).det := by
  have hr := columnIndex_strictAnti hh
  have hc := columnIndex_strictAnti hk
  have hp := det_toeplitz_elementary_pos s a ha
    (fun i => columnIndex h (Fin.rev i)) (fun i => columnIndex k (Fin.rev i))
    (fun _ _ hij => hr (Fin.rev_lt_rev.mpr hij))
    (fun _ _ hij => hc (Fin.rev_lt_rev.mpr hij))
  have hlo : ∀ i, columnIndex k (Fin.rev i) ≤ columnIndex h (Fin.rev i) := by
    intro i
    have hi := (Fin.rev i).isLt
    have hb := hkh (Fin.rev i)
    dsimp [columnIndex]
    lia
  have hhi : ∀ i, columnIndex h (Fin.rev i) ≤ columnIndex k (Fin.rev i) + s.card := by
    intro i
    have hi := (Fin.rev i).isLt
    have hb := hsize (Fin.rev i)
    dsimp [columnIndex]
    lia
  have hp' := hp hlo hhi
  change 0 < ((elementaryMatrix s a h k).submatrix Fin.revPerm Fin.revPerm).det at hp'
  simpa only [Matrix.det_submatrix_equiv_self] using hp'

/-- Zero letters do not change the elementary generating polynomial. -/
theorem elementaryPolynomial_filter_pos {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    elementaryPolynomial (s.filter fun i => 0 < a i) a = elementaryPolynomial s a := by
  classical
  unfold elementaryPolynomial
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hp : 0 < a i
  · simp [hp]
  · have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
    simp [hz]

/-- For a nonnegative alphabet, only its positive letters count toward the
skew-column-height bound needed for strict positivity. -/
theorem det_elementaryMatrix_pos_of_nonneg {ι : Type*} {n : ℕ} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
    (hkh : ∀ i, k i ≤ h i)
    (hsize : ∀ i, h i ≤ k i + (s.filter fun j => 0 < a j).card) :
    0 < (elementaryMatrix s a h k).det := by
  classical
  have hp := det_elementaryMatrix_pos (s.filter fun i => 0 < a i) a
    (fun i hi => (Finset.mem_filter.mp hi).2) hh hk hkh hsize
  simpa only [elementaryMatrix, elementaryPolynomial_filter_pos s a ha] using hp

end RealRooted.Schur
