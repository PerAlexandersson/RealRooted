module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.ElementaryPositivity
public import RealRooted.TotallyNonnegPencil.CornerInterlacing

/-! # Consecutive interlacing of parity-compatible skew Schur determinants -/

public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- Removing the first column of a shape agrees with the boundary-index shift. -/
@[simp] theorem columnIndex_succ {n : ℕ} (h : Fin (n + 1) → ℕ) (i : Fin n) :
    columnIndex h i.succ = columnIndex (h ∘ Fin.succ) i := by
  have hi := i.isLt
  simp only [columnIndex, Fin.val_succ, Function.comp_apply]
  lia

/-- Southeast truncation removes the first column of each skew boundary. -/
@[simp] theorem elementaryMatrix_submatrix_succ {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (h k : Fin (n + 1) → ℕ) :
    (elementaryMatrix s a h k).submatrix Fin.succ Fin.succ =
      elementaryMatrix s a (h ∘ Fin.succ) (k ∘ Fin.succ) := by
  ext i j
  simp [elementaryMatrix]

/-- The active-coordinate matrix has the same southeast truncation rule. -/
@[simp] theorem activeMatrix_columnIndex_submatrix_succ {n : ℕ}
    (h k : Fin (n + 1) → ℕ) (r : ℤ) :
    (activeMatrix (fun i => (columnIndex h i : ℤ))
      (fun j => (columnIndex k j : ℤ)) r).submatrix Fin.succ Fin.succ =
    activeMatrix (fun i => (columnIndex (h ∘ Fin.succ) i : ℤ))
      (fun j => (columnIndex (k ∘ Fin.succ) j : ℤ)) r := by
  ext i j
  simp [activeMatrix]

/-- Even active-position parity identifies the skew specialization with a TN pencil. -/
theorem elementarySubstitution_eq_checkerboardPencil {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (h k : Fin n → ℕ) (r : ℤ)
    (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r →
      Even (i.val + j.val)) :
    elementarySubstitution s a h k r = checkerboardPencil (elementaryMatrix s a h k)
      (activeMatrix (fun i => (columnIndex h i : ℤ))
        (fun j => (columnIndex k j : ℤ)) r) := by
  simp only [checkerboardPencil, activeMatrix_checkerboard hpar, elementarySubstitution]

/-- Removing the first column of both skew boundaries preserves active-position parity. -/
theorem even_active_succ {n : ℕ} {h k : Fin (n + 1) → ℕ} {r : ℤ}
    (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r →
      Even (i.val + j.val)) :
    ∀ i j, (columnIndex (h ∘ Fin.succ) i : ℤ) = columnIndex (k ∘ Fin.succ) j + r →
      Even (i.val + j.val) := by
  intro i j hij
  have hp := hpar i.succ j.succ (by simpa only [columnIndex_succ] using hij)
  rcases hp with ⟨m, hm⟩
  refine ⟨m - 1, ?_⟩
  simp only [Fin.val_succ] at hm
  lia

/-- Consecutive suffixes of parity-compatible skew shapes interlace. The alphabet
hypothesis supplies both positive constant determinants; no matrix hypotheses remain. -/
theorem strictInterl_elementarySubstitution_succ {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {h k : Fin (n + 1) → ℕ} (hh : Antitone h) (hk : Antitone k)
    (hkh : ∀ i, k i ≤ h i)
    (hsize : ∀ i, h i ≤ k i + (s.filter fun j => 0 < a j).card)
    (r : ℤ) (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r →
      Even (i.val + j.val)) :
    StrictInterl (elementarySubstitution s a (h ∘ Fin.succ) (k ∘ Fin.succ) r)
      (elementarySubstitution s a h k r) := by
  have hhs := hh.comp_monotone Fin.strictMono_succ.monotone
  have hks := hk.comp_monotone Fin.strictMono_succ.monotone
  rw [elementarySubstitution_eq_checkerboardPencil s a h k r hpar,
    elementarySubstitution_eq_checkerboardPencil s a _ _ r (even_active_succ hpar)]
  have hM := elementaryMatrix_isTotallyNonneg s a ha hh hk
  have hV := activeMatrix_isTotallyNonneg
    (fun i j hij => Int.ofNat_lt.mpr (columnIndex_strictAnti hh hij))
    (fun i j hij => Int.ofNat_lt.mpr (columnIndex_strictAnti hk hij)) r
  have hdet := det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize
  have hminor := det_elementaryMatrix_pos_of_nonneg s a ha hhs hks
    (fun i => hkh i.succ) (fun i => hsize i.succ)
  simpa only [elementaryMatrix_submatrix_succ, activeMatrix_columnIndex_submatrix_succ] using
    hM.strictInterl_checkerboardPencil_succ hV hdet
      (by simpa only [elementaryMatrix_submatrix_succ] using hminor)

end RealRooted.Schur
