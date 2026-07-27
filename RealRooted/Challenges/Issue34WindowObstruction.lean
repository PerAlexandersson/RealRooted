import RealRooted.HurwitzMatrix

/-!
# Issue #34 window-minor obstruction

This file records a small structural obstruction from an Aristotle #34 run.
The full Hurwitz Schur-product target is special to Hurwitz matrices: the
corresponding statement for arbitrary totally nonnegative `3` by `3` windows is
false.  Thus a proof of the issue #34 two-matrix target must use the Hurwitz
staircase or Toeplitz relations between neighbouring entries, not only total
nonnegativity of the selected windows.
-/

namespace RealRooted.Issue34WindowObstruction

/-- A `StrictMono` map `Fin n → Fin 3` forces `n ≤ 3`. -/
theorem strictMono_fin_three_le {n : ℕ} {f : Fin n → Fin 3} (hf : StrictMono f) :
    n ≤ 3 := by
  simpa using Fintype.card_le_of_injective f hf.injective

/-- A `StrictMono` self-map of `Fin 3` is the identity, pointwise. -/
theorem strictMono_fin_three_eq {rows : Fin 3 → Fin 3} (h : StrictMono rows) :
    rows 0 = 0 ∧ rows 1 = 1 ∧ rows 2 = 2 := by
  have := Fin.lt_def.mp (h (show (0 : Fin 3) < 1 by simp))
  have := Fin.lt_def.mp (h (show (1 : Fin 3) < 2 by simp))
  grind

/-- First witness matrix. -/
def aMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 0; 1, 1, 1; 1, 1, 1]

/-- Second witness matrix. -/
def bMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 1, 1; 2, 2, 3; 0, 1, 2]

/-- The first witness matrix is totally nonnegative. -/
theorem aMat_isTotallyNonneg : aMat.IsTotallyNonneg := fun n rows cols hrows hcols => by
  have hn : n ≤ 3 := strictMono_fin_three_le hrows
  interval_cases n <;> norm_num [Matrix.det_fin_two, Matrix.det_fin_three]
  · fin_cases rows <;> fin_cases cols <;> simp [aMat, Multiset.Pi.cons]
  · unfold aMat
    fin_cases rows <;> fin_cases cols <;>
      norm_num [Multiset.Pi.cons] at hrows hcols ⊢ <;>
      revert hrows hcols <;> decide
  · obtain ⟨r0, r1, r2⟩ := strictMono_fin_three_eq hrows
    obtain ⟨c0, c1, c2⟩ := strictMono_fin_three_eq hcols
    simp [r0, r1, r2, c0, c1, c2, aMat]

/-- The second witness matrix is totally nonnegative. -/
theorem bMat_isTotallyNonneg : bMat.IsTotallyNonneg := fun n rows cols hrows hcols => by
  have hn : n ≤ 3 := strictMono_fin_three_le hrows
  interval_cases n <;> norm_num [Matrix.det_fin_two, Matrix.det_fin_three]
  · fin_cases rows <;> fin_cases cols <;> simp [bMat, Multiset.Pi.cons]
  · fin_cases rows <;> fin_cases cols <;>
      norm_num [bMat, Multiset.Pi.cons] at hrows hcols ⊢ <;>
      revert hrows hcols <;> decide
  · obtain ⟨r0, r1, r2⟩ := strictMono_fin_three_eq hrows
    obtain ⟨c0, c1, c2⟩ := strictMono_fin_three_eq hcols
    simp [r0, r1, r2, c0, c1, c2, bMat] ; norm_num

/-- The Hadamard product of the two witness matrices has determinant `-2`. -/
theorem hadamard_det_eq :
    (Matrix.of fun i j => aMat i j * bMat i j).det = -2 := by
  simp [Matrix.det_fin_three, aMat, bMat]
  norm_num

/-- Totally nonnegative `3` by `3` matrices need not have a totally
nonnegative Hadamard product. -/
theorem exists_totallyNonneg_hadamard_det_neg :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℝ,
      a.IsTotallyNonneg ∧ b.IsTotallyNonneg ∧
        (Matrix.of fun i j => a i j * b i j).det < 0 := by
  exact ⟨aMat, bMat, aMat_isTotallyNonneg, bMat_isTotallyNonneg,
    by norm_num [hadamard_det_eq]⟩

/-- The corner-zeroed Hadamard determinant shape used in the issue #34
full-band target. -/
def hadamardCornerZeroedDet (a b : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (a 0 0 * b 0 0) *
      ((a 1 1 * b 1 1) * (a 2 2 * b 2 2) - (a 1 2 * b 1 2) * (a 2 1 * b 2 1)) -
    (a 0 1 * b 0 1) *
      ((a 1 0 * b 1 0) * (a 2 2 * b 2 2) - (a 1 2 * b 1 2) * (a 2 0 * b 2 0))

/-- The corner-zeroed Hadamard determinant of the witnesses is `-2`. -/
theorem hadamardCornerZeroedDet_eq : hadamardCornerZeroedDet aMat bMat = -2 := by
  simp [hadamardCornerZeroedDet, aMat, bMat]
  norm_num

/-- Even the corner-zeroed target cannot be proved from the selected window
minors alone. -/
theorem exists_totallyNonneg_hadamardCornerZeroed_neg :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℝ,
      a.IsTotallyNonneg ∧ b.IsTotallyNonneg ∧ hadamardCornerZeroedDet a b < 0 := by
  exact ⟨aMat, bMat, aMat_isTotallyNonneg, bMat_isTotallyNonneg,
    by norm_num [hadamardCornerZeroedDet_eq]⟩

end RealRooted.Issue34WindowObstruction
