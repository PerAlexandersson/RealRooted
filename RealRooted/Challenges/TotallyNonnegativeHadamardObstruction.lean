module

public import RealRooted.HurwitzMatrix

/-!
# Totally nonnegative windows do not give the Hurwitz Schur product

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "totally-nonnegative-hadamard-obstruction"
formalized = "2026-09-30"
references = [
  "Wagner1992",
]

[[theorems]]
name = "RealRooted.TotallyNonnegativeHadamardObstruction.exists_totallyNonneg_hadamard_det_neg"
label = "The Hadamard product of two 3 × 3 TNN matrices can have negative determinant"
headline = true

[[theorems]]
name = """RealRooted.TotallyNonnegativeHadamardObstruction.\
exists_totallyNonneg_hadamardCornerZeroed_neg"""
label = "A corner-zeroed Hadamard determinant can be negative"
-->

<!-- realrooted-catalog-content -->
# Hadamard products of totally nonnegative matrices

The Hadamard product multiplies two matrices entry by entry. We give two
totally nonnegative $3 \times 3$ matrices whose Hadamard product has determinant
$-2$. Thus entrywise multiplication does not preserve total nonnegativity,
even in size three. The same witnesses also make the corner-zeroed determinant
used by the Hurwitz-matrix calculation negative.

For infinite Hurwitz matrices, the corresponding Schur-product assertion also
fails; see `RealRooted.not_hurwitz_schurProduct_det_fin_three_nonneg`.

## References

See [@Wagner1992] and the
[Hadamard product on symmetricfunctions.com](sf:hadamardProductDefinition).
<!-- /realrooted-catalog-content -->
-/

@[expose] public section

namespace RealRooted.TotallyNonnegativeHadamardObstruction

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
def hadamardCounterexampleLeft : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 0; 1, 1, 1; 1, 1, 1]

/-- Second witness matrix. -/
def hadamardCounterexampleRight : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 1, 1; 2, 2, 3; 0, 1, 2]

/-- The first witness matrix is totally nonnegative. -/
theorem hadamardCounterexampleLeft_isTotallyNonneg :
    hadamardCounterexampleLeft.IsTotallyNonneg := fun n rows cols hrows hcols => by
  change 0 ≤ (hadamardCounterexampleLeft.submatrix rows cols).det
  have hn : n ≤ 3 := strictMono_fin_three_le hrows
  interval_cases n
  · norm_num
  · erw [Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply]
    generalize rows 0 = r0, cols 0 = c0
    fin_cases r0 <;> fin_cases c0 <;> norm_num [hadamardCounterexampleLeft]
  · erw [Matrix.det_fin_two]
    have hr := hrows (show (0 : Fin 2) < 1 by decide)
    have hc := hcols (show (0 : Fin 2) < 1 by decide)
    simp only [Matrix.submatrix_apply]
    generalize rows 0 = r0, rows 1 = r1 at hr ⊢
    generalize cols 0 = c0, cols 1 = c1 at hc ⊢
    fin_cases r0 <;> fin_cases r1 <;> fin_cases c0 <;> fin_cases c1 <;>
      (revert hr hc; norm_num [hadamardCounterexampleLeft])
  · obtain ⟨r0, r1, r2⟩ := strictMono_fin_three_eq hrows
    obtain ⟨c0, c1, c2⟩ := strictMono_fin_three_eq hcols
    erw [Matrix.det_fin_three]
    simp [r0, r1, r2, c0, c1, c2, hadamardCounterexampleLeft]

/-- The second witness matrix is totally nonnegative. -/
theorem hadamardCounterexampleRight_isTotallyNonneg :
    hadamardCounterexampleRight.IsTotallyNonneg := fun n rows cols hrows hcols => by
  change 0 ≤ (hadamardCounterexampleRight.submatrix rows cols).det
  have hn : n ≤ 3 := strictMono_fin_three_le hrows
  interval_cases n
  · norm_num
  · erw [Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply]
    generalize rows 0 = r0, cols 0 = c0
    fin_cases r0 <;> fin_cases c0 <;> norm_num [hadamardCounterexampleRight]
  · erw [Matrix.det_fin_two]
    have hr := hrows (show (0 : Fin 2) < 1 by decide)
    have hc := hcols (show (0 : Fin 2) < 1 by decide)
    simp only [Matrix.submatrix_apply]
    generalize rows 0 = r0, rows 1 = r1 at hr ⊢
    generalize cols 0 = c0, cols 1 = c1 at hc ⊢
    fin_cases r0 <;> fin_cases r1 <;> fin_cases c0 <;> fin_cases c1 <;>
      (revert hr hc; norm_num [hadamardCounterexampleRight])
  · obtain ⟨r0, r1, r2⟩ := strictMono_fin_three_eq hrows
    obtain ⟨c0, c1, c2⟩ := strictMono_fin_three_eq hcols
    erw [Matrix.det_fin_three]
    simp [r0, r1, r2, c0, c1, c2, hadamardCounterexampleRight]; norm_num

/-- The Hadamard product of the two witness matrices has determinant `-2`. -/
theorem hadamard_det_eq :
    (Matrix.of fun i j =>
      hadamardCounterexampleLeft i j * hadamardCounterexampleRight i j).det = -2 := by
  simp [Matrix.det_fin_three, hadamardCounterexampleLeft, hadamardCounterexampleRight]
  norm_num

/-- Totally nonnegative `3` by `3` matrices need not have a totally
nonnegative Hadamard product. -/
theorem exists_totallyNonneg_hadamard_det_neg :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℝ,
      a.IsTotallyNonneg ∧ b.IsTotallyNonneg ∧
        (Matrix.of fun i j => a i j * b i j).det < 0 :=
  ⟨hadamardCounterexampleLeft, hadamardCounterexampleRight,
    hadamardCounterexampleLeft_isTotallyNonneg,
    hadamardCounterexampleRight_isTotallyNonneg,
    by norm_num [hadamard_det_eq]⟩

/-- The `3 × 3` Hadamard determinant with the top-right corner contribution
deleted. -/
def hadamardCornerZeroedDet (a b : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (a 0 0 * b 0 0) *
      ((a 1 1 * b 1 1) * (a 2 2 * b 2 2) - (a 1 2 * b 1 2) * (a 2 1 * b 2 1)) -
    (a 0 1 * b 0 1) *
      ((a 1 0 * b 1 0) * (a 2 2 * b 2 2) - (a 1 2 * b 1 2) * (a 2 0 * b 2 0))

/-- The corner-zeroed Hadamard determinant of the witnesses is `-2`. -/
theorem hadamardCornerZeroedDet_eq :
    hadamardCornerZeroedDet hadamardCounterexampleLeft hadamardCounterexampleRight = -2 := by
  simp [hadamardCornerZeroedDet, hadamardCounterexampleLeft, hadamardCounterexampleRight]
  norm_num

/-- Even the corner-zeroed Hadamard determinant can be negative for totally
nonnegative windows. -/
theorem exists_totallyNonneg_hadamardCornerZeroed_neg :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℝ,
      a.IsTotallyNonneg ∧ b.IsTotallyNonneg ∧ hadamardCornerZeroedDet a b < 0 :=
  ⟨hadamardCounterexampleLeft, hadamardCounterexampleRight,
    hadamardCounterexampleLeft_isTotallyNonneg,
    hadamardCounterexampleRight_isTotallyNonneg,
    by norm_num [hadamardCornerZeroedDet_eq]⟩

end RealRooted.TotallyNonnegativeHadamardObstruction
