import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Border
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# A standard-basis source border for totally nonnegative matrices

We prepend the first standard-basis column to a finite square matrix and prove
rectangular total nonnegativity.  A second construction adjoins a scalar first
row, producing the source-step matrix used in bordered chain recurrences.
-/

namespace Matrix

/-- The product of two matrices which vanish strictly above the diagonal also
vanishes strictly above the diagonal. -/
theorem mul_apply_eq_zero_of_lt_of_upper_zero
    {R ι : Type*} [Semiring R] [Fintype ι] [LinearOrder ι]
    (A B : Matrix ι ι R)
    (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0)
    {i j : ι} (hij : i < j) :
    (A * B) i j = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (lt_of_le_of_lt (le_of_not_gt hik) hij), mul_zero]

/-- On the diagonal, the product of two matrices which vanish strictly above
the diagonal is the product of their diagonal entries. -/
theorem mul_apply_self_of_upper_zero
    {R ι : Type*} [Semiring R] [Fintype ι] [LinearOrder ι]
    (A B : Matrix ι ι R)
    (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : ι) :
    (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hki | hik
    · rw [hB k i hki, mul_zero]
    · rw [hA i k hik, zero_mul]
  · simp

/-- Prepend the first standard-basis column to a nonempty square matrix. -/
def prependFirstBasisColumn {R : Type*} [Zero R] [One R] {N : ℕ}
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 1)) (Fin (N + 2)) R :=
  fun i => Fin.cases (if i = 0 then 1 else 0) (H i)

@[simp]
theorem prependFirstBasisColumn_zero {R : Type*} [Zero R] [One R] {N : ℕ}
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (i : Fin (N + 1)) :
    prependFirstBasisColumn H i 0 = if i = 0 then 1 else 0 :=
  rfl

@[simp]
theorem prependFirstBasisColumn_succ {R : Type*} [Zero R] [One R] {N : ℕ}
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i j : Fin (N + 1)) :
    prependFirstBasisColumn H i j.succ = H i j :=
  rfl

/-- Prepending the first standard-basis column preserves rectangular total
nonnegativity. -/
protected theorem IsTotallyNonneg.prependFirstBasisColumn
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hH : H.IsTotallyNonneg) :
    (prependFirstBasisColumn H).IsTotallyNonnegRect := by
  intro q rows cols hrows hcols
  cases q with
  | zero => simp
  | succ q =>
      by_cases hc0 : cols 0 = 0
      · by_cases hr0 : rows 0 = 0
        · have hcols_tail_ne : ∀ j : Fin q, cols j.succ ≠ 0 := by
            intro j hj
            have hlt := hcols (by simp : (0 : Fin (q + 1)) < j.succ)
            simp [hc0, hj] at hlt
          have hrows_tail_ne : ∀ i : Fin q, rows i.succ ≠ 0 := by
            intro i hi
            have hlt := hrows (by simp : (0 : Fin (q + 1)) < i.succ)
            simp [hr0, hi] at hlt
          let rows' : Fin q → Fin (N + 1) := fun i => rows i.succ
          let cols' : Fin q → Fin (N + 1) := fun j =>
            (cols j.succ).pred (hcols_tail_ne j)
          have hrows' : StrictMono rows' := by
            intro i j hij
            exact hrows (Fin.succ_lt_succ_iff.mpr hij)
          have hcols' : StrictMono cols' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr
              (hcols (Fin.succ_lt_succ_iff.mpr hij))
          let M := (prependFirstBasisColumn H).submatrix rows cols
          have hcolM : ∀ i : Fin q, M i.succ 0 = 0 := by
            intro i
            simp [M, hc0, hrows_tail_ne i]
          have hfactor : M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det := by
            rw [det_succ_column_zero, Fin.sum_univ_succ]
            have htail : ∑ i : Fin q,
                (-1 : R) ^ ((i.succ : Fin (q + 1)) : ℕ) * M i.succ 0 *
                  (M.submatrix i.succ.succAbove Fin.succ).det = 0 := by
              apply Finset.sum_eq_zero
              intro i _
              rw [hcolM i]
              simp
            rw [htail]
            simp
          have htail : M.submatrix Fin.succ Fin.succ =
              H.submatrix rows' cols' := by
            ext i j
            change prependFirstBasisColumn H (rows i.succ) (cols j.succ) =
              H (rows' i) (cols' j)
            have hj : (cols' j).succ = cols j.succ := by simp [cols']
            rw [← hj]
            simp [rows']
          rw [show ((prependFirstBasisColumn H).submatrix rows cols).det = M.det from rfl]
          rw [hfactor, htail]
          simpa [M, hr0, hc0] using hH hrows' hcols'
        · have hrows_ne_zero : ∀ i : Fin (q + 1), rows i ≠ 0 := by
            intro i hi
            apply hr0
            apply Fin.le_zero_iff.mp
            simpa [hi] using hrows.monotone (Fin.zero_le i)
          have hminor_col : ∀ i : Fin (q + 1),
              ((prependFirstBasisColumn H).submatrix rows cols) i 0 = 0 := by
            intro i
            simp [hc0, hrows_ne_zero i]
          rw [det_eq_zero_of_column_eq_zero (0 : Fin (q + 1)) hminor_col]
      · have hcols_ne_zero : ∀ j : Fin (q + 1), cols j ≠ 0 := by
          intro j hj
          apply hc0
          apply Fin.le_zero_iff.mp
          simpa [hj] using hcols.monotone (Fin.zero_le j)
        let cols' : Fin (q + 1) → Fin (N + 1) := fun j =>
          (cols j).pred (hcols_ne_zero j)
        have hcols' : StrictMono cols' := by
          intro i j hij
          exact Fin.pred_lt_pred_iff.mpr (hcols hij)
        have heq : (prependFirstBasisColumn H).submatrix rows cols =
            H.submatrix rows cols' := by
          ext i j
          change prependFirstBasisColumn H (rows i) (cols j) =
            H (rows i) (cols' j)
          have hj : (cols' j).succ = cols j := by simp [cols']
          rw [← hj]
          rfl
        rw [heq]
        exact hH hrows hcols'

/-- Adjoin a scalar first row above a matrix with a prepended first
standard-basis column. -/
def sourceStep {R : Type*} [Zero R] [One R] {N : ℕ} (δ : R)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) R :=
  Fin.cases (Fin.cases δ fun _ => 0) (prependFirstBasisColumn H)

@[simp]
theorem sourceStep_zero_zero {R : Type*} [Zero R] [One R] {N : ℕ} (δ : R)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    sourceStep δ H 0 0 = δ :=
  rfl

@[simp]
theorem sourceStep_zero_succ {R : Type*} [Zero R] [One R] {N : ℕ} (δ : R)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (j : Fin (N + 1)) :
    sourceStep δ H 0 j.succ = 0 :=
  rfl

@[simp]
theorem sourceStep_succ_zero {R : Type*} [Zero R] [One R] {N : ℕ} (δ : R)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (i : Fin (N + 1)) :
    sourceStep δ H i.succ 0 = if i = 0 then 1 else 0 :=
  rfl

@[simp]
theorem sourceStep_succ_succ {R : Type*} [Zero R] [One R] {N : ℕ} (δ : R)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (i j : Fin (N + 1)) :
    sourceStep δ H i.succ j.succ = H i j :=
  rfl

/-- Adjoin an isolated first coordinate with value one to a square matrix. -/
def isolateFirstCoordinate {R : Type*} [Zero R] [One R] {N : ℕ}
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) R :=
  Fin.cases (Fin.cases 1 fun _ => 0)
    (fun i => Fin.cases 0 (G i))

@[simp]
theorem isolateFirstCoordinate_zero_zero {R : Type*} [Zero R] [One R]
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    isolateFirstCoordinate G 0 0 = 1 :=
  rfl

@[simp]
theorem isolateFirstCoordinate_zero_succ {R : Type*} [Zero R] [One R]
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (j : Fin (N + 1)) :
    isolateFirstCoordinate G 0 j.succ = 0 :=
  rfl

@[simp]
theorem isolateFirstCoordinate_succ_zero {R : Type*} [Zero R] [One R]
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    isolateFirstCoordinate G i.succ 0 = 0 :=
  rfl

@[simp]
theorem isolateFirstCoordinate_succ_succ {R : Type*} [Zero R] [One R]
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i j : Fin (N + 1)) :
    isolateFirstCoordinate G i.succ j.succ = G i j :=
  rfl

/-- Isolating a first coordinate with value one preserves total
nonnegativity. -/
protected theorem IsTotallyNonneg.isolateFirstCoordinate
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} {G : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hG : G.IsTotallyNonneg) :
    (isolateFirstCoordinate G).IsTotallyNonneg := by
  apply IsTotallyNonneg.of_zero_border (isolateFirstCoordinate G)
  · intro j
    rfl
  · intro i
    rfl
  · simp
  · have htrail :
        (isolateFirstCoordinate G).submatrix Fin.succ Fin.succ = G := by
      ext i j
      rfl
    rw [htrail]
    exact hG

/-- A nonnegative scalar source step over a nonempty totally nonnegative
matrix is totally nonnegative. -/
protected theorem IsTotallyNonneg.sourceStep
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hH : H.IsTotallyNonneg) {δ : R} (hδ : 0 ≤ δ) :
    (sourceStep δ H).IsTotallyNonneg := by
  intro q rows cols hrows hcols
  cases q with
  | zero => simp
  | succ q =>
      have hrow : ∀ j : Fin (N + 1), sourceStep δ H 0 j.succ = 0 := by
        intro j
        rfl
      have htrail : (sourceStep δ H).submatrix Fin.succ Fin.succ = H := by
        ext i j
        rfl
      by_cases hc0 : cols 0 = 0
      · by_cases hr0 : rows 0 = 0
        · have hrows_tail_ne : ∀ i : Fin q, rows i.succ ≠ 0 := by
            intro i hi
            have hlt := hrows (by simp : (0 : Fin (q + 1)) < i.succ)
            simp [hr0, hi] at hlt
          have hcols_tail_ne : ∀ j : Fin q, cols j.succ ≠ 0 := by
            intro j hj
            have hlt := hcols (by simp : (0 : Fin (q + 1)) < j.succ)
            simp [hc0, hj] at hlt
          let rows' : Fin q → Fin (N + 1) := fun i =>
            (rows i.succ).pred (hrows_tail_ne i)
          let cols' : Fin q → Fin (N + 1) := fun j =>
            (cols j.succ).pred (hcols_tail_ne j)
          have hrows' : StrictMono rows' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr
              (hrows (Fin.succ_lt_succ_iff.mpr hij))
          have hcols' : StrictMono cols' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr
              (hcols (Fin.succ_lt_succ_iff.mpr hij))
          have hrows_eq :
              (Fin.cases 0 fun i => (rows' i).succ) = rows := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact hr0.symm
            · simp [rows']
          have hcols_eq :
              (Fin.cases 0 fun j => (cols' j).succ) = cols := by
            funext j
            refine Fin.cases ?_ (fun k => ?_) j
            · exact hc0.symm
            · simp [cols']
          rw [← hrows_eq, ← hcols_eq]
          exact nonneg_of_isTotallyNonneg_trailing_zero_zero
            (sourceStep δ H) rows' cols' hrow hδ (htrail ▸ hH) hrows' hcols'
        · have hrows_ne_zero : ∀ i : Fin (q + 1), rows i ≠ 0 := by
            intro i hi
            apply hr0
            apply Fin.le_zero_iff.mp
            simpa [hi] using hrows.monotone (Fin.zero_le i)
          let rows' : Fin (q + 1) → Fin (N + 1) := fun i =>
            (rows i).pred (hrows_ne_zero i)
          have hrows' : StrictMono rows' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr (hrows hij)
          have heq : (sourceStep δ H).submatrix rows cols =
              (prependFirstBasisColumn H).submatrix rows' cols := by
            ext i j
            change sourceStep δ H (rows i) (cols j) =
              prependFirstBasisColumn H (rows' i) (cols j)
            have hi : (rows' i).succ = rows i := by simp [rows']
            rw [← hi]
            rfl
          rw [heq]
          exact hH.prependFirstBasisColumn hrows' hcols
      · have hcols_ne_zero : ∀ j : Fin (q + 1), cols j ≠ 0 := by
          intro j hj
          apply hc0
          apply Fin.le_zero_iff.mp
          simpa [hj] using hcols.monotone (Fin.zero_le j)
        let cols' : Fin (q + 1) → Fin (N + 1) := fun j =>
          (cols j).pred (hcols_ne_zero j)
        have hcols' : StrictMono cols' := by
          intro i j hij
          exact Fin.pred_lt_pred_iff.mpr (hcols hij)
        have hcols_eq : (fun j => (cols' j).succ) = cols := by
          funext j
          simp [cols']
        rw [← hcols_eq]
        exact nonneg_of_isTotallyNonneg_trailing
          (sourceStep δ H) hrow (htrail ▸ hH) rows cols' hrows hcols'

end Matrix
