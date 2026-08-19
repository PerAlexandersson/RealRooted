import RealRooted.AissenSchoenbergWhitneyBase
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Toeplitz matrix in Karlin's finite-order sector theorem

Karlin's proof of the finite-order zero-free sector theorem repeats an
`order × (degree + order)` Toeplitz coefficient window `blocks` times, with
successive windows overlapping in one column.  The resulting rectangular
matrix is itself an ordered submatrix of the transpose of the infinite
Toeplitz matrix.  This file records that identification and obtains total
nonnegativity directly from the Pólya-frequency hypothesis.

Reference: S. Karlin, *Total Positivity*, Vol. I, Chapter 8, Theorem 3.1.
-/

open Matrix

namespace RealRooted

/-- Global Toeplitz row occupied by row `j` in Karlin's repeated coefficient
window.  Each new block skips `degree - 1` additional global rows. -/
def aswKarlinRowPos (degree order j : ℕ) : ℕ :=
  j + (j / order) * (degree - 1)

lemma strictMono_aswKarlinRowPos (degree order : ℕ) :
    StrictMono (aswKarlinRowPos degree order) := by
  intro i j hij
  exact Nat.add_lt_add_of_lt_of_le hij
    (Nat.mul_le_mul_right (degree - 1) (Nat.div_le_div_right hij.le))

/-- Karlin's repeated overlapping coefficient-window matrix.  It has
`blocks * order` rows and `blocks * (degree + order - 1) + 1` columns. -/
def aswKarlinMatrix (u : ℕ → ℝ) (degree order blocks : ℕ) :
    Matrix (Fin (blocks * order)) (Fin (blocks * (degree + order - 1) + 1)) ℝ :=
  fun i j => toeplitz u (j : ℕ) (aswKarlinRowPos degree order i)

@[simp]
lemma aswKarlinMatrix_apply (u : ℕ → ℝ) (degree order blocks : ℕ)
    (i : Fin (blocks * order)) (j : Fin (blocks * (degree + order - 1) + 1)) :
    aswKarlinMatrix u degree order blocks i j =
      if aswKarlinRowPos degree order i ≤ (j : ℕ) then
        u ((j : ℕ) - aswKarlinRowPos degree order i)
      else 0 :=
  rfl

/-- The repeated coefficient-window matrix is the transpose of an ordered
rectangular submatrix of the infinite Toeplitz matrix. -/
lemma aswKarlinMatrix_eq_transpose_submatrix (u : ℕ → ℝ)
    (degree order blocks : ℕ) :
    aswKarlinMatrix u degree order blocks =
      ((toeplitz u).submatrix
        (fun j : Fin (blocks * (degree + order - 1) + 1) => (j : ℕ))
        (fun i : Fin (blocks * order) => aswKarlinRowPos degree order i)).transpose :=
  rfl

/-- Full Pólya-frequency total nonnegativity supplies total nonnegativity of
every Karlin repeated coefficient-window matrix. -/
theorem IsPolyaFreqSeq.aswKarlinMatrix_isTotallyNonnegRect
    {u : ℕ → ℝ} (hpf : IsPolyaFreqSeq u) (degree order blocks : ℕ) :
    (aswKarlinMatrix u degree order blocks).IsTotallyNonnegRect := by
  rw [aswKarlinMatrix_eq_transpose_submatrix]
  exact (hpf.toRect.submatrix Fin.val_strictMono
    ((strictMono_aswKarlinRowPos degree order).comp Fin.val_strictMono)).transpose

/-- The square minor obtained by selecting the global Toeplitz row positions
as columns in Karlin's rectangular matrix. -/
def aswKarlinPivotMatrix (u : ℕ → ℝ) (degree order blocks : ℕ) :
    Matrix (Fin (blocks * order)) (Fin (blocks * order)) ℝ :=
  fun i j => toeplitz u (aswKarlinRowPos degree order j)
    (aswKarlinRowPos degree order i)

lemma aswKarlinPivotMatrix_blockTriangular (u : ℕ → ℝ)
    (degree order blocks : ℕ) :
    (aswKarlinPivotMatrix u degree order blocks).BlockTriangular id := by
  intro i j hji
  change (j : ℕ) < (i : ℕ) at hji
  have hpos : aswKarlinRowPos degree order j < aswKarlinRowPos degree order i :=
    strictMono_aswKarlinRowPos degree order hji
  simp [aswKarlinPivotMatrix, toeplitz_apply, Nat.not_le_of_lt hpos]

/-- Karlin's selected square minor is upper triangular with constant diagonal
`u 0`. -/
theorem det_aswKarlinPivotMatrix (u : ℕ → ℝ) (degree order blocks : ℕ) :
    (aswKarlinPivotMatrix u degree order blocks).det = u 0 ^ (blocks * order) := by
  rw [Matrix.det_of_upperTriangular
    (aswKarlinPivotMatrix_blockTriangular u degree order blocks)]
  simp [aswKarlinPivotMatrix, toeplitz_apply]

theorem det_aswKarlinPivotMatrix_pos {u : ℕ → ℝ} (degree order blocks : ℕ)
    (hconst : 0 < u 0) :
    0 < (aswKarlinPivotMatrix u degree order blocks).det := by
  rw [det_aswKarlinPivotMatrix]
  exact pow_pos hconst _

lemma aswKarlinRowPos_lt (degree order blocks : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) (i : Fin (blocks * order)) :
    aswKarlinRowPos degree order i < blocks * (degree + order - 1) + 1 := by
  have hdiv : (i : ℕ) / order < blocks :=
    (Nat.div_lt_iff_lt_mul horder).2 i.isLt
  have hinner : order + (degree - 1) = degree + order - 1 := by lia
  calc
    aswKarlinRowPos degree order i <
        blocks * order + blocks * (degree - 1) :=
      Nat.add_lt_add_of_lt_of_le i.isLt
        (Nat.mul_le_mul_right (degree - 1) hdiv.le)
    _ = blocks * (order + (degree - 1)) := (Nat.mul_add _ _ _).symm
    _ = blocks * (degree + order - 1) := by rw [hinner]
    _ < blocks * (degree + order - 1) + 1 := Nat.lt_succ_self _

/-- Every coefficient window in the repeated Karlin matrix ends within its
finite column range. -/
lemma aswKarlinRowPos_add_degree_le (degree order blocks : ℕ)
    (hdegree : 0 < degree) (horder : 0 < order)
    (i : Fin (blocks * order)) :
    aswKarlinRowPos degree order i + degree ≤
      blocks * (degree + order - 1) := by
  have hdiv : (i : ℕ) / order < blocks :=
    (Nat.div_lt_iff_lt_mul horder).2 i.isLt
  have hmod : (i : ℕ) % order < order := Nat.mod_lt _ horder
  have hinner : degree + order - 1 = order + (degree - 1) := by lia
  have hpos : aswKarlinRowPos degree order i =
      ((i : ℕ) / order) * (degree + order - 1) + (i : ℕ) % order := by
    rw [hinner]
    unfold aswKarlinRowPos
    conv_lhs =>
      lhs
      rw [← Nat.div_add_mod (i : ℕ) order]
    ring
  rw [hpos]
  calc
    (i : ℕ) / order * (degree + order - 1) + (i : ℕ) % order + degree ≤
        (i : ℕ) / order * (degree + order - 1) +
          (degree + order - 1) := by
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left (by lia) _
    _ = ((i : ℕ) / order + 1) * (degree + order - 1) := by ring
    _ ≤ blocks * (degree + order - 1) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdiv)

/-- The finite-column embedding of the Toeplitz row positions used by the
pivot minor. -/
def aswKarlinSelectedCol (degree order blocks : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) (i : Fin (blocks * order)) :
    Fin (blocks * (degree + order - 1) + 1) :=
  ⟨aswKarlinRowPos degree order i,
    aswKarlinRowPos_lt degree order blocks hdegree horder i⟩

@[simp]
lemma aswKarlinSelectedCol_val (degree order blocks : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) (i : Fin (blocks * order)) :
    (aswKarlinSelectedCol degree order blocks hdegree horder i : ℕ) =
      aswKarlinRowPos degree order i :=
  rfl

lemma aswKarlinMatrix_submatrix_selected (u : ℕ → ℝ) (degree order blocks : ℕ)
    (hdegree : 0 < degree) (horder : 0 < order) :
    (aswKarlinMatrix u degree order blocks).submatrix id
        (aswKarlinSelectedCol degree order blocks hdegree horder) =
      aswKarlinPivotMatrix u degree order blocks :=
  rfl

/-- Extend a vector on the selected pivot columns by zero and add values when
selected columns coincide.  In the Karlin application the selected columns
are distinct, but the multiplication identity below does not need that fact. -/
def aswKarlinExtend (degree order blocks : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) (w : Fin (blocks * order) → ℝ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  ∑ i, Pi.single (aswKarlinSelectedCol degree order blocks hdegree horder i) (w i)

lemma aswKarlinMatrix_mulVec_extend (u : ℕ → ℝ) (degree order blocks : ℕ)
    (hdegree : 0 < degree) (horder : 0 < order)
    (w : Fin (blocks * order) → ℝ) :
    aswKarlinMatrix u degree order blocks *ᵥ
        aswKarlinExtend degree order blocks hdegree horder w =
      aswKarlinPivotMatrix u degree order blocks *ᵥ w := by
  unfold aswKarlinExtend
  rw [Matrix.mulVec_sum _ Finset.univ]
  ext i
  simp [Matrix.mulVec, dotProduct, aswKarlinPivotMatrix, mul_comm]

/-- Positive constant coefficient makes Karlin's rectangular matrix
surjective as a map from column vectors to row vectors. -/
theorem aswKarlinMatrix_mulVec_surjective {u : ℕ → ℝ}
    (degree order blocks : ℕ) (hdegree : 0 < degree) (horder : 0 < order)
    (hconst : 0 < u 0) :
    Function.Surjective (aswKarlinMatrix u degree order blocks).mulVec := by
  intro y
  have hpivot : IsUnit (aswKarlinPivotMatrix u degree order blocks) :=
    (aswKarlinPivotMatrix u degree order blocks).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr
        (det_aswKarlinPivotMatrix_pos degree order blocks hconst).ne')
  obtain ⟨w, hw⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr hpivot) y
  refine ⟨aswKarlinExtend degree order blocks hdegree horder w, ?_⟩
  rw [aswKarlinMatrix_mulVec_extend, hw]

end RealRooted
