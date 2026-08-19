import RealRooted.GeneralizedSnakePosets.SnakeReachability
import RealRooted.GeneralizedSnakePosets.SquarecaseModel

/-!
# Concrete generalized snake boards

This module contains the finite squarecase board attached to a Braun--Jal
generalized snake word, its constant-word shape checks, and the concrete
squarecase rook model built from that board.
-/

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Concrete snake boards -/

/-- The concrete finite squarecase board attached to a generalized snake word.

The cells are the cross-chain pairs that are incomparable in the generalized
snake poset `P(w)`, following the Alexandersson--Jal width-two-poset/skew-shape
correspondence used by Braun--Jal. -/
def generalizedSnakeBoard (w : SnakeWord) : FiniteSkewBoard where
  cells :=
    ((Finset.range (w.length + 1)).product (Finset.range (w.length + 1))).filter
      fun cell =>
        (!snakeElementReachable w (snakeRowCode cell.1) (snakeColCode cell.2) &&
          !snakeElementReachable w (snakeColCode cell.2) (snakeRowCode cell.1)) = true

/-- The cells of an all-`R` snake board form the upper triangular staircase in
the `(n + 1) × (n + 1)` square. -/
theorem mem_generalizedSnakeBoard_replicate_R_cells {n r c : ℕ} :
    (r, c) ∈ (generalizedSnakeBoard (List.replicate n SnakeLetter.R)).cells ↔
      r ≤ n ∧ c ≤ n ∧ r ≤ c := by
  constructor
  · intro h
    rw [generalizedSnakeBoard, Finset.mem_filter] at h
    simp only [List.length_replicate] at h
    rcases h with ⟨hbound, hcell⟩
    have hbounds : r ≤ n ∧ c ≤ n := by simpa [Finset.mem_product] using hbound
    rw [Bool.and_eq_true] at hcell
    rcases hcell with ⟨_hrow_col, hcol_row⟩
    have hrc : r ≤ c := by
      exact (snakeElementReachable_replicate_R_colCode_rowCode_eq_false_iff
        (n := n) (c := c) (r := r) hbounds.1).mp (by simpa using hcol_row)
    exact ⟨hbounds.1, hbounds.2, hrc⟩
  · rintro ⟨hr, hc, hrc⟩
    rw [generalizedSnakeBoard, Finset.mem_filter]
    simp only [List.length_replicate]
    constructor
    · simpa [Finset.mem_product] using ⟨hr, hc⟩
    · rw [Bool.and_eq_true]
      constructor
      · simp [snakeElementReachable_replicate_R_rowCode_colCode_eq_false]
      · have hfalse :=
          (snakeElementReachable_replicate_R_colCode_rowCode_eq_false_iff
            (n := n) (c := c) (r := r) hr).mpr hrc
        simp [hfalse]

/-- The cells of an all-`L` snake board form the lower triangular staircase in
the `(n + 1) × (n + 1)` square. -/
theorem mem_generalizedSnakeBoard_replicate_L_cells {n r c : ℕ} :
    (r, c) ∈ (generalizedSnakeBoard (List.replicate n SnakeLetter.L)).cells ↔
      r ≤ n ∧ c ≤ n ∧ c ≤ r := by
  constructor
  · intro h
    rw [generalizedSnakeBoard, Finset.mem_filter] at h
    simp only [List.length_replicate] at h
    rcases h with ⟨hbound, hcell⟩
    have hbounds : r ≤ n ∧ c ≤ n := by simpa [Finset.mem_product] using hbound
    rw [Bool.and_eq_true] at hcell
    rcases hcell with ⟨hrow_col, _hcol_row⟩
    have hcr : c ≤ r := by
      exact (snakeElementReachable_replicate_L_rowCode_colCode_eq_false_iff
        (n := n) (r := r) (c := c) hbounds.2).mp (by simpa using hrow_col)
    exact ⟨hbounds.1, hbounds.2, hcr⟩
  · rintro ⟨hr, hc, hcr⟩
    rw [generalizedSnakeBoard, Finset.mem_filter]
    simp only [List.length_replicate]
    constructor
    · simpa [Finset.mem_product] using ⟨hr, hc⟩
    · rw [Bool.and_eq_true]
      constructor
      · have hfalse :=
          (snakeElementReachable_replicate_L_rowCode_colCode_eq_false_iff
            (n := n) (r := r) (c := c) hc).mpr hcr
        simp [hfalse]
      · simp [snakeElementReachable_replicate_L_colCode_rowCode_eq_false]

/-- In a final `R` suffix after a last-change index, every board cell whose row
coordinate lies in the suffix has row weakly below column. -/
theorem mem_generalizedSnakeBoard_suffix_R_cells_row_le_col
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hr : r ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R)
    (hcell : (r, c) ∈ (generalizedSnakeBoard w).cells) :
    r ≤ c := by
  by_contra hnot
  have hcr : c < r := Nat.lt_of_not_ge hnot
  rw [generalizedSnakeBoard, Finset.mem_filter] at hcell
  rcases hcell with ⟨_hbound, hcell⟩
  rw [Bool.and_eq_true] at hcell
  rcases hcell with ⟨_hrow_col, hcol_row⟩
  have hreach := snakeElementReachable_suffix_R_colCode_rowCode_of_lt
    (w := w) (last := last) (c := c) (r := r) hlast hcr hr hfinal
  simp [hreach] at hcol_row

/-- In a final `R` suffix after a last-change index, the suffix-coordinate
cells are exactly the all-`R` triangular block. -/
theorem mem_generalizedSnakeBoard_suffix_R_cells_iff
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hr : r ≤ w.length - (last + 1))
    (hc : c ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R) :
    (r, c) ∈ (generalizedSnakeBoard w).cells ↔ r ≤ c := by
  constructor
  · intro hcell
    exact mem_generalizedSnakeBoard_suffix_R_cells_row_le_col
      hlast hr hfinal hcell
  · intro hrc
    rw [generalizedSnakeBoard, Finset.mem_filter]
    constructor
    · simpa [Finset.mem_product] using
        ⟨le_trans hr (Nat.sub_le _ _), le_trans hc (Nat.sub_le _ _)⟩
    · rw [Bool.and_eq_true]
      constructor
      · have hfalse := snakeElementReachable_suffix_R_rowCode_colCode_eq_false
          hlast hr hc hfinal
        simp [hfalse]
      · have hdrop : snakeRowCode r < snakeColCode c := by
          simp [snakeRowCode, snakeColCode]
          lia
        have hfalse := snakeElementReachable_eq_false_of_target_lt
          (w := w) (a := snakeColCode c) (b := snakeRowCode r) hdrop
        simp [hfalse]

/-- In a final `L` suffix after a last-change index, every board cell whose
column coordinate lies in the suffix has column weakly below row. -/
theorem mem_generalizedSnakeBoard_suffix_L_cells_col_le_row
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hc : c ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L)
    (hcell : (r, c) ∈ (generalizedSnakeBoard w).cells) :
    c ≤ r := by
  by_contra hnot
  have hrc : r < c := Nat.lt_of_not_ge hnot
  rw [generalizedSnakeBoard, Finset.mem_filter] at hcell
  rcases hcell with ⟨_hbound, hcell⟩
  rw [Bool.and_eq_true] at hcell
  rcases hcell with ⟨hrow_col, _hcol_row⟩
  have hreach := snakeElementReachable_suffix_L_rowCode_colCode_of_lt
    (w := w) (last := last) (r := r) (c := c) hlast hrc hc hfinal
  simp [hreach] at hrow_col

/-- In a final `L` suffix after a last-change index, the suffix-coordinate
cells are exactly the all-`L` triangular block. -/
theorem mem_generalizedSnakeBoard_suffix_L_cells_iff
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hr : r ≤ w.length - (last + 1))
    (hc : c ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L) :
    (r, c) ∈ (generalizedSnakeBoard w).cells ↔ c ≤ r := by
  constructor
  · intro hcell
    exact mem_generalizedSnakeBoard_suffix_L_cells_col_le_row
      hlast hc hfinal hcell
  · intro hcr
    rw [generalizedSnakeBoard, Finset.mem_filter]
    constructor
    · simpa [Finset.mem_product] using
        ⟨le_trans hr (Nat.sub_le _ _), le_trans hc (Nat.sub_le _ _)⟩
    · rw [Bool.and_eq_true]
      constructor
      · have hfalse := snakeElementReachable_rowCode_colCode_eq_false_of_le
          (w := w) hcr
        simp [hfalse]
      · have hfalse := snakeElementReachable_suffix_L_colCode_rowCode_eq_false
          hlast hc hr hfinal
        simp [hfalse]

/-- The concrete finite-board squarecase model for generalized snake words. -/
def generalizedSnakeRookModel : SquarecaseRookModel :=
  squarecaseRookModelOfFiniteSkewBoard generalizedSnakeBoard

@[simp] theorem generalizedSnakeRookModel_boardOfSnake (w : SnakeWord) :
    generalizedSnakeRookModel.boardOfSnake w = generalizedSnakeBoard w :=
  rfl

@[simp] theorem generalizedSnakeRookModel_snakePolynomial (w : SnakeWord) :
    generalizedSnakeRookModel.snakePolynomial w =
      (generalizedSnakeBoard w).rookPolynomial :=
  rfl

end GeneralizedSnakePosets
end RealRooted
