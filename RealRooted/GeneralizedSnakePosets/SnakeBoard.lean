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
    have hbounds : r ≤ n ∧ c ≤ n := by
      simpa [Finset.mem_product] using hbound
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
    have hbounds : r ≤ n ∧ c ≤ n := by
      simpa [Finset.mem_product] using hbound
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
