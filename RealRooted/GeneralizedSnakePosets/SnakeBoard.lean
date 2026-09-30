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

/-! ## Incomparable cross pairs -/

/-- The incomparable cross-chain pairs of the generalized snake poset `P(w)`:
`(r, c)` such that row element `r` and column element `c` are incomparable,
following the Alexandersson–Jal width-two-poset/skew-shape correspondence.
The Braun–Jal board `generalizedSnakeBoard` reverses the column order of this
set. -/
def snakeIncomparableBoard (w : SnakeWord) : FiniteSkewBoard where
  cells :=
    ((Finset.range (w.length + 1)).product (Finset.range (w.length + 1))).filter
      fun cell =>
        (!snakeElementReachable w (snakeRowCode cell.1) (snakeColCode cell.2) &&
          !snakeElementReachable w (snakeColCode cell.2) (snakeRowCode cell.1)) = true

/-- The cells of an all-`R` snake board form the upper triangular staircase in
the `(n + 1) × (n + 1)` square. -/
theorem mem_snakeIncomparableBoard_replicate_R_cells {n r c : ℕ} :
    (r, c) ∈ (snakeIncomparableBoard (List.replicate n SnakeLetter.R)).cells ↔
      r ≤ n ∧ c ≤ n ∧ r ≤ c := by
  constructor
  · intro h
    rw [snakeIncomparableBoard, Finset.mem_filter] at h
    simp only [List.length_replicate] at h
    rcases h with ⟨hbound, hcell⟩
    have hbounds : r ≤ n ∧ c ≤ n := by simpa [Finset.mem_product] using hbound
    rw [Bool.and_eq_true] at hcell
    rcases hcell with ⟨_hrow_col, hcol_row⟩
    have hrc : r ≤ c :=
      (snakeElementReachable_replicate_R_colCode_rowCode_eq_false_iff
        (n := n) (c := c) (r := r) hbounds.1).mp (by simpa using hcol_row)
    exact ⟨hbounds.1, hbounds.2, hrc⟩
  · rintro ⟨hr, hc, hrc⟩
    rw [snakeIncomparableBoard, Finset.mem_filter]
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
theorem mem_snakeIncomparableBoard_replicate_L_cells {n r c : ℕ} :
    (r, c) ∈ (snakeIncomparableBoard (List.replicate n SnakeLetter.L)).cells ↔
      r ≤ n ∧ c ≤ n ∧ c ≤ r := by
  constructor
  · intro h
    rw [snakeIncomparableBoard, Finset.mem_filter] at h
    simp only [List.length_replicate] at h
    rcases h with ⟨hbound, hcell⟩
    have hbounds : r ≤ n ∧ c ≤ n := by simpa [Finset.mem_product] using hbound
    rw [Bool.and_eq_true] at hcell
    rcases hcell with ⟨hrow_col, _hcol_row⟩
    have hcr : c ≤ r :=
      (snakeElementReachable_replicate_L_rowCode_colCode_eq_false_iff
        (n := n) (r := r) (c := c) hbounds.2).mp (by simpa using hrow_col)
    exact ⟨hbounds.1, hbounds.2, hcr⟩
  · rintro ⟨hr, hc, hcr⟩
    rw [snakeIncomparableBoard, Finset.mem_filter]
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

/-! ## The generalized snake board

The incomparable cross pairs above use the column order of the second chain.
Braun–Jal's non-nesting rook placements live on the board with that column
order reversed: with `n = w.length`, the cell `(r, c)` of the snake board is the
incomparable pair `(row r, col (n - c))`.  In this orientation the non-nesting
rook polynomial is the `h^*`-polynomial of the order polytope of `P(w)`; with
the unreflected columns it is not.  (Checked against an independent `h^*`
computation for all 4094 words of length at most 11.) -/

/-- The concrete Braun–Jal board attached to a generalized snake word: the
incomparable cross pairs with the column order reversed. -/
def generalizedSnakeBoard (w : SnakeWord) : FiniteSkewBoard where
  cells := (snakeIncomparableBoard w).cells.image fun cell => (cell.1, w.length - cell.2)

theorem mem_snakeIncomparableBoard_cells_le {w : SnakeWord} {r c : ℕ}
    (h : (r, c) ∈ (snakeIncomparableBoard w).cells) : r ≤ w.length ∧ c ≤ w.length := by
  rw [snakeIncomparableBoard, Finset.mem_filter] at h
  simpa [Finset.mem_product, Nat.lt_succ_iff] using h.1

/-- Membership in the snake board: `(r, c)` is a cell exactly when `c ≤ n` and
`(row r, col (n - c))` is an incomparable pair. -/
theorem mem_generalizedSnakeBoard_cells {w : SnakeWord} {r c : ℕ} :
    (r, c) ∈ (generalizedSnakeBoard w).cells ↔
      c ≤ w.length ∧ (r, w.length - c) ∈ (snakeIncomparableBoard w).cells := by
  constructor
  · intro h
    rw [generalizedSnakeBoard, Finset.mem_image] at h
    obtain ⟨⟨r', c'⟩, hmem, hEq⟩ := h
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    have hc := (mem_snakeIncomparableBoard_cells_le hmem).2
    refine ⟨Nat.sub_le _ _, ?_⟩
    rwa [Nat.sub_sub_self hc]
  · rintro ⟨hc, hmem⟩
    rw [generalizedSnakeBoard, Finset.mem_image]
    exact ⟨(r, w.length - c), hmem, by simp [Nat.sub_sub_self hc]⟩

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
