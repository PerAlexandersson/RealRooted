import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase

/-!
# Snake suffix blocks and truncated staircases

This module relates the final constant suffix blocks of concrete generalized
snake boards to the truncated-staircase coordinate convention used by the
Braun--Jal Section 3 recurrence.
-/

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

namespace FiniteSkewBoard

/-! ## Reflected triangular blocks -/

/-- Reflecting columns sends the upper triangle `r <= c` in an `(m + 1)` by
`(m + 1)` square to the truncated-staircase convention. -/
theorem mem_truncatedStaircase_reflectUpperTriangle_iff
    {m r c : ℕ} (hr : r ≤ m) :
    (r, m - c) ∈ (truncatedStaircase (m + 1) (m + 1)).cells ↔
      r ≤ c := by
  rw [mem_truncatedStaircase_cells]
  constructor
  · rintro ⟨_hr, hcol⟩
    lia
  · intro hrc
    exact ⟨Nat.lt_succ_of_le hr, by lia⟩

/-- Reflecting rows after swapping coordinates sends the lower triangle
`c <= r` in an `(m + 1)` by `(m + 1)` square to the truncated-staircase
convention. -/
theorem mem_truncatedStaircase_reflectLowerTriangle_iff
    {m r c : ℕ} (hc : c ≤ m) :
    (c, m - r) ∈ (truncatedStaircase (m + 1) (m + 1)).cells ↔
      c ≤ r := by
  rw [mem_truncatedStaircase_cells]
  constructor
  · rintro ⟨_hc, hrow⟩
    lia
  · intro hcr
    exact ⟨Nat.lt_succ_of_le hc, by lia⟩

end FiniteSkewBoard

/-! ## Final suffix blocks -/

/-- A final `R` suffix block of a concrete generalized snake board becomes the
straight truncated staircase after reflecting columns. -/
theorem mem_generalizedSnakeBoard_suffix_R_reflectCol_truncatedStaircase_iff
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hr : r ≤ w.length - (last + 1))
    (hc : c ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R) :
    (r, w.length - (last + 1) - c) ∈
        (FiniteSkewBoard.truncatedStaircase
          (w.length - (last + 1) + 1)
          (w.length - (last + 1) + 1)).cells ↔
      (r, c) ∈ (generalizedSnakeBoard w).cells := by
  rw [mem_generalizedSnakeBoard_suffix_R_cells_iff hlast hr hc hfinal]
  exact FiniteSkewBoard.mem_truncatedStaircase_reflectUpperTriangle_iff hr

/-- A final `L` suffix block of a concrete generalized snake board becomes the
straight truncated staircase after swapping coordinates and reflecting rows. -/
theorem mem_generalizedSnakeBoard_suffix_L_reflectRow_truncatedStaircase_iff
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hr : r ≤ w.length - (last + 1))
    (hc : c ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L) :
    (c, w.length - (last + 1) - r) ∈
        (FiniteSkewBoard.truncatedStaircase
          (w.length - (last + 1) + 1)
          (w.length - (last + 1) + 1)).cells ↔
      (r, c) ∈ (generalizedSnakeBoard w).cells := by
  rw [mem_generalizedSnakeBoard_suffix_L_cells_iff hlast hr hc hfinal]
  exact FiniteSkewBoard.mem_truncatedStaircase_reflectLowerTriangle_iff hc

end GeneralizedSnakePosets
end RealRooted
