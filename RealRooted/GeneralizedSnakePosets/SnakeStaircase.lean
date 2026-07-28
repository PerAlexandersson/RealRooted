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

/-! ## Final suffix blocks -/

/-- The distinguished final-`R` boundary segment from Braun--Jal Theorem 3.5,
in the local suffix coordinates.  For suffix length `m`, this is the final
column without the corner cell. -/
def finalRBoundarySegment (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).image fun r => (r, m)

/-- The distinguished final-`L` boundary segment from Braun--Jal Theorem 3.5,
in the local suffix coordinates.  For suffix length `m`, this is the final row
without the corner cell. -/
def finalLBoundarySegment (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).image fun c => (m, c)

@[simp] theorem mem_finalRBoundarySegment {m : ℕ} {a : ℕ × ℕ} :
    a ∈ finalRBoundarySegment m ↔ a.1 < m ∧ a.2 = m := by
  rw [finalRBoundarySegment, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨by simpa using hr, rfl⟩
  · rintro ⟨hr, hcol⟩
    exact ⟨a.1, by simpa using hr, by ext <;> simp [hcol]⟩

@[simp] theorem mem_finalLBoundarySegment {m : ℕ} {a : ℕ × ℕ} :
    a ∈ finalLBoundarySegment m ↔ a.1 = m ∧ a.2 < m := by
  rw [finalLBoundarySegment, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨rfl, by simpa using hc⟩
  · rintro ⟨hrow, hc⟩
    exact ⟨a.2, by simpa using hc, by ext <;> simp [hrow]⟩

/-- The final-`R` distinguished segment lies in the concrete snake board. -/
theorem finalRBoundarySegment_subset_generalizedSnakeBoard_cells
    {w : SnakeWord} {last : ℕ} (hlast : w.IsLastChangeIndex last)
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R) :
    finalRBoundarySegment (w.length - (last + 1)) ⊆
      (generalizedSnakeBoard w).cells := by
  intro a ha
  rw [mem_finalRBoundarySegment] at ha
  have hrow : a.1 ≤ w.length - (last + 1) := Nat.le_of_lt ha.1
  have hcol : a.2 ≤ w.length - (last + 1) := by rw [ha.2]
  rw [mem_generalizedSnakeBoard_suffix_R_cells_iff hlast hrow hcol hfinal]
  rw [ha.2]
  exact Nat.le_of_lt ha.1

/-- The final-`L` distinguished segment lies in the concrete snake board. -/
theorem finalLBoundarySegment_subset_generalizedSnakeBoard_cells
    {w : SnakeWord} {last : ℕ} (hlast : w.IsLastChangeIndex last)
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L) :
    finalLBoundarySegment (w.length - (last + 1)) ⊆
      (generalizedSnakeBoard w).cells := by
  intro a ha
  rw [mem_finalLBoundarySegment] at ha
  have hrow : a.1 ≤ w.length - (last + 1) := by rw [ha.1]
  have hcol : a.2 ≤ w.length - (last + 1) := Nat.le_of_lt ha.2
  rw [mem_generalizedSnakeBoard_suffix_L_cells_iff hlast hrow hcol hfinal]
  rw [ha.1]
  exact Nat.le_of_lt ha.2

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
