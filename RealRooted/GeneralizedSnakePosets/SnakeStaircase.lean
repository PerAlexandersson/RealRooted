import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Basic

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

/-- Diagonally shift a finite cell set by `m` rows and columns.  This embeds
prefix-board cells back into the original coordinates after removing a final
constant suffix of length `m`. -/
def shiftedCells (m : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.image fun a => (a.1 + m, a.2 + m)

@[simp] theorem mem_shiftedCells {m : ℕ} {S : Finset (ℕ × ℕ)} {a : ℕ × ℕ} :
    a ∈ shiftedCells m S ↔ ∃ b ∈ S, (b.1 + m, b.2 + m) = a := by
  classical
  simp [shiftedCells]

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

/-- The smaller staircase block left after deleting the final-`R` boundary
segment, in the original suffix coordinates. -/
def finalRSmallerStaircaseCells (m : ℕ) : Finset (ℕ × ℕ) :=
  (FiniteSkewBoard.truncatedStaircase m m).cells.image fun a => (a.1, m - 1 - a.2)

/-- The smaller staircase block left after deleting the final-`L` boundary
segment, in the original suffix coordinates. -/
def finalLSmallerStaircaseCells (m : ℕ) : Finset (ℕ × ℕ) :=
  (FiniteSkewBoard.truncatedStaircase m m).cells.image fun a => (m - 1 - a.2, a.1)

@[simp] theorem mem_finalRSmallerStaircaseCells {m : ℕ} {a : ℕ × ℕ} :
    a ∈ finalRSmallerStaircaseCells m ↔ a.1 < m ∧ a.2 < m ∧ a.1 ≤ a.2 := by
  rw [finalRSmallerStaircaseCells, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [FiniteSkewBoard.mem_truncatedStaircase_cells] at hb
    constructor
    · exact hb.1
    constructor
    · have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le b.1) hb.1
      lia
    · lia
  · rintro ⟨hrow, hcol, hle⟩
    refine ⟨(a.1, m - 1 - a.2), ?_, ?_⟩
    · rw [FiniteSkewBoard.mem_truncatedStaircase_cells]
      exact ⟨hrow, by lia⟩
    · ext <;> simp
      lia

@[simp] theorem mem_finalLSmallerStaircaseCells {m : ℕ} {a : ℕ × ℕ} :
    a ∈ finalLSmallerStaircaseCells m ↔ a.1 < m ∧ a.2 < m ∧ a.2 ≤ a.1 := by
  rw [finalLSmallerStaircaseCells, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [FiniteSkewBoard.mem_truncatedStaircase_cells] at hb
    constructor
    · have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le b.1) hb.1
      lia
    constructor
    · exact hb.1
    · lia
  · rintro ⟨hrow, hcol, hle⟩
    refine ⟨(a.2, m - 1 - a.1), ?_, ?_⟩
    · rw [FiniteSkewBoard.mem_truncatedStaircase_cells]
      exact ⟨hcol, by lia⟩
    · ext <;> simp
      lia

end GeneralizedSnakePosets
end RealRooted
