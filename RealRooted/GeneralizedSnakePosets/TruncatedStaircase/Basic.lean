import RealRooted.GeneralizedSnakePosets.FiniteBoard

/-!
# Truncated staircase board basics

This module defines truncated-staircase finite boards and records the elementary
reflection lemmas used by the full-staircase and snake-suffix developments.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

/-- The truncated staircase shape `mu_{n,i}` used in Braun--Jal Section 3,
modeled as the first `i` rows of the staircase with row lengths
`n, n - 1, ...`. -/
def truncatedStaircase (n i : ℕ) : FiniteSkewBoard where
  cells :=
    (Finset.range i).biUnion fun row =>
      (Finset.range (n - row)).image fun col => (row, col)

/-- Membership in a truncated staircase cell set. -/
@[simp] theorem mem_truncatedStaircase_cells {n i row col : ℕ} :
    (row, col) ∈ (truncatedStaircase n i).cells ↔ row < i ∧ col < n - row := by
  simp [truncatedStaircase]

/-! ## Reflected triangular blocks -/

/-- The full truncated staircase consists exactly of cells below the
antidiagonal. -/
theorem mem_truncatedStaircase_full_cells_iff {n row col : ℕ} :
    (row, col) ∈ (truncatedStaircase n n).cells ↔ row + col < n := by
  rw [mem_truncatedStaircase_cells]
  constructor
  · intro h
    simpa [Nat.add_comm] using Nat.add_lt_of_lt_sub h.2
  · intro h
    have hcolrow : col + row < n := by simpa [Nat.add_comm] using h
    exact ⟨Nat.lt_of_le_of_lt (Nat.le_add_right row col) h,
      Nat.lt_sub_iff_add_lt.mpr hcolrow⟩

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

/-- Full-staircase version of the column-reflection convention used for
encoding placements by componentwise ordered subset pairs. -/
theorem mem_truncatedStaircase_full_reflectColumn_iff
    {n row col : ℕ} (hrow : row < n) :
    (row, n - 1 - col) ∈ (truncatedStaircase n n).cells ↔
      row ≤ col := by
  rw [mem_truncatedStaircase_full_cells_iff]
  constructor <;> intro h <;> lia

/-- Reflected columns remain distinct in a full-staircase placement. -/
theorem IsNonNestingPlacement.full_reflectedColumn_ne
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P)
    {a b : ℕ × ℕ} (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) :
    n - 1 - a.2 ≠ n - 1 - b.2 := by
  intro hreflect
  have hcol_ne := hP.col_ne ha hb hne
  have ha_cell := hP.1 ha
  have hb_cell := hP.1 hb
  rw [mem_truncatedStaircase_full_cells_iff] at ha_cell hb_cell
  have hcol : a.2 = b.2 := by lia
  exact hcol_ne hcol

/-- The reflected-column projection of a full-staircase placement has the same
cardinality as the placement. -/
theorem IsNonNestingPlacement.full_card_image_reflectedColumn
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (P.image fun a => n - 1 - a.2).card = P.card := by
  exact Finset.card_image_of_injOn (by
    intro a ha b hb hreflect
    by_contra hne
    exact hP.full_reflectedColumn_ne ha hb hne hreflect)

/-- A full-staircase cell lies weakly below its reflected column coordinate. -/
theorem IsNonNestingPlacement.full_row_le_reflectedColumn
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P)
    {a : ℕ × ℕ} (ha : a ∈ P) :
    a.1 ≤ n - 1 - a.2 := by
  have ha_cell := hP.1 ha
  rw [mem_truncatedStaircase_full_cells_iff] at ha_cell
  lia

/-- Along increasing rows in a full-staircase placement, reflected columns
strictly increase. -/
theorem IsNonNestingPlacement.full_reflectedColumn_lt_of_row_lt
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P)
    {a b : ℕ × ℕ} (ha : a ∈ P) (hb : b ∈ P) (hrow : a.1 < b.1) :
    n - 1 - a.2 < n - 1 - b.2 := by
  have hcol_lt := hP.2.2 a ha b hb hrow
  have ha_cell := hP.1 ha
  have hb_cell := hP.1 hb
  rw [mem_truncatedStaircase_full_cells_iff] at ha_cell hb_cell
  lia

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
