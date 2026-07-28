import RealRooted.FolkloreLemma

/-!
# Finite non-nesting rook boards

This module contains the finite-board and basic non-nesting rook-polynomial API
used by the Braun--Jal generalized snake poset development.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Board and rook-polynomial interfaces -/

/-- A finite skew board, represented only by its finite set of cells.

This intentionally avoids committing to a Ferrers or squarecase coordinate
system.  Concrete squarecase encodings can later prove that their cell sets
agree with this finite model. -/
structure FiniteSkewBoard where
  cells : Finset (ℕ × ℕ)
  deriving DecidableEq

namespace FiniteSkewBoard

/-- The empty finite skew board. -/
def empty : FiniteSkewBoard :=
  ⟨∅⟩

/-- A rook placement is non-nesting if all cells lie in the board, no two
rooks share a row, and columns strictly decrease as rows increase. -/
def IsNonNestingPlacement (B : FiniteSkewBoard) (P : Finset (ℕ × ℕ)) : Prop :=
  P ⊆ B.cells ∧
    (∀ a ∈ P, ∀ b ∈ P, a ≠ b → a.1 ≠ b.1) ∧
    (∀ a ∈ P, ∀ b ∈ P, a.1 < b.1 → b.2 < a.2)

/-- The non-nesting rook polynomial of a finite skew board. -/
def rookPolynomial (B : FiniteSkewBoard) : ℝ[X] := by
  classical
  exact (B.cells.powerset.filter (fun P => B.IsNonNestingPlacement P)).sum
    (fun P => X ^ P.card)

/-- The finite set of non-nesting placements on a finite skew board. -/
def nonNestingPlacements (B : FiniteSkewBoard) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact B.cells.powerset.filter fun P => B.IsNonNestingPlacement P

/-- The finite set of non-nesting placements containing a specified cell. -/
def nonNestingPlacementsWithCell (B : FiniteSkewBoard) (a : ℕ × ℕ) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact B.nonNestingPlacements.filter fun P => a ∈ P

/-- Cells of a finite board in a fixed row. -/
def rowCells (B : FiniteSkewBoard) (row : ℕ) : Finset (ℕ × ℕ) :=
  B.cells.filter fun a => a.1 = row

/-- Cells of a finite board in a fixed column. -/
def colCells (B : FiniteSkewBoard) (col : ℕ) : Finset (ℕ × ℕ) :=
  B.cells.filter fun a => a.2 = col

/-- Valid placements with no rook in a fixed row. -/
def nonNestingPlacementsWithoutRow (B : FiniteSkewBoard) (row : ℕ) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact B.nonNestingPlacements.filter fun P => ∀ c, (row, c) ∉ P

/-- Valid placements containing a rook in a fixed row. -/
def nonNestingPlacementsWithRow (B : FiniteSkewBoard) (row : ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (B.rowCells row).biUnion fun a => B.nonNestingPlacementsWithCell a

/-- Valid placements with no rook in a fixed column. -/
def nonNestingPlacementsWithoutCol (B : FiniteSkewBoard) (col : ℕ) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact B.nonNestingPlacements.filter fun P => ∀ r, (r, col) ∉ P

/-- Valid placements containing a rook in a fixed column. -/
def nonNestingPlacementsWithCol (B : FiniteSkewBoard) (col : ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (B.colCells col).biUnion fun a => B.nonNestingPlacementsWithCell a

/-- Membership in the cells of a fixed row. -/
@[simp] theorem mem_rowCells {B : FiniteSkewBoard} {row : ℕ}
    {a : ℕ × ℕ} :
    a ∈ B.rowCells row ↔ a ∈ B.cells ∧ a.1 = row := by
  simp [rowCells]

/-- Membership in the cells of a fixed column. -/
@[simp] theorem mem_colCells {B : FiniteSkewBoard} {col : ℕ}
    {a : ℕ × ℕ} :
    a ∈ B.colCells col ↔ a ∈ B.cells ∧ a.2 = col := by
  simp [colCells]

/-- Membership in the finite set of non-nesting placements. -/
@[simp] theorem mem_nonNestingPlacements {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} :
    P ∈ B.nonNestingPlacements ↔ B.IsNonNestingPlacement P := by
  classical
  rw [nonNestingPlacements, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Membership in the finite set of non-nesting placements containing a
specified cell. -/
@[simp] theorem mem_nonNestingPlacementsWithCell {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} {a : ℕ × ℕ} :
    P ∈ B.nonNestingPlacementsWithCell a ↔
      B.IsNonNestingPlacement P ∧ a ∈ P := by
  classical
  simp [nonNestingPlacementsWithCell]

/-- Membership in the row-free placement slice. -/
@[simp] theorem mem_nonNestingPlacementsWithoutRow {B : FiniteSkewBoard}
    {row : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ B.nonNestingPlacementsWithoutRow row ↔
      B.IsNonNestingPlacement P ∧ ∀ c, (row, c) ∉ P := by
  classical
  simp [nonNestingPlacementsWithoutRow]

/-- Membership in the placement slice using a fixed row. -/
@[simp] theorem mem_nonNestingPlacementsWithRow {B : FiniteSkewBoard}
    {row : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ B.nonNestingPlacementsWithRow row ↔
      B.IsNonNestingPlacement P ∧ ∃ a ∈ B.rowCells row, a ∈ P := by
  classical
  rw [nonNestingPlacementsWithRow, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hP⟩
    rw [mem_nonNestingPlacementsWithCell] at hP
    exact ⟨hP.1, ⟨a, ha, hP.2⟩⟩
  · rintro ⟨hP, a, ha, haP⟩
    exact ⟨a, ha, mem_nonNestingPlacementsWithCell.mpr ⟨hP, haP⟩⟩

/-- Membership in the column-free placement slice. -/
@[simp] theorem mem_nonNestingPlacementsWithoutCol {B : FiniteSkewBoard}
    {col : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ B.nonNestingPlacementsWithoutCol col ↔
      B.IsNonNestingPlacement P ∧ ∀ r, (r, col) ∉ P := by
  classical
  simp [nonNestingPlacementsWithoutCol]

/-- Membership in the placement slice using a fixed column. -/
@[simp] theorem mem_nonNestingPlacementsWithCol {B : FiniteSkewBoard}
    {col : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ B.nonNestingPlacementsWithCol col ↔
      B.IsNonNestingPlacement P ∧ ∃ a ∈ B.colCells col, a ∈ P := by
  classical
  rw [nonNestingPlacementsWithCol, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hP⟩
    rw [mem_nonNestingPlacementsWithCell] at hP
    exact ⟨hP.1, ⟨a, ha, hP.2⟩⟩
  · rintro ⟨hP, a, ha, haP⟩
    exact ⟨a, ha, mem_nonNestingPlacementsWithCell.mpr ⟨hP, haP⟩⟩

/-- Distinct cells in a valid placement have distinct rows. -/
theorem IsNonNestingPlacement.row_ne {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} (hP : B.IsNonNestingPlacement P)
    {a b : ℕ × ℕ} (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) :
    a.1 ≠ b.1 :=
  hP.2.1 a ha b hb hne

/-- Distinct cells in a valid placement have distinct columns. -/
theorem IsNonNestingPlacement.col_ne {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} (hP : B.IsNonNestingPlacement P)
    {a b : ℕ × ℕ} (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) :
    a.2 ≠ b.2 := by
  have hrow_ne := hP.row_ne ha hb hne
  rcases lt_or_gt_of_ne hrow_ne with hlt | hgt
  · exact ne_of_gt (hP.2.2 a ha b hb hlt)
  · exact ne_of_lt (hP.2.2 b hb a ha hgt)

/-- The row projection of a valid placement has the same cardinality as the
placement. -/
theorem IsNonNestingPlacement.card_image_fst {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} (hP : B.IsNonNestingPlacement P) :
    (P.image fun a => a.1).card = P.card := by
  exact Finset.card_image_of_injOn (by
    intro a ha b hb hrow
    by_contra hne
    exact hP.row_ne ha hb hne hrow)

/-- The column projection of a valid placement has the same cardinality as the
placement. -/
theorem IsNonNestingPlacement.card_image_snd {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} (hP : B.IsNonNestingPlacement P) :
    (P.image fun a => a.2).card = P.card := by
  exact Finset.card_image_of_injOn (by
    intro a ha b hb hcol
    by_contra hne
    exact hP.col_ne ha hb hne hcol)

/-- Placements avoiding a row and placements using that row are disjoint. -/
theorem disjoint_nonNestingPlacementsWithoutRow_withRow
    (B : FiniteSkewBoard) (row : ℕ) :
    Disjoint (B.nonNestingPlacementsWithoutRow row)
      (B.nonNestingPlacementsWithRow row) := by
  classical
  rw [Finset.disjoint_left]
  intro P hfree hrow
  rw [mem_nonNestingPlacementsWithoutRow] at hfree
  rw [mem_nonNestingPlacementsWithRow] at hrow
  rcases hrow.2 with ⟨a, ha, haP⟩
  have hrow_eq : a.1 = row := (mem_rowCells.mp ha).2
  have hcell : (row, a.2) = a := by
    ext <;> simp [hrow_eq]
  exact hfree.2 a.2 (by simpa [hcell] using haP)

/-- Every placement either avoids a fixed row or uses a cell in that row. -/
theorem union_nonNestingPlacementsWithoutRow_withRow
    (B : FiniteSkewBoard) (row : ℕ) :
    B.nonNestingPlacementsWithoutRow row ∪ B.nonNestingPlacementsWithRow row =
      B.nonNestingPlacements := by
  classical
  ext P
  rw [Finset.mem_union, mem_nonNestingPlacementsWithoutRow,
    mem_nonNestingPlacementsWithRow, mem_nonNestingPlacements]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hP
    by_cases hrow : ∃ c, (row, c) ∈ P
    · rcases hrow with ⟨c, hcP⟩
      have hcell := hP.1 hcP
      exact Or.inr ⟨hP, ⟨(row, c), by simp [hcell], hcP⟩⟩
    · exact Or.inl ⟨hP, fun c hc => hrow ⟨c, hc⟩⟩

/-- A valid placement can contain at most one cell in a fixed row. -/
theorem pairwiseDisjoint_nonNestingPlacementsWithCell_rowCells
    (B : FiniteSkewBoard) (row : ℕ) :
    (↑(B.rowCells row) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun a => B.nonNestingPlacementsWithCell a) := by
  classical
  intro a ha b hb hne
  change Disjoint (B.nonNestingPlacementsWithCell a)
    (B.nonNestingPlacementsWithCell b)
  rw [Finset.disjoint_iff_ne]
  intro P hPa Q hQ hPQ
  rw [mem_nonNestingPlacementsWithCell] at hPa hQ
  subst Q
  have hrow_ne := hPa.1.row_ne hPa.2 hQ.2 hne
  have ha_row : a.1 = row := (mem_rowCells.mp ha).2
  have hb_row : b.1 = row := (mem_rowCells.mp hb).2
  exact hrow_ne (by rw [ha_row, hb_row])

/-- The sum over placements using a row is the sum over fixed cells in that
row. -/
theorem sum_nonNestingPlacementsWithRow
    (B : FiniteSkewBoard) (row : ℕ) :
    (B.nonNestingPlacementsWithRow row).sum (fun P => (X : ℝ[X]) ^ P.card) =
      (B.rowCells row).sum (fun a =>
        (B.nonNestingPlacementsWithCell a).sum fun P => (X : ℝ[X]) ^ P.card) := by
  classical
  rw [nonNestingPlacementsWithRow]
  exact Finset.sum_biUnion
    (pairwiseDisjoint_nonNestingPlacementsWithCell_rowCells B row)

/-- The placement sum for a finite board splits according to occupancy of a
fixed row. -/
theorem sum_nonNestingPlacements_eq_withoutRow_add_withRow
    (B : FiniteSkewBoard) (row : ℕ) :
    B.nonNestingPlacements.sum (fun P => (X : ℝ[X]) ^ P.card) =
      (B.nonNestingPlacementsWithoutRow row).sum
        (fun P => (X : ℝ[X]) ^ P.card) +
      (B.rowCells row).sum (fun a =>
        (B.nonNestingPlacementsWithCell a).sum fun P => (X : ℝ[X]) ^ P.card) := by
  classical
  rw [← union_nonNestingPlacementsWithoutRow_withRow B row]
  rw [Finset.sum_union
    (disjoint_nonNestingPlacementsWithoutRow_withRow B row)]
  rw [sum_nonNestingPlacementsWithRow]

/-- Placements avoiding a column and placements using that column are
disjoint. -/
theorem disjoint_nonNestingPlacementsWithoutCol_withCol
    (B : FiniteSkewBoard) (col : ℕ) :
    Disjoint (B.nonNestingPlacementsWithoutCol col)
      (B.nonNestingPlacementsWithCol col) := by
  classical
  rw [Finset.disjoint_left]
  intro P hfree hcol
  rw [mem_nonNestingPlacementsWithoutCol] at hfree
  rw [mem_nonNestingPlacementsWithCol] at hcol
  rcases hcol.2 with ⟨a, ha, haP⟩
  have hcol_eq : a.2 = col := (mem_colCells.mp ha).2
  have hcell : (a.1, col) = a := by
    ext <;> simp [hcol_eq]
  exact hfree.2 a.1 (by simpa [hcell] using haP)

/-- Every placement either avoids a fixed column or uses a cell in that
column. -/
theorem union_nonNestingPlacementsWithoutCol_withCol
    (B : FiniteSkewBoard) (col : ℕ) :
    B.nonNestingPlacementsWithoutCol col ∪ B.nonNestingPlacementsWithCol col =
      B.nonNestingPlacements := by
  classical
  ext P
  rw [Finset.mem_union, mem_nonNestingPlacementsWithoutCol,
    mem_nonNestingPlacementsWithCol, mem_nonNestingPlacements]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hP
    by_cases hcol : ∃ r, (r, col) ∈ P
    · rcases hcol with ⟨r, hrP⟩
      have hcell := hP.1 hrP
      exact Or.inr ⟨hP, ⟨(r, col), by simp [hcell], hrP⟩⟩
    · exact Or.inl ⟨hP, fun r hr => hcol ⟨r, hr⟩⟩

/-- A valid placement can contain at most one cell in a fixed column. -/
theorem pairwiseDisjoint_nonNestingPlacementsWithCell_colCells
    (B : FiniteSkewBoard) (col : ℕ) :
    (↑(B.colCells col) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun a => B.nonNestingPlacementsWithCell a) := by
  classical
  intro a ha b hb hne
  change Disjoint (B.nonNestingPlacementsWithCell a)
    (B.nonNestingPlacementsWithCell b)
  rw [Finset.disjoint_iff_ne]
  intro P hPa Q hQ hPQ
  rw [mem_nonNestingPlacementsWithCell] at hPa hQ
  subst Q
  have hcol_ne := hPa.1.col_ne hPa.2 hQ.2 hne
  have ha_col : a.2 = col := (mem_colCells.mp ha).2
  have hb_col : b.2 = col := (mem_colCells.mp hb).2
  exact hcol_ne (by rw [ha_col, hb_col])

/-- The sum over placements using a column is the sum over fixed cells in that
column. -/
theorem sum_nonNestingPlacementsWithCol
    (B : FiniteSkewBoard) (col : ℕ) :
    (B.nonNestingPlacementsWithCol col).sum (fun P => (X : ℝ[X]) ^ P.card) =
      (B.colCells col).sum (fun a =>
        (B.nonNestingPlacementsWithCell a).sum fun P => (X : ℝ[X]) ^ P.card) := by
  classical
  rw [nonNestingPlacementsWithCol]
  exact Finset.sum_biUnion
    (pairwiseDisjoint_nonNestingPlacementsWithCell_colCells B col)

/-- The placement sum for a finite board splits according to occupancy of a
fixed column. -/
theorem sum_nonNestingPlacements_eq_withoutCol_add_withCol
    (B : FiniteSkewBoard) (col : ℕ) :
    B.nonNestingPlacements.sum (fun P => (X : ℝ[X]) ^ P.card) =
      (B.nonNestingPlacementsWithoutCol col).sum
        (fun P => (X : ℝ[X]) ^ P.card) +
      (B.colCells col).sum (fun a =>
        (B.nonNestingPlacementsWithCell a).sum fun P => (X : ℝ[X]) ^ P.card) := by
  classical
  rw [← union_nonNestingPlacementsWithoutCol_withCol B col]
  rw [Finset.sum_union
    (disjoint_nonNestingPlacementsWithoutCol_withCol B col)]
  rw [sum_nonNestingPlacementsWithCol]

/-- The rook polynomial as a sum over the named finite set of non-nesting
placements. -/
theorem rookPolynomial_eq_nonNestingPlacements_sum (B : FiniteSkewBoard) :
    B.rookPolynomial =
      B.nonNestingPlacements.sum fun P => (X : ℝ[X]) ^ P.card := by
  classical
  rw [rookPolynomial, nonNestingPlacements]

/-- The coefficient of `X^k` in a finite skew-board rook polynomial counts
non-nesting placements of cardinality `k`. -/
theorem rookPolynomial_coeff (B : FiniteSkewBoard) (k : ℕ) :
    B.rookPolynomial.coeff k =
      ((B.nonNestingPlacements.filter fun P => P.card = k).card : ℝ) := by
  classical
  rw [rookPolynomial_eq_nonNestingPlacements_sum, Polynomial.finsetSum_coeff]
  trans B.nonNestingPlacements.sum fun P =>
      if P.card = k then (1 : ℝ) else 0
  · apply Finset.sum_congr rfl
    intro P _hP
    by_cases hcard : P.card = k
    · simp [Polynomial.coeff_X_pow, hcard]
    · have hne : k ≠ P.card := fun h => hcard h.symm
      simp [Polynomial.coeff_X_pow, hcard, hne]
  · rw [← Finset.sum_filter]
    simp

/-- The empty placement is non-nesting on every finite skew board. -/
@[simp] theorem isNonNestingPlacement_empty (B : FiniteSkewBoard) :
    B.IsNonNestingPlacement ∅ := by
  simp [IsNonNestingPlacement]

/-- A singleton cell is a non-nesting placement when it lies in the board. -/
theorem isNonNestingPlacement_singleton {B : FiniteSkewBoard} {a : ℕ × ℕ}
    (ha : a ∈ B.cells) :
    B.IsNonNestingPlacement ({a} : Finset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact ha
  · intro x hx y hy hne
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy] at hne
    exact (hne rfl).elim
  · intro x hx y hy hlt
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

/-- A two-cell set is a non-nesting placement when the two cells lie in the
board, are in different rows, and satisfy the decreasing-column condition. -/
theorem isNonNestingPlacement_pair {B : FiniteSkewBoard} (a b : ℕ × ℕ)
    (ha : a ∈ B.cells) (hb : b ∈ B.cells) (hrow : a.1 ≠ b.1)
    (hcol_ab : a.1 < b.1 → b.2 < a.2)
    (hcol_ba : b.1 < a.1 → a.2 < b.2) :
    B.IsNonNestingPlacement ({a, b} : Finset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · intro x hx y hy hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · exact hrow
    · rcases hy with rfl | rfl
      · exact hrow.symm
      · exact (hne rfl).elim
  · intro x hx y hy hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (Nat.lt_irrefl _ hlt).elim
      · exact hcol_ab hlt
    · rcases hy with rfl | rfl
      · exact hcol_ba hlt
      · exact (Nat.lt_irrefl _ hlt).elim

private def finsetAllBool {α : Type*} (s : Finset α) (p : α → Bool) : Bool :=
  s.fold (fun a b => a && b) true p

private lemma finsetAllBool_iff {α : Type*} (s : Finset α) (p : α → Bool) :
    finsetAllBool s p ↔ ∀ a ∈ s, p a := by
  classical
  induction s using Finset.induction with
  | empty => simp [finsetAllBool]
  | insert a s ha ih =>
      rw [finsetAllBool, Finset.fold_insert ha, Bool.and_eq_true_iff]
      constructor
      · rintro ⟨hpa, hall⟩ b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact hpa
        · exact ih.mp hall b hb
      · intro hall
        exact ⟨hall a (Finset.mem_insert_self a s), ih.mpr fun b hb =>
          hall b (Finset.mem_insert_of_mem hb)⟩

def isNonNestingPlacementBool (B : FiniteSkewBoard)
    (P : Finset (ℕ × ℕ)) : Bool :=
  finsetAllBool P (fun a => decide (a ∈ B.cells)) &&
    finsetAllBool P (fun a =>
      finsetAllBool P (fun b =>
        decide ((a.1 = b.1 → a.2 ≠ b.2) → a.1 ≠ b.1))) &&
    finsetAllBool P (fun a =>
      finsetAllBool P (fun b => decide (a.1 < b.1 → b.2 < a.2)))

theorem isNonNestingPlacementBool_iff (B : FiniteSkewBoard)
    (P : Finset (ℕ × ℕ)) :
    isNonNestingPlacementBool B P ↔ B.IsNonNestingPlacement P := by
  simp only [isNonNestingPlacementBool, ne_eq, decide_implies, decide_not,
    dite_eq_ite, Bool.if_true_right, Bool.not_or, Bool.not_not,
    Bool.and_eq_true, finsetAllBool_iff, decide_eq_true_eq, Prod.forall,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_lt, IsNonNestingPlacement,
    Finset.subset_iff, Prod.mk.injEq, not_and]
  constructor
  · rintro ⟨⟨hsub, hrow⟩, hnest⟩
    refine ⟨hsub, ?_, ?_⟩
    · intro a b hab c d hcd hne
      rcases hrow a b hab c d hcd with hEq | hrow_ne
      · exact (hne hEq.1 hEq.2).elim
      · exact hrow_ne
    · intro a b hab c d hcd hlt
      rcases hnest a b hab c d hcd with hle | hcol
      · exact (False.elim ((not_lt_of_ge hle) hlt))
      · exact hcol
  · rintro ⟨hsub, hrow, hnest⟩
    refine ⟨⟨hsub, ?_⟩, ?_⟩
    · intro a b hab c d hcd
      by_cases ha : a = c
      · by_cases hb : b = d
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr (hrow a b hab c d hcd (by intro _; exact hb))
      · exact Or.inr ha
    · intro a b hab c d hcd
      by_cases hlt : a < c
      · exact Or.inr (hnest a b hab c d hcd hlt)
      · exact Or.inl (le_of_not_gt hlt)

/-- The empty board has rook polynomial `1`. -/
@[simp] theorem rookPolynomial_empty :
    empty.rookPolynomial = 1 := by
  classical
  have hpowerset :
      empty.cells.powerset = ({∅} : Finset (Finset (ℕ × ℕ))) := by
    simp [empty]
  have hfilter :
      empty.cells.powerset.filter (fun P => empty.IsNonNestingPlacement P) =
        ({∅} : Finset (Finset (ℕ × ℕ))) := by
    rw [hpowerset]
    apply Finset.filter_true_of_mem
    intro P hP
    have hPempty : P = ∅ := by
      simpa using hP
    subst P
    simp [IsNonNestingPlacement, empty]
  simp [rookPolynomial, hfilter]

/-- Finite skew board rook polynomials have nonnegative coefficients. -/
theorem rookPolynomial_hasNonnegCoeffs (B : FiniteSkewBoard) :
    HasNonnegCoeffs B.rookPolynomial := by
  intro k
  rw [rookPolynomial_coeff]
  positivity

/-- The empty placement gives the constant coefficient of a finite skew board
rook polynomial. -/
@[simp] theorem rookPolynomial_coeff_zero (B : FiniteSkewBoard) :
    B.rookPolynomial.coeff 0 = 1 := by
  classical
  rw [rookPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro P _hP hne
    have hP_nonzero : P.card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    have hzero : ¬ 0 = P.card := fun h => hP_nonzero h.symm
    simp [Polynomial.coeff_X_pow, hzero]
  · intro hnot
    simp at hnot

/-- Finite skew board rook polynomials are nonzero. -/
theorem rookPolynomial_ne_zero (B : FiniteSkewBoard) :
    B.rookPolynomial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
  rw [rookPolynomial_coeff_zero] at hcoeff
  norm_num at hcoeff

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
