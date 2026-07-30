import RealRooted.GeneralizedSnakePosets.SnakeStaircase
import RealRooted.GeneralizedSnakePosets.Section3Packages
import RealRooted.GeneralizedSnakePosets.MatrixInduction

/-!
# Generalized snake poset finite-board interfaces

This file contains the concrete finite-board interfaces for Braun--Jal,
*Order polytopes of generalized snake posets are h^*-real-rooted*,
arXiv:2607.00922v1.

The paper-facing theorem statements and Section 3 packages live in
`RealRooted.GeneralizedSnakePosets.Statements` and
`RealRooted.GeneralizedSnakePosets.Section3Packages`.  This module imports the
package layer as an umbrella, so downstream files that import
`RealRooted.GeneralizedSnakePosets` keep the same public API.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

universe u

namespace FiniteSkewBoard

/-! ## Skew Ferrers boards -/

/-- The skew Ferrers board `lam / mu` in zero-based row coordinates.

The paper uses cells `(i,j)` with `1 ≤ i` and `mu_i < j ≤ lam_i`; this encoding
uses rows indexed by `0, ..., lam.length - 1`, keeps the same column inequality,
and reads missing `mu` entries as zero. -/
def skewFerrers (lam mu : List ℕ) : FiniteSkewBoard where
  cells :=
    (Finset.range lam.length).biUnion fun row =>
      (Finset.Ioc (mu.getD row 0) (lam.getD row 0)).image fun col => (row, col)

/-- The straight Ferrers board attached to a finite row-length list. -/
def ferrers (lam : List ℕ) : FiniteSkewBoard :=
  skewFerrers lam []

/-- Membership in a straight Ferrers-board cell set. -/
@[simp] theorem mem_ferrers_cells {lam : List ℕ} {row col : ℕ} :
    (row, col) ∈ (ferrers lam).cells ↔
      row < lam.length ∧ 0 < col ∧ col ≤ lam.getD row 0 := by
  simp [ferrers, skewFerrers]

/-- The non-nesting rook polynomial of a zero-based skew Ferrers board. -/
def skewFerrersRookPolynomial (lam mu : List ℕ) : ℝ[X] :=
  (skewFerrers lam mu).rookPolynomial

/-- The non-nesting rook polynomial of a straight Ferrers board. -/
def ferrersRookPolynomial (lam : List ℕ) : ℝ[X] :=
  (ferrers lam).rookPolynomial

/-- Remove one column from every row-length entry. -/
def partitionSubOne (lam : List ℕ) : List ℕ :=
  lam.map fun n => n - 1

@[simp] theorem partitionSubOne_getD (lam : List ℕ) (row : ℕ) :
    (partitionSubOne lam).getD row 0 = lam.getD row 0 - 1 := by
  rw [partitionSubOne, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases lam[row]? <;> simp

/-- Keep the first `i` row-length entries. -/
def partitionPrefix (lam : List ℕ) (i : ℕ) : List ℕ :=
  lam.take i

@[simp] theorem partitionPrefix_length (lam : List ℕ) (i : ℕ) :
    (partitionPrefix lam i).length = min i lam.length := by
  simp [partitionPrefix, List.length_take]

theorem partitionPrefix_getD_of_lt {lam : List ℕ} {row i : ℕ}
    (hrow : row < i) :
    (partitionPrefix lam i).getD row 0 = lam.getD row 0 := by
  rw [partitionPrefix, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take]
  simp [hrow]

/-- A list of row lengths is an integer partition in Braun--Jal's sense:
positive parts in weakly decreasing order. -/
def IsIntegerPartition (lam : List ℕ) : Prop :=
  lam.Pairwise (· ≥ ·) ∧ ∀ n ∈ lam, 0 < n

/-- The first-column cells of a straight Ferrers board. -/
def firstColumnCells (lam : List ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range lam.length).image fun row => (row, 1)

@[simp] theorem mem_firstColumnCells {lam : List ℕ} {a : ℕ × ℕ} :
    a ∈ firstColumnCells lam ↔ a.1 < lam.length ∧ a.2 = 1 := by
  classical
  rw [firstColumnCells, Finset.mem_image]
  constructor
  · rintro ⟨row, hrow, rfl⟩
    exact ⟨Finset.mem_range.mp hrow, rfl⟩
  · rintro ⟨hrow, hcol⟩
    refine ⟨a.1, Finset.mem_range.mpr hrow, ?_⟩
    ext <;> simp [hcol]

/-- Remove a first-column rook and shift all remaining columns left by one. -/
def firstColumnRemainder (i : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  (P.erase (i, 1)).image fun a => (a.1, a.2 - 1)

/-- Shift a placement right by one column and reinsert the first-column rook. -/
def firstColumnExtension (i : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  insert (i, 1) (P.image fun a => (a.1, a.2 + 1))

/-- Delete the first column from a placement by shifting all columns left. -/
def deleteFirstColumnPlacement (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  P.image fun a => (a.1, a.2 - 1)

/-- Add a first column to a placement by shifting all columns right. -/
def addFirstColumnPlacement (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  P.image fun a => (a.1, a.2 + 1)

/-- Skew Ferrers rook polynomials have nonnegative coefficients. -/
theorem skewFerrersRookPolynomial_hasNonnegCoeffs (lam mu : List ℕ) :
    HasNonnegCoeffs (skewFerrersRookPolynomial lam mu) :=
  rookPolynomial_hasNonnegCoeffs _

/-- Ferrers rook polynomials have nonnegative coefficients. -/
theorem ferrersRookPolynomial_hasNonnegCoeffs (lam : List ℕ) :
    HasNonnegCoeffs (ferrersRookPolynomial lam) :=
  rookPolynomial_hasNonnegCoeffs _

/-- Skew Ferrers rook polynomials have constant coefficient one. -/
@[simp] theorem skewFerrersRookPolynomial_coeff_zero (lam mu : List ℕ) :
    (skewFerrersRookPolynomial lam mu).coeff 0 = 1 :=
  rookPolynomial_coeff_zero _

/-- Ferrers rook polynomials have constant coefficient one. -/
@[simp] theorem ferrersRookPolynomial_coeff_zero (lam : List ℕ) :
    (ferrersRookPolynomial lam).coeff 0 = 1 :=
  rookPolynomial_coeff_zero _

/-- Skew Ferrers rook polynomials are nonzero. -/
theorem skewFerrersRookPolynomial_ne_zero (lam mu : List ℕ) :
    skewFerrersRookPolynomial lam mu ≠ 0 :=
  rookPolynomial_ne_zero _

/-- Ferrers rook polynomials are nonzero. -/
theorem ferrersRookPolynomial_ne_zero (lam : List ℕ) :
    ferrersRookPolynomial lam ≠ 0 :=
  rookPolynomial_ne_zero _

/-- Braun--Jal Proposition 3.2, stated for a straight Ferrers rook-polynomial
family indexed by integer partitions.  The partition hypothesis is needed:
without positive row lengths, the one-row list `[0]` gives the false identity
`1 = 1 + X`. -/
def FerrersFirstColumnDeletionStatement (M : List ℕ → ℝ[X]) : Prop :=
  ∀ lam : List ℕ, IsIntegerPartition lam →
    M lam =
      M (partitionSubOne lam) +
        X * ((List.range lam.length).map fun i =>
          M (partitionPrefix (partitionSubOne lam) i)).sum

/-- Braun--Jal Proposition 3.2 as the target statement for the concrete finite
Ferrers-board rook-polynomial model. -/
def ferrersFirstColumnDeletionStatement : Prop :=
  FerrersFirstColumnDeletionStatement ferrersRookPolynomial

/-- Valid Ferrers placements with no rook in the first column. -/
def nonNestingPlacementsWithoutFirstColumn (lam : List ℕ) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact (ferrers lam).nonNestingPlacements.filter fun P => ∀ row, (row, 1) ∉ P

/-- Valid Ferrers placements containing a fixed first-column cell. -/
def nonNestingPlacementsWithFirstColumnCell (lam : List ℕ) (row : ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (ferrers lam).nonNestingPlacementsWithCell (row, 1)

/-- Valid Ferrers placements with a rook somewhere in the first column. -/
def nonNestingPlacementsWithFirstColumn (lam : List ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (firstColumnCells lam).biUnion fun a =>
    (ferrers lam).nonNestingPlacementsWithCell a

@[simp] theorem mem_nonNestingPlacementsWithoutFirstColumn
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ nonNestingPlacementsWithoutFirstColumn lam ↔
      (ferrers lam).IsNonNestingPlacement P ∧ ∀ row, (row, 1) ∉ P := by
  classical
  simp [nonNestingPlacementsWithoutFirstColumn]

@[simp] theorem mem_nonNestingPlacementsWithFirstColumnCell
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} {row : ℕ} :
    P ∈ nonNestingPlacementsWithFirstColumnCell lam row ↔
      (ferrers lam).IsNonNestingPlacement P ∧ (row, 1) ∈ P := by
  classical
  simp [nonNestingPlacementsWithFirstColumnCell]

@[simp] theorem mem_nonNestingPlacementsWithFirstColumn
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ nonNestingPlacementsWithFirstColumn lam ↔
      (ferrers lam).IsNonNestingPlacement P ∧
        ∃ a ∈ firstColumnCells lam, a ∈ P := by
  classical
  rw [nonNestingPlacementsWithFirstColumn, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hP⟩
    rw [mem_nonNestingPlacementsWithCell] at hP
    exact ⟨hP.1, ⟨a, ha, hP.2⟩⟩
  · rintro ⟨hP, a, ha, haP⟩
    exact ⟨a, ha, mem_nonNestingPlacementsWithCell.mpr ⟨hP, haP⟩⟩

/-- First-column-free placements and placements using the first column are
disjoint. -/
theorem disjoint_nonNestingPlacementsWithoutFirstColumn_withFirstColumn
    (lam : List ℕ) :
    Disjoint (nonNestingPlacementsWithoutFirstColumn lam)
      (nonNestingPlacementsWithFirstColumn lam) := by
  classical
  rw [Finset.disjoint_left]
  intro P hfree hfirst
  rw [mem_nonNestingPlacementsWithoutFirstColumn] at hfree
  rw [mem_nonNestingPlacementsWithFirstColumn] at hfirst
  rcases hfirst.2 with ⟨a, ha, haP⟩
  have hcol : a.2 = 1 := (mem_firstColumnCells.mp ha).2
  have hcell : (a.1, 1) = a := by
    ext <;> simp [hcol]
  exact hfree.2 a.1 (by simpa [hcell] using haP)

/-- Valid Ferrers placements split into those avoiding the first column and
those using it. -/
theorem union_nonNestingPlacementsWithoutFirstColumn_withFirstColumn
    (lam : List ℕ) :
    nonNestingPlacementsWithoutFirstColumn lam ∪
        nonNestingPlacementsWithFirstColumn lam =
      (ferrers lam).nonNestingPlacements := by
  classical
  ext P
  rw [Finset.mem_union, mem_nonNestingPlacementsWithoutFirstColumn,
    mem_nonNestingPlacementsWithFirstColumn, mem_nonNestingPlacements]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hP
    by_cases hfirst : ∃ row, (row, 1) ∈ P
    · rcases hfirst with ⟨row, hrowP⟩
      have hcell := hP.1 hrowP
      rw [mem_ferrers_cells] at hcell
      exact Or.inr ⟨hP, ⟨(row, 1), mem_firstColumnCells.mpr
        ⟨hcell.1, rfl⟩, hrowP⟩⟩
    · exact Or.inl ⟨hP, fun row hrowP => hfirst ⟨row, hrowP⟩⟩

/-- A valid placement can contain at most one first-column cell. -/
theorem pairwiseDisjoint_nonNestingPlacementsWithCell_firstColumn
    (lam : List ℕ) :
    (↑(firstColumnCells lam) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun a => (ferrers lam).nonNestingPlacementsWithCell a) := by
  classical
  intro a ha b hb hne
  change Disjoint ((ferrers lam).nonNestingPlacementsWithCell a)
    ((ferrers lam).nonNestingPlacementsWithCell b)
  rw [Finset.disjoint_iff_ne]
  intro P hPa Q hQ hPQ
  rw [mem_nonNestingPlacementsWithCell] at hPa hQ
  subst Q
  have hcol_a : a.2 = 1 := (mem_firstColumnCells.mp ha).2
  have hcol_b : b.2 = 1 := (mem_firstColumnCells.mp hb).2
  by_cases hrow : a.1 = b.1
  · have hab : a = b := by
      ext <;> simp [hrow, hcol_a, hcol_b]
    exact hne hab
  · rcases Nat.lt_or_gt_of_ne hrow with hlt | hgt
    · have hcol := hPa.1.2.2 a hPa.2 b hQ.2 hlt
      simp [hcol_a, hcol_b] at hcol
    · have hcol := hPa.1.2.2 b hQ.2 a hPa.2 hgt
      simp [hcol_a, hcol_b] at hcol

/-- The sum over placements using the first column is the sum over fixed
first-column cells. -/
theorem sum_nonNestingPlacementsWithFirstColumn
    (lam : List ℕ) :
    (nonNestingPlacementsWithFirstColumn lam).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        (firstColumnCells lam).sum (fun a =>
          ((ferrers lam).nonNestingPlacementsWithCell a).sum
            (fun P => (X : ℝ[X]) ^ P.card)) := by
  classical
  rw [nonNestingPlacementsWithFirstColumn]
  exact Finset.sum_biUnion
    (pairwiseDisjoint_nonNestingPlacementsWithCell_firstColumn lam)

/-- The placement sum for a Ferrers board splits according to first-column
occupancy. -/
theorem sum_nonNestingPlacements_eq_withoutFirstColumn_add_withFirstColumn
    (lam : List ℕ) :
    ((ferrers lam).nonNestingPlacements).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        (nonNestingPlacementsWithoutFirstColumn lam).sum
          (fun P => (X : ℝ[X]) ^ P.card) +
        (firstColumnCells lam).sum (fun a =>
          ((ferrers lam).nonNestingPlacementsWithCell a).sum
            (fun P => (X : ℝ[X]) ^ P.card)) := by
  classical
  rw [← union_nonNestingPlacementsWithoutFirstColumn_withFirstColumn lam]
  rw [Finset.sum_union
    (disjoint_nonNestingPlacementsWithoutFirstColumn_withFirstColumn lam)]
  rw [sum_nonNestingPlacementsWithFirstColumn]

/-- Deleting the first column sends a first-column-free placement in `lam` to
a placement in `partitionSubOne lam`. -/
theorem deleteFirstColumnPlacement_isNonNestingPlacement
    {lam : List ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (ferrers lam).IsNonNestingPlacement P)
    (hfree : ∀ row, (row, 1) ∉ P) :
    (ferrers (partitionSubOne lam)).IsNonNestingPlacement
      (deleteFirstColumnPlacement P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [deleteFirstColumnPlacement] at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases a with ⟨row, col⟩
    have ha_cell := hP.1 ha
    rw [mem_ferrers_cells] at ha_cell ⊢
    have hcol_ne : col ≠ 1 := by
      intro hcol
      exact hfree row (by simpa [hcol] using ha)
    have hcol_gt : 1 < col := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt ha_cell.2.1) hcol_ne.symm
    refine ⟨by simpa [partitionSubOne] using ha_cell.1,
      Nat.sub_pos_of_lt hcol_gt, ?_⟩
    rw [partitionSubOne_getD]
    exact Nat.sub_le_sub_right ha_cell.2.2 1
  · intro x hx y hy hxy
    rw [deleteFirstColumnPlacement] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hxy rfl
    exact hP.2.1 a ha b hb hab
  · intro x hx y hy hxy
    rw [deleteFirstColumnPlacement] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hrow : a.1 < b.1 := hxy
    have hcol := hP.2.2 a ha b hb hrow
    have hb_cell := hP.1 hb
    rw [mem_ferrers_cells] at hb_cell
    have hb_col_ne : b.2 ≠ 1 := by
      intro hcol_one
      have hb_eq : (b.1, 1) = b := by
        ext <;> simp [hcol_one]
      exact hfree b.1 (by simpa [hb_eq] using hb)
    have hb_col_gt : 1 < b.2 := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt hb_cell.2.1) hb_col_ne.symm
    exact Nat.sub_lt_sub_right hb_cell.2.1 hcol

/-- Adding a first column sends a placement of `partitionSubOne lam` back to a
first-column-free placement in `lam`. -/
theorem addFirstColumnPlacement_isNonNestingPlacement
    {lam : List ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (ferrers (partitionSubOne lam)).IsNonNestingPlacement P) :
    (ferrers lam).IsNonNestingPlacement (addFirstColumnPlacement P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [addFirstColumnPlacement] at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases a with ⟨row, col⟩
    have ha_cell := hP.1 ha
    rw [mem_ferrers_cells] at ha_cell ⊢
    refine ⟨by simpa [partitionSubOne] using ha_cell.1, by lia, ?_⟩
    rw [partitionSubOne_getD] at ha_cell
    lia
  · intro x hx y hy hxy
    rw [addFirstColumnPlacement] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hxy rfl
    exact hP.2.1 a ha b hb hab
  · intro x hx y hy hxy
    rw [addFirstColumnPlacement] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    exact Nat.add_lt_add_right (hP.2.2 a ha b hb hxy) 1

/-- A shifted placement from `partitionSubOne lam` avoids the first column. -/
theorem addFirstColumnPlacement_avoids_firstColumn
    {lam : List ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (ferrers (partitionSubOne lam)).IsNonNestingPlacement P) :
    ∀ row, (row, 1) ∉ addFirstColumnPlacement P := by
  intro row hrow
  rw [addFirstColumnPlacement] at hrow
  rcases Finset.mem_image.mp hrow with ⟨a, ha, hmap⟩
  have hcol : a.2 + 1 = 1 := by
    simpa using congrArg (fun x : ℕ × ℕ => x.2) hmap
  have ha_cell := hP.1 ha
  rw [mem_ferrers_cells] at ha_cell
  lia

/-- Deleting the first column after adding it returns the original placement. -/
theorem deleteFirstColumnPlacement_addFirstColumnPlacement
    (P : Finset (ℕ × ℕ)) :
    deleteFirstColumnPlacement (addFirstColumnPlacement P) = P := by
  classical
  ext x
  constructor
  · intro hx
    rw [deleteFirstColumnPlacement, addFirstColumnPlacement] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    rcases Finset.mem_image.mp hy with ⟨a, ha, hay⟩
    subst y
    have hxa : x = a := by
      simpa using hxy.symm
    simpa [hxa] using ha
  · intro hx
    rw [deleteFirstColumnPlacement, addFirstColumnPlacement]
    refine Finset.mem_image.mpr ⟨(x.1, x.2 + 1), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · simp

/-- Adding back a deleted first column recovers a placement that avoided the
first column. -/
theorem addFirstColumnPlacement_deleteFirstColumnPlacement
    {P : Finset (ℕ × ℕ)} (hcol : ∀ a ∈ P, 1 < a.2) :
    addFirstColumnPlacement (deleteFirstColumnPlacement P) = P := by
  classical
  ext x
  constructor
  · intro hx
    rw [addFirstColumnPlacement, deleteFirstColumnPlacement] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    rcases Finset.mem_image.mp hy with ⟨a, ha, hay⟩
    subst y
    have hone : 1 ≤ a.2 := Nat.le_of_lt (hcol a ha)
    have hxa : x = a := by
      simpa [Nat.sub_add_cancel hone] using hxy.symm
    simpa [hxa] using ha
  · intro hx
    rw [addFirstColumnPlacement, deleteFirstColumnPlacement]
    refine Finset.mem_image.mpr ⟨(x.1, x.2 - 1), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · have hone : 1 ≤ x.2 := Nat.le_of_lt (hcol x hx)
      ext <;> simp [Nat.sub_add_cancel hone]

/-- Deleting the first column preserves cardinality for placements avoiding
that column. -/
theorem deleteFirstColumnPlacement_card
    {P : Finset (ℕ × ℕ)} (hcol : ∀ a ∈ P, 1 < a.2) :
    (deleteFirstColumnPlacement P).card = P.card := by
  classical
  rw [deleteFirstColumnPlacement]
  have hinj : Set.InjOn (fun a : ℕ × ℕ => (a.1, a.2 - 1)) ↑P := by
    intro a ha b hb hmap
    have hrow : a.1 = b.1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have hcol_sub : a.2 - 1 = b.2 - 1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.2) hmap
    have haone : 1 ≤ a.2 := Nat.le_of_lt (hcol a ha)
    have hbone : 1 ≤ b.2 := Nat.le_of_lt (hcol b hb)
    have hcol_eq : a.2 = b.2 := by
      calc
        a.2 = (a.2 - 1) + 1 := (Nat.sub_add_cancel haone).symm
        _ = (b.2 - 1) + 1 := by rw [hcol_sub]
        _ = b.2 := Nat.sub_add_cancel hbone
    exact Prod.ext hrow hcol_eq
  exact Finset.card_image_of_injOn hinj

/-- A first-column-free valid placement has every rook strictly after the first
column. -/
theorem one_lt_col_of_mem_withoutFirstColumn
    {lam : List ℕ} {P : Finset (ℕ × ℕ)}
    (hP : P ∈ nonNestingPlacementsWithoutFirstColumn lam) :
    ∀ a ∈ P, 1 < a.2 := by
  rw [mem_nonNestingPlacementsWithoutFirstColumn] at hP
  intro a ha
  have ha_cell := hP.1.1 ha
  rw [mem_ferrers_cells] at ha_cell
  have hcol_ne : a.2 ≠ 1 := by
    intro hcol
    exact hP.2 a.1 (by
      have ha_eq : (a.1, 1) = a := by
        ext <;> simp [hcol]
      simpa [ha_eq] using ha)
  exact lt_of_le_of_ne (Nat.succ_le_of_lt ha_cell.2.1) hcol_ne.symm

/-- Deleting the first column identifies the first-column-free placement slice
with placements on `partitionSubOne lam`. -/
theorem deleteFirstColumnPlacement_image_withoutFirstColumn (lam : List ℕ) :
    (nonNestingPlacementsWithoutFirstColumn lam).image deleteFirstColumnPlacement =
      (ferrers (partitionSubOne lam)).nonNestingPlacements := by
  classical
  ext Q
  constructor
  · intro hQ
    rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
    rw [mem_nonNestingPlacementsWithoutFirstColumn] at hP
    exact mem_nonNestingPlacements.mpr
      (deleteFirstColumnPlacement_isNonNestingPlacement hP.1 hP.2)
  · intro hQ
    have hQvalid := mem_nonNestingPlacements.mp hQ
    refine Finset.mem_image.mpr ⟨addFirstColumnPlacement Q, ?_, ?_⟩
    · rw [mem_nonNestingPlacementsWithoutFirstColumn]
      exact ⟨addFirstColumnPlacement_isNonNestingPlacement hQvalid,
        addFirstColumnPlacement_avoids_firstColumn hQvalid⟩
    · exact deleteFirstColumnPlacement_addFirstColumnPlacement Q

/-- Deleting the first column is injective on first-column-free placements. -/
theorem deleteFirstColumnPlacement_injOn_withoutFirstColumn (lam : List ℕ) :
    Set.InjOn deleteFirstColumnPlacement
      ↑(nonNestingPlacementsWithoutFirstColumn lam) := by
  intro P hP Q hQ hdel
  calc
    P = addFirstColumnPlacement (deleteFirstColumnPlacement P) :=
      (addFirstColumnPlacement_deleteFirstColumnPlacement
        (one_lt_col_of_mem_withoutFirstColumn hP)).symm
    _ = addFirstColumnPlacement (deleteFirstColumnPlacement Q) := by rw [hdel]
    _ = Q :=
      addFirstColumnPlacement_deleteFirstColumnPlacement
        (one_lt_col_of_mem_withoutFirstColumn hQ)

/-- The no-first-column contribution is the rook polynomial after deleting the
first column. -/
theorem sum_nonNestingPlacementsWithoutFirstColumn_eq_partitionSubOne
    (lam : List ℕ) :
    (nonNestingPlacementsWithoutFirstColumn lam).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        ferrersRookPolynomial (partitionSubOne lam) := by
  classical
  let S := nonNestingPlacementsWithoutFirstColumn lam
  let T := (ferrers (partitionSubOne lam)).nonNestingPlacements
  have himage : S.image deleteFirstColumnPlacement = T := by
    simpa [S, T] using deleteFirstColumnPlacement_image_withoutFirstColumn lam
  have hinj : Set.InjOn deleteFirstColumnPlacement ↑S := by
    simpa [S] using deleteFirstColumnPlacement_injOn_withoutFirstColumn lam
  have hsum_image :
      (S.image deleteFirstColumnPlacement).sum (fun Q => (X : ℝ[X]) ^ Q.card) =
        S.sum (fun P => (X : ℝ[X]) ^ (deleteFirstColumnPlacement P).card) := by
    simpa using
      (Finset.sum_image (s := S) (g := deleteFirstColumnPlacement)
        (f := fun Q => (X : ℝ[X]) ^ Q.card) hinj)
  calc
    S.sum (fun P => (X : ℝ[X]) ^ P.card)
        = S.sum (fun P => (X : ℝ[X]) ^ (deleteFirstColumnPlacement P).card) := by
          apply Finset.sum_congr rfl
          intro P hP
          rw [deleteFirstColumnPlacement_card
            (one_lt_col_of_mem_withoutFirstColumn (by simpa [S] using hP))]
    _ = T.sum (fun Q => (X : ℝ[X]) ^ Q.card) := by
          rw [← hsum_image, himage]
    _ = ferrersRookPolynomial (partitionSubOne lam) := by
          rw [ferrersRookPolynomial, rookPolynomial_eq_nonNestingPlacements_sum]

/-- After erasing a first-column rook, every remaining rook lies in a row above
it. -/
theorem row_lt_of_mem_erase_firstColumn
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} {i : ℕ}
    (hP : (ferrers lam).IsNonNestingPlacement P)
    (hfirst : (i, 1) ∈ P) {a : ℕ × ℕ}
    (ha : a ∈ P.erase (i, 1)) :
    a.1 < i := by
  have haP : a ∈ P := (Finset.mem_erase.mp ha).2
  have hane : a ≠ (i, 1) := (Finset.mem_erase.mp ha).1
  have ha_cell := hP.1 haP
  rw [mem_ferrers_cells] at ha_cell
  by_cases hlt : a.1 < i
  · exact hlt
  · have hi_le : i ≤ a.1 := le_of_not_gt hlt
    by_cases hrow : a.1 = i
    · have hrow_ne := hP.2.1 a haP (i, 1) hfirst hane
      exact (hrow_ne hrow).elim
    · have hi_lt : i < a.1 := lt_of_le_of_ne hi_le (fun h => hrow h.symm)
      have hcol := hP.2.2 (i, 1) hfirst a haP hi_lt
      exact (not_lt_of_ge (Nat.succ_le_of_lt ha_cell.2.1) hcol).elim

/-- After erasing a first-column rook, every remaining rook is strictly to the
right of the first column. -/
theorem one_lt_col_of_mem_erase_firstColumn
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} {i : ℕ}
    (hP : (ferrers lam).IsNonNestingPlacement P)
    (hfirst : (i, 1) ∈ P) :
    ∀ a ∈ P.erase (i, 1), 1 < a.2 := by
  intro a ha
  have haP : a ∈ P := (Finset.mem_erase.mp ha).2
  have hrow := row_lt_of_mem_erase_firstColumn hP hfirst ha
  exact hP.2.2 a haP (i, 1) hfirst hrow

/-- If a valid Ferrers placement contains the first-column rook `(i,1)`, then
erasing it and shifting columns left gives a placement on the first `i` rows of
`partitionSubOne lam`. -/
theorem firstColumnRemainder_isNonNestingPlacement
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} {i : ℕ}
    (hP : (ferrers lam).IsNonNestingPlacement P)
    (hfirst : (i, 1) ∈ P) :
    (ferrers (partitionPrefix (partitionSubOne lam) i)).IsNonNestingPlacement
      (firstColumnRemainder i P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [firstColumnRemainder] at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases a with ⟨row, col⟩
    have haP : (row, col) ∈ P := (Finset.mem_erase.mp ha).2
    have ha_cell := hP.1 haP
    rw [mem_ferrers_cells] at ha_cell ⊢
    have hrow_lt := row_lt_of_mem_erase_firstColumn hP hfirst ha
    have hcol_gt := one_lt_col_of_mem_erase_firstColumn hP hfirst (row, col) ha
    refine ⟨?_, Nat.sub_pos_of_lt hcol_gt, ?_⟩
    · rw [partitionPrefix_length]
      exact lt_min hrow_lt (by simpa [partitionSubOne] using ha_cell.1)
    · rw [partitionPrefix_getD_of_lt hrow_lt, partitionSubOne_getD]
      exact Nat.sub_le_sub_right ha_cell.2.2 1
  · intro x hx y hy hxy
    rw [firstColumnRemainder] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have haP : a ∈ P := (Finset.mem_erase.mp ha).2
    have hbP : b ∈ P := (Finset.mem_erase.mp hb).2
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hxy rfl
    exact hP.2.1 a haP b hbP hab
  · intro x hx y hy hxy
    rw [firstColumnRemainder] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have haP : a ∈ P := (Finset.mem_erase.mp ha).2
    have hbP : b ∈ P := (Finset.mem_erase.mp hb).2
    have hcol := hP.2.2 a haP b hbP hxy
    have hb_cell := hP.1 hbP
    rw [mem_ferrers_cells] at hb_cell
    exact Nat.sub_lt_sub_right hb_cell.2.1 hcol

/-- Reinsert a first-column rook and shift a valid remainder right by one
column. -/
theorem firstColumnExtension_isNonNestingPlacement
    {lam : List ℕ} {Q : Finset (ℕ × ℕ)} {i : ℕ}
    (hQ :
      (ferrers (partitionPrefix (partitionSubOne lam) i)).IsNonNestingPlacement Q)
    (hfirst_cell : (i, 1) ∈ (ferrers lam).cells) :
    (ferrers lam).IsNonNestingPlacement (firstColumnExtension i Q) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [firstColumnExtension] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hfirst_cell
    · rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases a with ⟨row, col⟩
      have ha_cell := hQ.1 ha
      rw [mem_ferrers_cells] at ha_cell ⊢
      have hrow_pair : row < i ∧ row < lam.length := by
        have hlen := ha_cell.1
        rw [partitionPrefix_length] at hlen
        exact lt_min_iff.mp (by simpa [partitionSubOne] using hlen)
      refine ⟨hrow_pair.2, by lia, ?_⟩
      rw [partitionPrefix_getD_of_lt hrow_pair.1, partitionSubOne_getD] at ha_cell
      lia
  · intro x hx y hy hxy
    rw [firstColumnExtension] at hx hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hxy rfl).elim
      · rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        have hb_cell := hQ.1 hb
        rw [mem_ferrers_cells] at hb_cell
        have hrow_lt : b.1 < i := by
          have hlen := hb_cell.1
          rw [partitionPrefix_length] at hlen
          exact (lt_min_iff.mp (by simpa [partitionSubOne] using hlen)).1
        exact ne_of_gt hrow_lt
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        have ha_cell := hQ.1 ha
        rw [mem_ferrers_cells] at ha_cell
        have hrow_lt : a.1 < i := by
          have hlen := ha_cell.1
          rw [partitionPrefix_length] at hlen
          exact (lt_min_iff.mp (by simpa [partitionSubOne] using hlen)).1
        exact ne_of_lt hrow_lt
      · rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        have hab : a ≠ b := by
          intro hab
          subst b
          exact hxy rfl
        exact hQ.2.1 a ha b hb hab
  · intro x hx y hy hxy
    rw [firstColumnExtension] at hx hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (Nat.lt_irrefl i hxy).elim
      · rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        have hb_cell := hQ.1 hb
        rw [mem_ferrers_cells] at hb_cell
        have hrow_lt : b.1 < i := by
          have hlen := hb_cell.1
          rw [partitionPrefix_length] at hlen
          exact (lt_min_iff.mp (by simpa [partitionSubOne] using hlen)).1
        exact (not_lt_of_ge (Nat.le_of_lt hrow_lt) hxy).elim
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        have ha_cell := hQ.1 ha
        rw [mem_ferrers_cells] at ha_cell
        exact Nat.succ_lt_succ ha_cell.2.1
      · rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        exact Nat.add_lt_add_right (hQ.2.2 a ha b hb hxy) 1

/-- Removing a first-column rook and shifting columns preserves the cardinality
of the remaining placement. -/
theorem firstColumnRemainder_card_add_one
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} {i : ℕ}
    (hP : (ferrers lam).IsNonNestingPlacement P)
    (hfirst : (i, 1) ∈ P) :
    (firstColumnRemainder i P).card + 1 = P.card := by
  classical
  rw [firstColumnRemainder]
  have hinj :
      Set.InjOn (fun a : ℕ × ℕ => (a.1, a.2 - 1)) ↑(P.erase (i, 1)) := by
    intro a ha b hb hmap
    have hrow : a.1 = b.1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have hcol_sub : a.2 - 1 = b.2 - 1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.2) hmap
    have haone : 1 ≤ a.2 :=
      Nat.le_of_lt (one_lt_col_of_mem_erase_firstColumn hP hfirst a ha)
    have hbone : 1 ≤ b.2 :=
      Nat.le_of_lt (one_lt_col_of_mem_erase_firstColumn hP hfirst b hb)
    have hcol : a.2 = b.2 := by
      calc
        a.2 = (a.2 - 1) + 1 := (Nat.sub_add_cancel haone).symm
        _ = (b.2 - 1) + 1 := by rw [hcol_sub]
        _ = b.2 := Nat.sub_add_cancel hbone
    exact Prod.ext hrow hcol
  rw [Finset.card_image_of_injOn hinj]
  exact Finset.card_erase_add_one hfirst

/-- Shifting a valid fixed-row remainder right and inserting the first-column
rook increases cardinality by one. -/
theorem firstColumnExtension_card
    {lam : List ℕ} {Q : Finset (ℕ × ℕ)} {i : ℕ}
    (hQ :
      (ferrers (partitionPrefix (partitionSubOne lam) i)).IsNonNestingPlacement Q) :
    (firstColumnExtension i Q).card = Q.card + 1 := by
  classical
  rw [firstColumnExtension]
  have hnot : (i, 1) ∉ Q.image fun a => (a.1, a.2 + 1) := by
    intro hi
    rcases Finset.mem_image.mp hi with ⟨a, ha, hmap⟩
    have hrow : a.1 = i := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have ha_cell := hQ.1 ha
    rw [mem_ferrers_cells] at ha_cell
    have hrow_lt : a.1 < i := by
      have hlen := ha_cell.1
      rw [partitionPrefix_length] at hlen
      exact (lt_min_iff.mp (by simpa [partitionSubOne] using hlen)).1
    exact (ne_of_lt hrow_lt hrow).elim
  have hinj :
      Set.InjOn (fun a : ℕ × ℕ => (a.1, a.2 + 1)) ↑Q := by
    intro a _ha b _hb hmap
    have hrow : a.1 = b.1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have hcol_add : a.2 + 1 = b.2 + 1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.2) hmap
    exact Prod.ext hrow (Nat.add_right_cancel hcol_add)
  rw [Finset.card_insert_eq_ite, if_neg hnot, Finset.card_image_of_injOn hinj]

/-- The reinserted first-column rook is not already present in a shifted valid
remainder. -/
theorem firstColumnRook_not_mem_addFirstColumnPlacement
    {lam : List ℕ} {Q : Finset (ℕ × ℕ)} {i : ℕ}
    (hQ :
      (ferrers (partitionPrefix (partitionSubOne lam) i)).IsNonNestingPlacement Q) :
    (i, 1) ∉ addFirstColumnPlacement Q := by
  intro hi
  rw [addFirstColumnPlacement] at hi
  rcases Finset.mem_image.mp hi with ⟨a, ha, hmap⟩
  have hrow : a.1 = i := by
    simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
  have ha_cell := hQ.1 ha
  rw [mem_ferrers_cells] at ha_cell
  have hrow_lt : a.1 < i := by
    have hlen := ha_cell.1
    rw [partitionPrefix_length] at hlen
    exact (lt_min_iff.mp (by simpa [partitionSubOne] using hlen)).1
  exact (ne_of_lt hrow_lt hrow).elim

/-- Taking the remainder of an extended fixed-row placement recovers the
original remainder. -/
theorem firstColumnRemainder_firstColumnExtension
    {lam : List ℕ} {Q : Finset (ℕ × ℕ)} {i : ℕ}
    (hQ :
      (ferrers (partitionPrefix (partitionSubOne lam) i)).IsNonNestingPlacement Q) :
    firstColumnRemainder i (firstColumnExtension i Q) = Q := by
  rw [firstColumnRemainder, firstColumnExtension]
  rw [Finset.erase_insert (by
    simpa [addFirstColumnPlacement]
      using firstColumnRook_not_mem_addFirstColumnPlacement hQ)]
  simpa [addFirstColumnPlacement, deleteFirstColumnPlacement]
    using deleteFirstColumnPlacement_addFirstColumnPlacement Q

/-- Extending the fixed-row remainder of a valid placement containing `(i,1)`
recovers the original placement. -/
theorem firstColumnExtension_firstColumnRemainder
    {lam : List ℕ} {P : Finset (ℕ × ℕ)} {i : ℕ}
    (hP : (ferrers lam).IsNonNestingPlacement P)
    (hfirst : (i, 1) ∈ P) :
    firstColumnExtension i (firstColumnRemainder i P) = P := by
  rw [firstColumnExtension, firstColumnRemainder]
  have hcol : ∀ a ∈ P.erase (i, 1), 1 < a.2 :=
    one_lt_col_of_mem_erase_firstColumn hP hfirst
  have hrecover :
      ((P.erase (i, 1)).image fun a => (a.1, a.2 - 1)).image
          (fun a => (a.1, a.2 + 1)) =
        P.erase (i, 1) := by
    simpa [addFirstColumnPlacement, deleteFirstColumnPlacement]
      using addFirstColumnPlacement_deleteFirstColumnPlacement hcol
  rw [hrecover]
  exact Finset.insert_erase hfirst

/-- On placements containing a fixed first-column rook, taking the shifted
remainder is injective. -/
theorem firstColumnRemainder_injOn_nonNestingPlacementsWithCell
    {lam : List ℕ} {i : ℕ} :
    Set.InjOn (firstColumnRemainder i)
      ↑((ferrers lam).nonNestingPlacementsWithCell (i, 1)) := by
  intro P hP Q hQ hrem
  change P ∈ (ferrers lam).nonNestingPlacementsWithCell (i, 1) at hP
  change Q ∈ (ferrers lam).nonNestingPlacementsWithCell (i, 1) at hQ
  rw [mem_nonNestingPlacementsWithCell] at hP hQ
  calc
    P = firstColumnExtension i (firstColumnRemainder i P) :=
      (firstColumnExtension_firstColumnRemainder hP.1 hP.2).symm
    _ = firstColumnExtension i (firstColumnRemainder i Q) := by rw [hrem]
    _ = Q := firstColumnExtension_firstColumnRemainder hQ.1 hQ.2

/-- For a fixed first-column cell `(i,1)`, shifted remainders of valid
placements containing that cell are exactly the valid placements on the first
`i` rows of `partitionSubOne lam`. -/
theorem firstColumnRemainder_image_nonNestingPlacementsWithCell
    {lam : List ℕ} {i : ℕ}
    (hfirst_cell : (i, 1) ∈ (ferrers lam).cells) :
    ((ferrers lam).nonNestingPlacementsWithCell (i, 1)).image
      (firstColumnRemainder i) =
        (ferrers (partitionPrefix (partitionSubOne lam) i)).nonNestingPlacements := by
  classical
  ext Q
  constructor
  · intro hQ
    rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
    rw [mem_nonNestingPlacementsWithCell] at hP
    exact mem_nonNestingPlacements.mpr
      (firstColumnRemainder_isNonNestingPlacement hP.1 hP.2)
  · intro hQ
    have hQvalid := mem_nonNestingPlacements.mp hQ
    refine Finset.mem_image.mpr ⟨firstColumnExtension i Q, ?_, ?_⟩
    · rw [mem_nonNestingPlacementsWithCell]
      exact ⟨firstColumnExtension_isNonNestingPlacement hQvalid hfirst_cell,
        by simp [firstColumnExtension]⟩
    · exact firstColumnRemainder_firstColumnExtension hQvalid

/-- The contribution of placements containing a fixed first-column rook is `X`
times the rook polynomial of the shifted prefix board. -/
theorem sum_nonNestingPlacementsWithFirstColumnCell_eq_mul_partitionPrefix
    {lam : List ℕ} {i : ℕ}
    (hfirst_cell : (i, 1) ∈ (ferrers lam).cells) :
    ((ferrers lam).nonNestingPlacementsWithCell (i, 1)).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        X * ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i) := by
  classical
  let S := (ferrers lam).nonNestingPlacementsWithCell (i, 1)
  let T := (ferrers (partitionPrefix (partitionSubOne lam) i)).nonNestingPlacements
  have himage : S.image (firstColumnRemainder i) = T := by
    simpa [S, T]
      using firstColumnRemainder_image_nonNestingPlacementsWithCell hfirst_cell
  have hinj : Set.InjOn (firstColumnRemainder i) ↑S := by
    simpa [S] using
      (firstColumnRemainder_injOn_nonNestingPlacementsWithCell (lam := lam)
        (i := i))
  have hsum_image :
      (S.image (firstColumnRemainder i)).sum (fun Q => (X : ℝ[X]) ^ Q.card) =
        S.sum (fun P => (X : ℝ[X]) ^ (firstColumnRemainder i P).card) := by
    simpa using
      (Finset.sum_image (s := S) (g := firstColumnRemainder i)
        (f := fun Q => (X : ℝ[X]) ^ Q.card) hinj)
  calc
    S.sum (fun P => (X : ℝ[X]) ^ P.card)
        = S.sum (fun P => X * X ^ (firstColumnRemainder i P).card) := by
          apply Finset.sum_congr rfl
          intro P hP
          have hPvalid : (ferrers lam).IsNonNestingPlacement P ∧ (i, 1) ∈ P := by
            simpa [S] using mem_nonNestingPlacementsWithCell.mp hP
          have hcard := firstColumnRemainder_card_add_one hPvalid.1 hPvalid.2
          rw [← hcard, pow_succ]
          ring
    _ = X * S.sum (fun P => X ^ (firstColumnRemainder i P).card) := by
          rw [Finset.mul_sum]
    _ = X * T.sum (fun Q => X ^ Q.card) := by
          rw [← hsum_image, himage]
    _ = X * ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i) := by
          rw [ferrersRookPolynomial, rookPolynomial_eq_nonNestingPlacements_sum]

/-- In an integer partition, every row index in `firstColumnCells` is a genuine
Ferrers-board first-column cell. -/
theorem firstColumn_mem_ferrers_of_isIntegerPartition
    {lam : List ℕ} (hpart : IsIntegerPartition lam) {i : ℕ}
    (hi : i < lam.length) :
    (i, 1) ∈ (ferrers lam).cells := by
  rw [mem_ferrers_cells]
  have hpos : 0 < lam[i] := hpart.2 lam[i] (List.get_mem lam ⟨i, hi⟩)
  have hget : lam.getD i 0 = lam[i] := List.getD_eq_getElem lam 0 hi
  exact ⟨hi, by norm_num, by rw [hget]; exact Nat.succ_le_of_lt hpos⟩

/-- Summing the fixed first-column contributions over all first-column cells
gives the first-column term in Braun--Jal's deletion recurrence. -/
theorem sum_firstColumnCells_nonNestingPlacementsWithCell_eq_mul_sum
    (lam : List ℕ) (hpart : IsIntegerPartition lam) :
    (firstColumnCells lam).sum (fun a =>
      ((ferrers lam).nonNestingPlacementsWithCell a).sum
        (fun P => (X : ℝ[X]) ^ P.card)) =
      X * ((List.range lam.length).map fun i =>
        ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i)).sum := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => (i, 1)) ↑(Finset.range lam.length) := by
    intro a _ha b _hb h
    simpa using congrArg (fun x : ℕ × ℕ => x.1) h
  rw [firstColumnCells, Finset.sum_image hinj]
  calc
    (Finset.range lam.length).sum (fun i =>
        ((ferrers lam).nonNestingPlacementsWithCell (i, 1)).sum
          (fun P => (X : ℝ[X]) ^ P.card))
        = (Finset.range lam.length).sum (fun i =>
            X * ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact sum_nonNestingPlacementsWithFirstColumnCell_eq_mul_partitionPrefix
            (firstColumn_mem_ferrers_of_isIntegerPartition hpart
              (Finset.mem_range.mp hi))
    _ = (List.map (fun i =>
          X * ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i))
          (List.range lam.length)).sum := by
          rw [← List.sum_toFinset (fun i =>
            X * ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i))
              List.nodup_range]
          congr 1
          ext i
          simp
    _ = X * ((List.range lam.length).map fun i =>
          ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i)).sum := by
          exact List.sum_map_mul_left (List.range lam.length)
            (fun i => ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i)) X

/-- Braun--Jal Proposition 3.2 for the concrete finite Ferrers-board
non-nesting rook-polynomial model. -/
theorem ferrersFirstColumnDeletionStatement_holds :
    ferrersFirstColumnDeletionStatement := by
  intro lam hpart
  calc
    ferrersRookPolynomial lam
        = ((ferrers lam).nonNestingPlacements).sum
            (fun P => (X : ℝ[X]) ^ P.card) := by
          rw [ferrersRookPolynomial, rookPolynomial_eq_nonNestingPlacements_sum]
    _ = (nonNestingPlacementsWithoutFirstColumn lam).sum
          (fun P => (X : ℝ[X]) ^ P.card) +
        (firstColumnCells lam).sum (fun a =>
          ((ferrers lam).nonNestingPlacementsWithCell a).sum
            (fun P => (X : ℝ[X]) ^ P.card)) :=
          sum_nonNestingPlacements_eq_withoutFirstColumn_add_withFirstColumn lam
    _ = ferrersRookPolynomial (partitionSubOne lam) +
        (firstColumnCells lam).sum (fun a =>
          ((ferrers lam).nonNestingPlacementsWithCell a).sum
            (fun P => (X : ℝ[X]) ^ P.card)) := by
          rw [sum_nonNestingPlacementsWithoutFirstColumn_eq_partitionSubOne]
    _ = ferrersRookPolynomial (partitionSubOne lam) +
        X * ((List.range lam.length).map fun i =>
          ferrersRookPolynomial (partitionPrefix (partitionSubOne lam) i)).sum := by
          rw [sum_firstColumnCells_nonNestingPlacementsWithCell_eq_mul_sum lam hpart]


end FiniteSkewBoard

/-- The finite-board definition of `G_n` satisfies the truncated-staircase
interface. -/
theorem FiniteSkewBoard.auxiliaryG_matchesTruncatedStaircases :
    AuxiliaryGMatchesTruncatedStaircasesStatement
      FiniteSkewBoard.truncatedStaircaseRookPolynomial
      FiniteSkewBoard.auxiliaryG := by
  intro n
  rfl


end GeneralizedSnakePosets
end RealRooted
