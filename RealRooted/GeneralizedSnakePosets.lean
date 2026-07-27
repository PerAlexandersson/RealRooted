import RealRooted.GeneralizedSnakePosets.SnakeReachability
import RealRooted.GeneralizedSnakePosets.SquarecaseModel

/-!
# Generalized snake poset statement interfaces

This file records the first Lean-facing interface for Braun--Jal,
*Order polytopes of generalized snake posets are h^*-real-rooted*,
arXiv:2607.00922v1.

The immediate target is Theorem 4.1 of the paper: if `w` is a generalized
snake word of length at least one and `w'` is obtained by deleting the final
letter, then the non-nesting rook polynomial `M_{epsilon w}` is real-rooted
and `M_{epsilon w'}` interlaces `M_{epsilon w}`.

The board, poset, and order-polytope encodings are intentionally left as
interfaces in this first module.  The recurrence/Narayana proof route should
later refine these statement interfaces rather than replacing them with a
one-off coefficient argument.
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

/-- A finite list sum of nonnegative-coefficient polynomials has nonnegative
coefficients. -/
private lemma listSum_hasNonnegCoeffs {ps : List ℝ[X]}
    (hps : ∀ p ∈ ps, HasNonnegCoeffs p) :
    HasNonnegCoeffs ps.sum := by
  induction ps with
  | nil =>
      simp [HasNonnegCoeffs]
  | cons p ps ih =>
      intro k
      have hp : HasNonnegCoeffs p := hps p (by simp)
      have htail : ∀ q ∈ ps, HasNonnegCoeffs q := by
        intro q hq
        exact hps q (by simp [hq])
      simpa using add_nonneg (hp k) (ih htail k)

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

/-- Membership in the bottom row of `mu_{n,i+1}`. -/
@[simp] theorem bottomRow_mem_truncatedStaircase_cells {n i c : ℕ} :
    (i, c) ∈ (truncatedStaircase n (i + 1)).cells ↔ c < n - i := by
  simp

/-- The cells in the bottom row of `mu_{n,i+1}`. -/
def bottomRowCells (n i : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n - i)).image fun c => (i, c)

/-- Membership in the bottom-row cell set, in column coordinates. -/
@[simp] theorem bottomRowCell_mem_bottomRowCells {n i c : ℕ} :
    (i, c) ∈ bottomRowCells n i ↔ c < n - i := by
  classical
  rw [bottomRowCells, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hc : d = c := by
      simpa using congrArg (fun x : ℕ × ℕ => x.2) hdc
    simpa [hc] using hd
  · intro hc
    exact ⟨c, by simpa using hc, rfl⟩

/-- Membership in the bottom-row cell set, for arbitrary cells. -/
@[simp] theorem mem_bottomRowCells {n i : ℕ} {a : ℕ × ℕ} :
    a ∈ bottomRowCells n i ↔ a.1 = i ∧ a.2 < n - i := by
  classical
  rw [bottomRowCells, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨rfl, by simpa using hc⟩
  · rintro ⟨hrow, hcol⟩
    refine ⟨a.2, by simpa using hcol, ?_⟩
    ext <;> simp [hrow]

/-- The non-nesting rook polynomial of the truncated staircase `mu_{n,i}`. -/
def truncatedStaircaseRookPolynomial (n i : ℕ) : ℝ[X] :=
  (truncatedStaircase n i).rookPolynomial

/-- Shift every column of a finite cell set down by `c + 1`. -/
def shiftColumnsAfter (c : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  P.image fun a => (a.1, a.2 - (c + 1))

/-- Remove a bottom-row rook `(i,c)` and shift the remaining columns down by
`c + 1`. -/
def bottomRookRemainder (i c : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  shiftColumnsAfter c (P.erase (i, c))

/-- Shift every column of a finite cell set up by `c + 1`. -/
def unshiftColumnsAfter (c : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  P.image fun a => (a.1, a.2 + (c + 1))

/-- Insert a bottom-row rook `(i,c)` and shift the remaining columns up by
`c + 1`. -/
def bottomRookExtension (i c : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  insert (i, c) (unshiftColumnsAfter c P)

/-- Any rook left after removing a bottom-row rook from a valid placement lies
strictly above the bottom row. -/
theorem row_lt_of_mem_erase_bottomRook
    {n i c : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P)
    (hbottom : (i, c) ∈ P) {a : ℕ × ℕ}
    (ha : a ∈ P.erase (i, c)) :
    a.1 < i := by
  have haP : a ∈ P := (Finset.mem_erase.mp ha).2
  have ha_cell := hP.1 haP
  rw [mem_truncatedStaircase_cells] at ha_cell
  have hrow_le : a.1 ≤ i := Nat.lt_succ_iff.mp ha_cell.1
  have hrow_ne : a.1 ≠ i := by
    exact hP.2.1 a haP (i, c) hbottom (Finset.mem_erase.mp ha).1
  exact lt_of_le_of_ne hrow_le hrow_ne

/-- Any rook left after removing a bottom-row rook from a valid placement lies
strictly to the right of the removed rook. -/
theorem bottom_col_lt_of_mem_erase_bottomRook
    {n i c : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P)
    (hbottom : (i, c) ∈ P) {a : ℕ × ℕ}
    (ha : a ∈ P.erase (i, c)) :
    c < a.2 :=
  hP.2.2 a (Finset.mem_erase.mp ha).2 (i, c) hbottom
    (row_lt_of_mem_erase_bottomRook hP hbottom ha)

/-- If a valid placement in `mu_{n,i+1}` contains the bottom-row rook `(i,c)`,
then removing that rook and shifting all remaining columns down by `c+1`
gives a valid placement in `mu_{n-c-1,i}`. -/
theorem bottomRookRemainder_isNonNestingPlacement
    {n i c : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P)
    (hbottom : (i, c) ∈ P) :
    (truncatedStaircase (n - c - 1) i).IsNonNestingPlacement
      (bottomRookRemainder i c P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [bottomRookRemainder, shiftColumnsAfter] at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases a with ⟨row, col⟩
    have haP : (row, col) ∈ P := (Finset.mem_erase.mp ha).2
    have ha_cell := hP.1 haP
    rw [mem_truncatedStaircase_cells] at ha_cell ⊢
    have hrow : row < i := row_lt_of_mem_erase_bottomRook hP hbottom ha
    have hcol_gt : c < col := bottom_col_lt_of_mem_erase_bottomRook hP hbottom ha
    have hcol_row : col + row < n := Nat.add_lt_of_lt_sub ha_cell.2
    refine ⟨hrow, ?_⟩
    lia
  · intro x hx y hy hxy
    rw [bottomRookRemainder, shiftColumnsAfter] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    intro hrow
    have haP : a ∈ P := (Finset.mem_erase.mp ha).2
    have hbP : b ∈ P := (Finset.mem_erase.mp hb).2
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hxy rfl
    exact hP.2.1 a haP b hbP hab hrow
  · intro x hx y hy hxy
    rw [bottomRookRemainder, shiftColumnsAfter] at hx hy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have haP : a ∈ P := (Finset.mem_erase.mp ha).2
    have hbP : b ∈ P := (Finset.mem_erase.mp hb).2
    have hcol := hP.2.2 a haP b hbP hxy
    have hb_col_gt : c < b.2 := bottom_col_lt_of_mem_erase_bottomRook hP hbottom hb
    exact Nat.sub_lt_sub_right (Nat.succ_le_of_lt hb_col_gt) hcol

/-- Removing a bottom-row rook and shifting columns preserves the cardinality
of the remaining placement. -/
theorem bottomRookRemainder_card_add_one
    {n i c : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P)
    (hbottom : (i, c) ∈ P) :
    (bottomRookRemainder i c P).card + 1 = P.card := by
  classical
  rw [bottomRookRemainder, shiftColumnsAfter]
  have hinj :
      Set.InjOn (fun a : ℕ × ℕ => (a.1, a.2 - (c + 1)))
        ↑(P.erase (i, c)) := by
    intro a ha b hb hmap
    have hrow : a.1 = b.1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have hcol_sub : a.2 - (c + 1) = b.2 - (c + 1) := by
      simpa using congrArg (fun x : ℕ × ℕ => x.2) hmap
    have hac : c < a.2 := bottom_col_lt_of_mem_erase_bottomRook hP hbottom ha
    have hbc : c < b.2 := bottom_col_lt_of_mem_erase_bottomRook hP hbottom hb
    have hcol : a.2 = b.2 := by
      have hac_le : c + 1 ≤ a.2 := Nat.succ_le_of_lt hac
      have hbc_le : c + 1 ≤ b.2 := Nat.succ_le_of_lt hbc
      calc
        a.2 = (a.2 - (c + 1)) + (c + 1) := (Nat.sub_add_cancel hac_le).symm
        _ = (b.2 - (c + 1)) + (c + 1) := by rw [hcol_sub]
        _ = b.2 := Nat.sub_add_cancel hbc_le
    exact Prod.ext hrow hcol
  rw [Finset.card_image_of_injOn hinj]
  exact Finset.card_erase_add_one hbottom

/-- A valid placement in `mu_{n,i}` is also valid in `mu_{n,i+1}`. -/
theorem truncatedStaircase_isNonNestingPlacement_succ
    {n i : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n i).IsNonNestingPlacement P) :
    (truncatedStaircase n (i + 1)).IsNonNestingPlacement P := by
  refine ⟨?_, hP.2.1, hP.2.2⟩
  intro a ha
  have ha_cell := hP.1 ha
  rw [mem_truncatedStaircase_cells] at ha_cell ⊢
  exact ⟨Nat.lt_trans ha_cell.1 (Nat.lt_succ_self i), ha_cell.2⟩

/-- A valid placement in `mu_{n,i+1}` with no bottom-row rook is already a
valid placement in `mu_{n,i}`. -/
theorem truncatedStaircase_isNonNestingPlacement_of_succ_of_no_bottom
    {n i : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P)
    (hno_bottom : ∀ c, (i, c) ∉ P) :
    (truncatedStaircase n i).IsNonNestingPlacement P := by
  refine ⟨?_, hP.2.1, hP.2.2⟩
  intro a ha
  have ha_cell := hP.1 ha
  rw [mem_truncatedStaircase_cells] at ha_cell ⊢
  refine ⟨?_, ha_cell.2⟩
  have hrow_le : a.1 ≤ i := Nat.lt_succ_iff.mp ha_cell.1
  have hrow_ne : a.1 ≠ i := by
    intro hrow
    have hcell : (i, a.2) = a := by
      ext <;> simp [hrow]
    exact hno_bottom a.2 (by simpa [hcell] using ha)
  exact lt_of_le_of_ne hrow_le hrow_ne

/-- Valid placements in `mu_{n,i+1}` with no bottom-row rook. -/
def nonNestingPlacementsWithoutBottomRow (n i : ℕ) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact (truncatedStaircase n (i + 1)).nonNestingPlacements.filter fun P =>
    ∀ c, (i, c) ∉ P

/-- Membership in the no-bottom-row placement slice. -/
@[simp] theorem mem_nonNestingPlacementsWithoutBottomRow
    {n i : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ nonNestingPlacementsWithoutBottomRow n i ↔
      (truncatedStaircase n (i + 1)).IsNonNestingPlacement P ∧
        ∀ c, (i, c) ∉ P := by
  classical
  simp [nonNestingPlacementsWithoutBottomRow]

/-- The no-bottom-row slice in `mu_{n,i+1}` is exactly the placement set for
`mu_{n,i}`. -/
theorem nonNestingPlacementsWithoutBottomRow_eq_nonNestingPlacements
    (n i : ℕ) :
    nonNestingPlacementsWithoutBottomRow n i =
      (truncatedStaircase n i).nonNestingPlacements := by
  classical
  ext P
  rw [mem_nonNestingPlacementsWithoutBottomRow, mem_nonNestingPlacements]
  constructor
  · intro h
    exact truncatedStaircase_isNonNestingPlacement_of_succ_of_no_bottom h.1 h.2
  · intro hP
    refine ⟨truncatedStaircase_isNonNestingPlacement_succ hP, ?_⟩
    intro c hc
    have hcell := hP.1 hc
    rw [mem_truncatedStaircase_cells] at hcell
    exact (Nat.lt_irrefl i hcell.1).elim

/-- The contribution of placements with no bottom-row rook is the rook
polynomial of `mu_{n,i}`. -/
theorem sum_nonNestingPlacementsWithoutBottomRow_eq_truncatedStaircaseRookPolynomial
    (n i : ℕ) :
    (nonNestingPlacementsWithoutBottomRow n i).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        truncatedStaircaseRookPolynomial n i := by
  rw [nonNestingPlacementsWithoutBottomRow_eq_nonNestingPlacements,
    truncatedStaircaseRookPolynomial, rookPolynomial_eq_nonNestingPlacements_sum]

/-- Valid placements in `mu_{n,i+1}` with a bottom-row rook. -/
def nonNestingPlacementsWithBottomRow (n i : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (bottomRowCells n i).biUnion fun a =>
    (truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell a

/-- Membership in the bottom-row placement slice. -/
@[simp] theorem mem_nonNestingPlacementsWithBottomRow
    {n i : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ nonNestingPlacementsWithBottomRow n i ↔
      (truncatedStaircase n (i + 1)).IsNonNestingPlacement P ∧
        ∃ a ∈ bottomRowCells n i, a ∈ P := by
  classical
  rw [nonNestingPlacementsWithBottomRow, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hP⟩
    rw [mem_nonNestingPlacementsWithCell] at hP
    exact ⟨hP.1, ⟨a, ha, hP.2⟩⟩
  · rintro ⟨hP, a, ha, haP⟩
    exact ⟨a, ha, mem_nonNestingPlacementsWithCell.mpr ⟨hP, haP⟩⟩

/-- The fixed bottom-row placement slices are pairwise disjoint. -/
theorem pairwiseDisjoint_nonNestingPlacementsWithCell_bottomRow (n i : ℕ) :
    (↑(bottomRowCells n i) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun a => (truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell a) := by
  classical
  intro a ha b hb hne
  change Disjoint ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell a)
    ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell b)
  rw [Finset.disjoint_iff_ne]
  intro P hPa Q hQ hPQ
  rw [mem_nonNestingPlacementsWithCell] at hPa hQ
  subst Q
  have hrow_ne := hPa.1.2.1 a hPa.2 b hQ.2 hne
  have ha_row : a.1 = i := (mem_bottomRowCells.mp ha).1
  have hb_row : b.1 = i := (mem_bottomRowCells.mp hb).1
  exact hrow_ne (by rw [ha_row, hb_row])

/-- The no-bottom-row and with-bottom-row placement slices are disjoint. -/
theorem disjoint_nonNestingPlacementsWithoutBottomRow_withBottomRow
    (n i : ℕ) :
    Disjoint (nonNestingPlacementsWithoutBottomRow n i)
      (nonNestingPlacementsWithBottomRow n i) := by
  classical
  rw [Finset.disjoint_left]
  intro P hP hbottom
  rw [mem_nonNestingPlacementsWithoutBottomRow] at hP
  rw [mem_nonNestingPlacementsWithBottomRow] at hbottom
  rcases hbottom.2 with ⟨a, ha, haP⟩
  have hrow : a.1 = i := (mem_bottomRowCells.mp ha).1
  have hcell : (i, a.2) = a := by
    ext <;> simp [hrow]
  exact hP.2 a.2 (by simpa [hcell] using haP)

/-- Valid placements in `mu_{n,i+1}` split into no-bottom-row placements and
placements with a bottom-row rook. -/
theorem union_nonNestingPlacementsWithoutBottomRow_withBottomRow
    (n i : ℕ) :
    nonNestingPlacementsWithoutBottomRow n i ∪
        nonNestingPlacementsWithBottomRow n i =
      (truncatedStaircase n (i + 1)).nonNestingPlacements := by
  classical
  ext P
  rw [Finset.mem_union, mem_nonNestingPlacementsWithoutBottomRow,
    mem_nonNestingPlacementsWithBottomRow, mem_nonNestingPlacements]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hP
    by_cases hbottom : ∃ a ∈ bottomRowCells n i, a ∈ P
    · exact Or.inr ⟨hP, hbottom⟩
    · left
      refine ⟨hP, ?_⟩
      intro c hc
      have hcell := hP.1 hc
      rw [bottomRow_mem_truncatedStaircase_cells] at hcell
      exact hbottom ⟨(i, c), by simpa using hcell, hc⟩

/-- The sum over all placements with a bottom-row rook is the sum of the
fixed-bottom-row slices. -/
theorem sum_nonNestingPlacementsWithBottomRow
    (n i : ℕ) :
    (nonNestingPlacementsWithBottomRow n i).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        (bottomRowCells n i).sum (fun a =>
          ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell a).sum
            (fun P => (X : ℝ[X]) ^ P.card)) := by
  classical
  rw [nonNestingPlacementsWithBottomRow]
  exact Finset.sum_biUnion
    (pairwiseDisjoint_nonNestingPlacementsWithCell_bottomRow n i)

/-- The sum over all placements in `mu_{n,i+1}` splits into the no-bottom-row
slice plus the bottom-row slices. -/
theorem sum_nonNestingPlacements_succ_eq_withoutBottomRow_add_bottomRow
    (n i : ℕ) :
    ((truncatedStaircase n (i + 1)).nonNestingPlacements).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        (nonNestingPlacementsWithoutBottomRow n i).sum
          (fun P => (X : ℝ[X]) ^ P.card) +
        (bottomRowCells n i).sum (fun a =>
          ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell a).sum
            (fun P => (X : ℝ[X]) ^ P.card)) := by
  classical
  rw [← union_nonNestingPlacementsWithoutBottomRow_withBottomRow n i]
  rw [Finset.sum_union
    (disjoint_nonNestingPlacementsWithoutBottomRow_withBottomRow n i)]
  rw [sum_nonNestingPlacementsWithBottomRow]

/-- Shifting columns right and then left by the same amount returns the
original finite cell set. -/
theorem shiftColumnsAfter_unshiftColumnsAfter (c : ℕ) (P : Finset (ℕ × ℕ)) :
    shiftColumnsAfter c (unshiftColumnsAfter c P) = P := by
  classical
  ext x
  constructor
  · intro hx
    rw [shiftColumnsAfter, unshiftColumnsAfter] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    rcases Finset.mem_image.mp hy with ⟨a, ha, hay⟩
    subst y
    have hxa : x = a := by
      simpa using hxy.symm
    simpa [hxa] using ha
  · intro hx
    rw [shiftColumnsAfter, unshiftColumnsAfter]
    refine Finset.mem_image.mpr ⟨(x.1, x.2 + (c + 1)), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · simp

/-- Shifting columns left and then right by the same amount returns the
original finite cell set when all columns are strictly after the cut. -/
theorem unshiftColumnsAfter_shiftColumnsAfter_of_forall_col_gt
    {c : ℕ} {P : Finset (ℕ × ℕ)}
    (hcol : ∀ a ∈ P, c < a.2) :
    unshiftColumnsAfter c (shiftColumnsAfter c P) = P := by
  classical
  ext x
  constructor
  · intro hx
    rw [unshiftColumnsAfter, shiftColumnsAfter] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    rcases Finset.mem_image.mp hy with ⟨a, ha, hay⟩
    subst y
    have hc_le : c + 1 ≤ a.2 := Nat.succ_le_of_lt (hcol a ha)
    have hxa : x = a := by
      simpa [Nat.sub_add_cancel hc_le] using hxy.symm
    simpa [hxa] using ha
  · intro hx
    rw [unshiftColumnsAfter, shiftColumnsAfter]
    refine Finset.mem_image.mpr ⟨(x.1, x.2 - (c + 1)), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · have hc_le : c + 1 ≤ x.2 := Nat.succ_le_of_lt (hcol x hx)
      ext <;> simp [Nat.sub_add_cancel hc_le]

/-- If a valid placement in `mu_{n-c-1,i}` is shifted back right and the
bottom-row rook `(i,c)` is reinserted, then the result is a valid placement in
`mu_{n,i+1}`. -/
theorem bottomRookExtension_isNonNestingPlacement
    {n i c : ℕ} {Q : Finset (ℕ × ℕ)}
    (hQ : (truncatedStaircase (n - c - 1) i).IsNonNestingPlacement Q)
    (hbottom : (i, c) ∈ (truncatedStaircase n (i + 1)).cells) :
    (truncatedStaircase n (i + 1)).IsNonNestingPlacement
      (bottomRookExtension i c Q) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [bottomRookExtension] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hbottom
    · rw [unshiftColumnsAfter] at hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases a with ⟨row, col⟩
      have ha_cell := hQ.1 ha
      rw [mem_truncatedStaircase_cells] at ha_cell ⊢
      have hcol_row : col + row < n - c - 1 := Nat.add_lt_of_lt_sub ha_cell.2
      refine ⟨Nat.lt_trans ha_cell.1 (Nat.lt_succ_self i), ?_⟩
      exact Nat.lt_sub_iff_add_lt.mpr (by lia)
  · intro x hx y hy hxy
    rw [bottomRookExtension] at hx hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hxy rfl).elim
      · rw [unshiftColumnsAfter] at hy
        rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        have hb_cell := hQ.1 hb
        rw [mem_truncatedStaircase_cells] at hb_cell
        exact ne_of_gt hb_cell.1
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [unshiftColumnsAfter] at hx
        rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        have ha_cell := hQ.1 ha
        rw [mem_truncatedStaircase_cells] at ha_cell
        exact ne_of_lt ha_cell.1
      · rw [unshiftColumnsAfter] at hx hy
        rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        have hab : a ≠ b := by
          intro hab
          subst b
          exact hxy rfl
        exact hQ.2.1 a ha b hb hab
  · intro x hx y hy hrow
    rw [bottomRookExtension] at hx hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (Nat.lt_irrefl i hrow).elim
      · rw [unshiftColumnsAfter] at hy
        rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        have hb_cell := hQ.1 hb
        rw [mem_truncatedStaircase_cells] at hb_cell
        exact (not_lt_of_ge (Nat.le_of_lt hb_cell.1) hrow).elim
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [unshiftColumnsAfter] at hx
        rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        lia
      · rw [unshiftColumnsAfter] at hx hy
        rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
        exact Nat.add_lt_add_right (hQ.2.2 a ha b hb hrow) (c + 1)

/-- Shifting a valid remainder back right and reinserting the bottom-row rook
increases cardinality by one. -/
theorem bottomRookExtension_card
    {n i c : ℕ} {Q : Finset (ℕ × ℕ)}
    (hQ : (truncatedStaircase (n - c - 1) i).IsNonNestingPlacement Q) :
    (bottomRookExtension i c Q).card = Q.card + 1 := by
  classical
  rw [bottomRookExtension, unshiftColumnsAfter]
  have hnot : (i, c) ∉ Q.image (fun a => (a.1, a.2 + (c + 1))) := by
    intro hi
    rcases Finset.mem_image.mp hi with ⟨a, ha, hmap⟩
    have hrow : a.1 = i := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have ha_cell := hQ.1 ha
    rw [mem_truncatedStaircase_cells] at ha_cell
    exact (ne_of_lt ha_cell.1 hrow).elim
  have hinj :
      Set.InjOn (fun a : ℕ × ℕ => (a.1, a.2 + (c + 1))) ↑Q := by
    intro a _ha b _hb hmap
    have hrow : a.1 = b.1 := by
      simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have hcol_add : a.2 + (c + 1) = b.2 + (c + 1) := by
      simpa using congrArg (fun x : ℕ × ℕ => x.2) hmap
    exact Prod.ext hrow (Nat.add_right_cancel hcol_add)
  rw [Finset.card_insert_eq_ite, if_neg hnot, Finset.card_image_of_injOn hinj]

/-- The bottom-row rook is not already present in a shifted valid remainder. -/
theorem bottomRook_not_mem_unshiftColumnsAfter
    {n i c : ℕ} {Q : Finset (ℕ × ℕ)}
    (hQ : (truncatedStaircase (n - c - 1) i).IsNonNestingPlacement Q) :
    (i, c) ∉ unshiftColumnsAfter c Q := by
  intro hi
  rw [unshiftColumnsAfter] at hi
  rcases Finset.mem_image.mp hi with ⟨a, ha, hmap⟩
  have hrow : a.1 = i := by
    simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
  have ha_cell := hQ.1 ha
  rw [mem_truncatedStaircase_cells] at ha_cell
  exact (ne_of_lt ha_cell.1 hrow).elim

/-- Removing the inserted bottom-row rook from an extended valid remainder
recovers the original remainder. -/
theorem bottomRookRemainder_bottomRookExtension
    {n i c : ℕ} {Q : Finset (ℕ × ℕ)}
    (hQ : (truncatedStaircase (n - c - 1) i).IsNonNestingPlacement Q) :
    bottomRookRemainder i c (bottomRookExtension i c Q) = Q := by
  rw [bottomRookRemainder, bottomRookExtension]
  rw [Finset.erase_insert (bottomRook_not_mem_unshiftColumnsAfter hQ)]
  exact shiftColumnsAfter_unshiftColumnsAfter c Q

/-- Extending the remainder of a valid placement containing a bottom-row rook
recovers the original placement. -/
theorem bottomRookExtension_bottomRookRemainder
    {n i c : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P)
    (hbottom : (i, c) ∈ P) :
    bottomRookExtension i c (bottomRookRemainder i c P) = P := by
  rw [bottomRookExtension, bottomRookRemainder]
  have hcol : ∀ a ∈ P.erase (i, c), c < a.2 := by
    intro a ha
    exact bottom_col_lt_of_mem_erase_bottomRook hP hbottom ha
  rw [unshiftColumnsAfter_shiftColumnsAfter_of_forall_col_gt hcol]
  exact Finset.insert_erase hbottom

/-- On placements containing a fixed bottom-row rook, taking the shifted
remainder is injective. -/
theorem bottomRookRemainder_injOn_nonNestingPlacementsWithCell
    {n i c : ℕ} :
    Set.InjOn (bottomRookRemainder i c)
      ↑((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)) := by
  intro P hP Q hQ hrem
  change P ∈ (truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)
    at hP
  change Q ∈ (truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)
    at hQ
  rw [mem_nonNestingPlacementsWithCell] at hP hQ
  calc
    P = bottomRookExtension i c (bottomRookRemainder i c P) :=
      (bottomRookExtension_bottomRookRemainder hP.1 hP.2).symm
    _ = bottomRookExtension i c (bottomRookRemainder i c Q) := by rw [hrem]
    _ = Q := bottomRookExtension_bottomRookRemainder hQ.1 hQ.2

/-- For a fixed bottom-row cell `(i,c)`, shifted remainders of valid
placements containing that cell are exactly the valid placements on the
smaller truncated staircase. -/
theorem bottomRookRemainder_image_nonNestingPlacementsWithCell
    {n i c : ℕ}
    (hbottom_cell : (i, c) ∈ (truncatedStaircase n (i + 1)).cells) :
    ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)).image
      (bottomRookRemainder i c) =
        (truncatedStaircase (n - c - 1) i).nonNestingPlacements := by
  classical
  ext Q
  constructor
  · intro hQ
    rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
    rw [mem_nonNestingPlacementsWithCell] at hP
    exact mem_nonNestingPlacements.mpr
      (bottomRookRemainder_isNonNestingPlacement hP.1 hP.2)
  · intro hQ
    have hQvalid := mem_nonNestingPlacements.mp hQ
    refine Finset.mem_image.mpr ⟨bottomRookExtension i c Q, ?_, ?_⟩
    · rw [mem_nonNestingPlacementsWithCell]
      exact ⟨bottomRookExtension_isNonNestingPlacement hQvalid hbottom_cell,
        by simp [bottomRookExtension]⟩
    · exact bottomRookRemainder_bottomRookExtension hQvalid

/-- The contribution of placements containing a fixed bottom-row rook is `X`
times the rook polynomial of the shifted remainder board. -/
theorem sum_nonNestingPlacementsWithCell_eq_mul_truncatedStaircaseRookPolynomial
    {n i c : ℕ}
    (hbottom_cell : (i, c) ∈ (truncatedStaircase n (i + 1)).cells) :
    ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        X * truncatedStaircaseRookPolynomial (n - c - 1) i := by
  classical
  let S := (truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)
  let T := (truncatedStaircase (n - c - 1) i).nonNestingPlacements
  have himage : S.image (bottomRookRemainder i c) = T := by
    simpa [S, T]
      using bottomRookRemainder_image_nonNestingPlacementsWithCell hbottom_cell
  have hinj : Set.InjOn (bottomRookRemainder i c) ↑S := by
    simpa [S] using
      (bottomRookRemainder_injOn_nonNestingPlacementsWithCell (n := n) (i := i)
        (c := c))
  have hsum_image :
      (S.image (bottomRookRemainder i c)).sum (fun Q => (X : ℝ[X]) ^ Q.card) =
        S.sum (fun P => (X : ℝ[X]) ^ (bottomRookRemainder i c P).card) := by
    simpa using
      (Finset.sum_image (s := S) (g := bottomRookRemainder i c)
        (f := fun Q => (X : ℝ[X]) ^ Q.card) hinj)
  calc
    S.sum (fun P => (X : ℝ[X]) ^ P.card)
        = S.sum (fun P => X * X ^ (bottomRookRemainder i c P).card) := by
          apply Finset.sum_congr rfl
          intro P hP
          have hPvalid : (truncatedStaircase n (i + 1)).IsNonNestingPlacement P ∧
              (i, c) ∈ P := by
            simpa [S] using mem_nonNestingPlacementsWithCell.mp hP
          have hcard := bottomRookRemainder_card_add_one hPvalid.1 hPvalid.2
          rw [← hcard, pow_succ]
          ring
    _ = X * S.sum (fun P => X ^ (bottomRookRemainder i c P).card) := by
          rw [Finset.mul_sum]
    _ = X * T.sum (fun Q => X ^ Q.card) := by
          rw [← hsum_image, himage]
    _ = X * truncatedStaircaseRookPolynomial (n - c - 1) i := by
          rw [truncatedStaircaseRookPolynomial,
            rookPolynomial_eq_nonNestingPlacements_sum]

/-- A range-shaped version of the fixed bottom-row contribution formula. -/
theorem sum_nonNestingPlacementsWithCell_eq_mul_truncatedStaircaseRookPolynomial_of_lt
    {n i c : ℕ} (hc : c < n - i) :
    ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)).sum
      (fun P => (X : ℝ[X]) ^ P.card) =
        X * truncatedStaircaseRookPolynomial (n - c - 1) i :=
  sum_nonNestingPlacementsWithCell_eq_mul_truncatedStaircaseRookPolynomial
    (by simpa using hc)

/-- Summing the fixed-bottom-row contributions over all bottom-row cells gives
the bottom-row term in the truncated-staircase expansion. -/
theorem sum_bottomRowCells_nonNestingPlacementsWithCell_eq_mul_sum
    (n i : ℕ) :
    (bottomRowCells n i).sum (fun a =>
      ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell a).sum
        (fun P => (X : ℝ[X]) ^ P.card)) =
      X * ((List.range (n - i)).map fun c =>
        truncatedStaircaseRookPolynomial (n - c - 1) i).sum := by
  classical
  have hinj : Set.InjOn (fun c : ℕ => (i, c)) ↑(Finset.range (n - i)) := by
    intro a _ha b _hb h
    simpa using congrArg (fun x : ℕ × ℕ => x.2) h
  rw [bottomRowCells, Finset.sum_image hinj]
  calc
    (Finset.range (n - i)).sum (fun c =>
        ((truncatedStaircase n (i + 1)).nonNestingPlacementsWithCell (i, c)).sum
          (fun P => (X : ℝ[X]) ^ P.card))
        = (Finset.range (n - i)).sum (fun c =>
            X * truncatedStaircaseRookPolynomial (n - c - 1) i) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact
            sum_nonNestingPlacementsWithCell_eq_mul_truncatedStaircaseRookPolynomial_of_lt
              (Finset.mem_range.mp hc)
    _ = (List.map (fun c => X * truncatedStaircaseRookPolynomial (n - c - 1) i)
          (List.range (n - i))).sum := by
          rw [← List.sum_toFinset (fun c =>
            X * truncatedStaircaseRookPolynomial (n - c - 1) i) List.nodup_range]
          congr 1
          ext c
          simp
    _ = X * ((List.range (n - i)).map fun c =>
          truncatedStaircaseRookPolynomial (n - c - 1) i).sum := by
          exact List.sum_map_mul_left (List.range (n - i))
            (fun c => truncatedStaircaseRookPolynomial (n - c - 1) i) X

/-- The truncated staircase with zero rows is the empty board. -/
@[simp] theorem truncatedStaircase_zero_rows (n : ℕ) :
    truncatedStaircase n 0 = empty := by
  simp [truncatedStaircase, empty]

/-- Truncated-staircase rook polynomials have constant coefficient one. -/
@[simp] theorem truncatedStaircaseRookPolynomial_coeff_zero (n i : ℕ) :
    (truncatedStaircaseRookPolynomial n i).coeff 0 = 1 :=
  rookPolynomial_coeff_zero _

/-- The zero-row truncated-staircase rook polynomial is one. -/
@[simp] theorem truncatedStaircaseRookPolynomial_zero_rows (n : ℕ) :
    truncatedStaircaseRookPolynomial n 0 = 1 := by
  simp [truncatedStaircaseRookPolynomial]

/-- The one-row truncated staircase with two cells has rook polynomial
`1 + 2X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_one :
    truncatedStaircaseRookPolynomial 2 1 = 1 + C (2 : ℝ) * X := by
  classical
  have hcells :
      (truncatedStaircase 2 1).cells =
        ({(0, 0), (0, 1)} : Finset (ℕ × ℕ)) := by
    ext x
    constructor
    · intro hx
      simp only [truncatedStaircase, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image] at hx
      rcases hx with ⟨row, hrow, col, hcol, hx⟩
      interval_cases row
      interval_cases col <;> simp_all
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp only [truncatedStaircase, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_image]
        exact ⟨0, by norm_num, 0, by norm_num, rfl⟩
      · simp only [truncatedStaircase, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_image]
        exact ⟨0, by norm_num, 1, by norm_num, rfl⟩
  have hplacements :
      (truncatedStaircase 2 1).cells.powerset.filter
        (fun P => (truncatedStaircase 2 1).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}} : Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    simp only [IsNonNestingPlacement, hcells, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      by_cases h00 : (0, 0) ∈ P
      · by_cases h01 : (0, 1) ∈ P
        · exfalso
          have hne : (0, 0) ≠ (0, 1) := by
            norm_num
          have hrow := h.2.2.1 (0, 0) h00 (0, 1) h01 hne
          exact hrow rfl
        · right
          left
          ext x
          constructor
          · intro hx
            have hxsub := h.1 hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxsub
            rcases hxsub with rfl | rfl
            · simp
            · exact (h01 hx).elim
          · intro hx
            rw [Finset.mem_singleton] at hx
            rw [hx]
            exact h00
      · by_cases h01 : (0, 1) ∈ P
        · right
          right
          ext x
          constructor
          · intro hx
            have hxsub := h.1 hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxsub
            rcases hxsub with rfl | rfl
            · exact (h00 hx).elim
            · simp
          · intro hx
            rw [Finset.mem_singleton] at hx
            rw [hx]
            exact h01
        · left
          ext x
          constructor
          · intro hx
            have hxsub := h.1 hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxsub
            rcases hxsub with rfl | rfl
            · exact (h00 hx).elim
            · exact (h01 hx).elim
          · intro hx
            simp at hx
    · rintro (rfl | rfl | rfl) <;> simp
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements]
  norm_num
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  rw [hC2]
  ring_nf

/-- The one-row truncated staircase with three cells has rook polynomial
`1 + 3X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_one :
    truncatedStaircaseRookPolynomial 3 1 = 1 + C (3 : ℝ) * X := by
  classical
  have hcells :
      (truncatedStaircase 3 1).cells =
        ({(0, 0), (0, 1), (0, 2)} : Finset (ℕ × ℕ)) := by
    decide
  have hplacements :
      (truncatedStaircase 3 1).cells.powerset.filter
        (fun P => (truncatedStaircase 3 1).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    constructor
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have hsub := hmem.1
      fin_cases hsub <;>
        simp [IsNonNestingPlacement] at hmem <;>
        try decide
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;>
        simp [IsNonNestingPlacement, hcells]
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements]
  norm_num
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  rw [hC3]
  ring_nf

/-- The one-row truncated staircase with four cells has rook polynomial
`1 + 4X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_one :
    truncatedStaircaseRookPolynomial 4 1 = 1 + C (4 : ℝ) * X := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 4 1).cells =
        ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℕ × ℕ)) := by
    decide
  have hplacements :
      (truncatedStaircase 4 1).cells.powerset.filter
        (fun P => (truncatedStaircase 4 1).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    constructor
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have hsub := hmem.1
      fin_cases hsub <;>
        simp [IsNonNestingPlacement] at hmem <;>
        try decide
    · intro hmem
      fin_cases hmem <;> simp [IsNonNestingPlacement, hcells]
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  rw [hC4]
  ring_nf

/-- The two-row truncated staircase with row lengths three and two has rook
polynomial `1 + 5X + 3X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_two :
    truncatedStaircaseRookPolynomial 3 2 =
      1 + C (5 : ℝ) * X + C (3 : ℝ) * X ^ 2 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)},
        {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 3 2).cells =
        ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)} : Finset (ℕ × ℕ)) := by
    decide
  have hvalid00 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 0)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid01 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 1)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid02 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 2)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid10 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(1, 0)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid11 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(1, 1)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid01_10 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
    refine isNonNestingPlacement_pair (0, 1) (1, 0) (by rw [hcells]; simp)
      (by rw [hcells]; simp) ?_ ?_ ?_
    · norm_num
    · intro _
      norm_num
    · intro h
      norm_num at h
  have hvalid02_10 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 2), (1, 0)} : Finset (ℕ × ℕ)) := by
    refine isNonNestingPlacement_pair (0, 2) (1, 0) (by rw [hcells]; simp)
      (by rw [hcells]; simp) ?_ ?_ ?_
    · norm_num
    · intro _
      norm_num
    · intro h
      norm_num at h
  have hvalid02_11 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 2), (1, 1)} : Finset (ℕ × ℕ)) := by
    refine isNonNestingPlacement_pair (0, 2) (1, 1) (by rw [hcells]; simp)
      (by rw [hcells]; simp) ?_ ?_ ?_
    · norm_num
    · intro _
      norm_num
    · intro h
      norm_num at h
  have hplacements :
      (truncatedStaircase 3 2).cells.powerset.filter
        (fun P => (truncatedStaircase 3 2).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    constructor
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have hsub := hmem.1
      fin_cases hsub <;>
        simp [IsNonNestingPlacement] at hmem <;>
        try decide
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨by simp, isNonNestingPlacement_empty _⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid00⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid01⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid02⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid10⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid11⟩
      · exact Finset.mem_filter.mpr ⟨by decide, hvalid01_10⟩
      · exact Finset.mem_filter.mpr ⟨by decide, hvalid02_10⟩
      · exact Finset.mem_filter.mpr ⟨by decide, hvalid02_11⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  rw [hC3, hC5]
  ring_nf

/-- The two-row truncated staircase with row lengths four and three has rook
polynomial `1 + 7X + 6X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_two :
    truncatedStaircaseRookPolynomial 4 2 =
      1 + C (7 : ℝ) * X + C (6 : ℝ) * X ^ 2 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
      {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
        {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
        {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 4 2).cells =
        ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2)} :
          Finset (ℕ × ℕ)) := by
    decide
  have hplacements_bool :
      ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2)} :
          Finset (ℕ × ℕ)).powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 4 2) P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}} :
          Finset (Finset (ℕ × ℕ))) := by
    decide
  have hplacements :
      (truncatedStaircase 4 2).cells.powerset.filter
        (fun P => (truncatedStaircase 4 2).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    rw [← hplacements_bool]
    ext P
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 2) P).mpr h.2⟩
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 2) P).mp h.2⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  rw [hC6, hC7]
  ring_nf

/-- The three-row truncated staircase with row lengths four, three, and two
has rook polynomial `1 + 9X + 14X^2 + 4X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_three :
    truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅,
      {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
      {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
      {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
      {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
      {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
      {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
      {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
      {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅,
        {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
        {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
        {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
        {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
        {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
        {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
        {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
        {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
        {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 4 3).cells =
        ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2),
          (2, 0), (2, 1)} : Finset (ℕ × ℕ)) := by
    decide
  have hplacements_bool :
      ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2),
          (2, 0), (2, 1)} : Finset (ℕ × ℕ)).powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 4 3) P) =
        ({∅,
          {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
          {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
          {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
          {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
          {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
          {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
          {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}} :
          Finset (Finset (ℕ × ℕ))) := by
    decide
  have hplacements :
      (truncatedStaircase 4 3).cells.powerset.filter
        (fun P => (truncatedStaircase 4 3).IsNonNestingPlacement P) =
        ({∅,
          {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
          {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
          {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
          {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
          {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
          {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
          {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    rw [← hplacements_bool]
    ext P
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 3) P).mpr h.2⟩
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 3) P).mp h.2⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 := Polynomial.C_eq_natCast (R := ℝ) 14
  rw [hC4, hC9, hC14]
  ring_nf

/-- Convert a verified finite placement list into the corresponding
truncated-staircase rook-polynomial sum. -/
private lemma truncatedStaircaseRookPolynomial_eq_placementList_sum
    {n i : ℕ} {cells : Finset (ℕ × ℕ)}
    {placements : List (Finset (ℕ × ℕ))}
    (hcells : (truncatedStaircase n i).cells = cells)
    (hplacements_bool :
      cells.powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase n i) P) =
        placements.toFinset)
    (hplacements_nodup : placements.Nodup) :
    truncatedStaircaseRookPolynomial n i =
      (placements.map fun P => (X : ℝ[X]) ^ P.card).sum := by
  classical
  have hplacements :
      (truncatedStaircase n i).cells.powerset.filter
        (fun P => (truncatedStaircase n i).IsNonNestingPlacement P) =
        placements.toFinset := by
    rw [hcells, ← hplacements_bool]
    ext P
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase n i) P).mpr h.2⟩
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase n i) P).mp h.2⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements]
  exact List.sum_toFinset (fun P => (X : ℝ[X]) ^ P.card) hplacements_nodup

/-- The two-row truncated staircase with row lengths two and one has rook
polynomial `1 + 3X + X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_two :
    truncatedStaircaseRookPolynomial 2 2 =
      1 + C (3 : ℝ) * X + X ^ 2 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(1, 0)}, {(0, 1), (1, 0)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (1, 0)} : Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 2 2).cells = cells := by
    decide
  have hplacements_bool :
      cells.powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 2 2) P) =
        placements.toFinset := by
    decide
  rw [truncatedStaircaseRookPolynomial_eq_placementList_sum hcells
    hplacements_bool hplacements_nodup]
  norm_num [placements]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  rw [hC3]
  ring_nf

/-- The three-row truncated staircase with row lengths three, two, and one
has rook polynomial `1 + 6X + 6X^2 + X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_three :
    truncatedStaircaseRookPolynomial 3 3 =
      1 + C (6 : ℝ) * X + C (6 : ℝ) * X ^ 2 + X ^ 3 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅,
      {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)}, {(2, 0)},
      {(0, 1), (1, 0)}, {(0, 1), (2, 0)}, {(0, 2), (1, 0)},
      {(0, 2), (1, 1)}, {(0, 2), (2, 0)}, {(1, 1), (2, 0)},
      {(0, 2), (1, 1), (2, 0)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)} :
      Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 3 3).cells = cells := by
    decide
  have hplacements_bool :
      cells.powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 3 3) P) =
        placements.toFinset := by
    decide
  rw [truncatedStaircaseRookPolynomial_eq_placementList_sum hcells
    hplacements_bool hplacements_nodup]
  norm_num [placements]
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  rw [hC6]
  ring_nf

/-- The one-row truncated staircase with five cells has rook polynomial
`1 + 5X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_one :
    truncatedStaircaseRookPolynomial 5 1 = 1 + C (5 : ℝ) * X := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(0, 4)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)} : Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 5 1).cells = cells := by
    decide
  have hplacements_bool :
      cells.powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 5 1) P) =
        placements.toFinset := by
    decide
  rw [truncatedStaircaseRookPolynomial_eq_placementList_sum hcells
    hplacements_bool hplacements_nodup]
  norm_num [placements]
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  rw [hC5]
  ring_nf

/-- The two-row truncated staircase with row lengths five and four has rook
polynomial `1 + 9X + 10X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_two :
    truncatedStaircaseRookPolynomial 5 2 =
      1 + C (9 : ℝ) * X + C (10 : ℝ) * X ^ 2 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅,
      {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(0, 4)}, {(1, 0)}, {(1, 1)},
      {(1, 2)}, {(1, 3)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
      {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
      {(0, 4), (1, 0)}, {(0, 4), (1, 1)}, {(0, 4), (1, 2)},
      {(0, 4), (1, 3)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2),
      (1, 3)} : Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 5 2).cells = cells := by
    decide
  have hplacements_bool :
      cells.powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 5 2) P) =
        placements.toFinset := by
    decide
  rw [truncatedStaircaseRookPolynomial_eq_placementList_sum hcells
    hplacements_bool hplacements_nodup]
  norm_num [placements]
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  rw [hC9, hC10]
  ring_nf

/-- Truncated-staircase rook polynomials are nonzero. -/
theorem truncatedStaircaseRookPolynomial_ne_zero (n i : ℕ) :
    truncatedStaircaseRookPolynomial n i ≠ 0 :=
  rookPolynomial_ne_zero _

/-- Bottom-row expansion for truncated-staircase rook polynomials: split
placements according to whether the last row is empty, and if not, according
to the column of its unique rook. -/
def truncatedStaircaseBottomRowExpansion (n i : ℕ) : Prop :=
  truncatedStaircaseRookPolynomial n (i + 1) =
    truncatedStaircaseRookPolynomial n i +
      X * ((List.range (n - i)).map fun c =>
        truncatedStaircaseRookPolynomial (n - c - 1) i).sum

/-- The bottom-row expansion holds for every truncated staircase. -/
theorem truncatedStaircaseBottomRowExpansion_all (n i : ℕ) :
    truncatedStaircaseBottomRowExpansion n i := by
  dsimp [truncatedStaircaseBottomRowExpansion]
  rw [truncatedStaircaseRookPolynomial, rookPolynomial_eq_nonNestingPlacements_sum]
  rw [sum_nonNestingPlacements_succ_eq_withoutBottomRow_add_bottomRow]
  rw [sum_nonNestingPlacementsWithoutBottomRow_eq_truncatedStaircaseRookPolynomial]
  rw [sum_bottomRowCells_nonNestingPlacementsWithCell_eq_mul_sum]

/-- The one-row truncated staircase with `n` cells has rook polynomial
`1 + nX`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_one_row (n : ℕ) :
    truncatedStaircaseRookPolynomial n 1 = 1 + C (n : ℝ) * X := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 0
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  simp only [truncatedStaircaseRookPolynomial_zero_rows] at hbottom
  rw [hbottom]
  induction n with
  | zero =>
      simp
  | succ n _ =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [Nat.cast_succ, add_comm, mul_add, add_mul]
      ring_nf

/-- Cast the quadratic binomial coefficient to the ambient real field. -/
private theorem nat_choose_two_cast_real (n : ℕ) :
    ((Nat.choose n 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.choose]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
    have hnat := Nat.add_one_mul_choose_eq (n - 1) 1
    rw [Nat.choose_one_right, hnsub] at hnat
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn_pos]
      norm_num
    rw [Nat.cast_mul, hsub] at hcast
    norm_num at hcast
    linarith

/-- Add two cubic polynomials written by coefficients. -/
private theorem add_cubic_coeffs (a b c d e f g : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 : ℝ[X]) +
      (C d + C e * X + C f * X ^ 2 + C g * X ^ 3) =
        C (1 + d) + C (a + e) * X + C (b + f) * X ^ 2 +
          C (c + g) * X ^ 3 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add]
  rw [Polynomial.C_1]
  ring_nf

/-- Add a cubic polynomial to `X` times another cubic polynomial. -/
private theorem add_X_mul_cubic_coeffs (a b c d e f g : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 : ℝ[X]) +
      X * (C d + C e * X + C f * X ^ 2 + C g * X ^ 3) =
        1 + C (a + d) * X + C (b + e) * X ^ 2 +
          C (c + f) * X ^ 3 + C g * X ^ 4 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add]
  ring_nf

/-- Add two quartic polynomials written by coefficients. -/
private theorem add_quartic_coeffs (a b c d e f g h i : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 : ℝ[X]) +
      (C e + C f * X + C g * X ^ 2 + C h * X ^ 3 + C i * X ^ 4) =
        C (1 + e) + C (a + f) * X + C (b + g) * X ^ 2 +
          C (c + h) * X ^ 3 + C (d + i) * X ^ 4 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add,
    Polynomial.C_add]
  rw [Polynomial.C_1]
  ring_nf

/-- Add a quartic polynomial to `X` times another quartic polynomial. -/
private theorem add_X_mul_quartic_coeffs (a b c d e f g h i : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 : ℝ[X]) +
      X * (C e + C f * X + C g * X ^ 2 + C h * X ^ 3 + C i * X ^ 4) =
        1 + C (a + e) * X + C (b + f) * X ^ 2 +
          C (c + g) * X ^ 3 + C (d + h) * X ^ 4 + C i * X ^ 5 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add]
  ring_nf

/-- Add two quintic polynomials written by coefficients. -/
private theorem add_quintic_coeffs (a b c d e f g h i j k : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 +
        C e * X ^ 5 : ℝ[X]) +
      (C f + C g * X + C h * X ^ 2 + C i * X ^ 3 + C j * X ^ 4 +
        C k * X ^ 5) =
        C (1 + f) + C (a + g) * X + C (b + h) * X ^ 2 +
          C (c + i) * X ^ 3 + C (d + j) * X ^ 4 + C (e + k) * X ^ 5 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add,
    Polynomial.C_add, Polynomial.C_add]
  rw [Polynomial.C_1]
  ring_nf

/-- Add a quintic polynomial to `X` times another quintic polynomial. -/
private theorem add_X_mul_quintic_coeffs (a b c d e f g h i j k : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 +
        C e * X ^ 5 : ℝ[X]) +
      X * (C f + C g * X + C h * X ^ 2 + C i * X ^ 3 + C j * X ^ 4 +
        C k * X ^ 5) =
        1 + C (a + f) * X + C (b + g) * X ^ 2 +
          C (c + h) * X ^ 3 + C (d + i) * X ^ 4 + C (e + j) * X ^ 5 +
            C k * X ^ 6 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add,
    Polynomial.C_add]
  ring_nf

/-- The same tail sum with a direct row-count parameter. -/
private theorem truncatedStaircaseRookPolynomial_one_row_tail_sum_direct (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 1 - c - 1) 1).sum =
      C (n : ℝ) + C (Nat.choose (n + 1) 2 : ℝ) * X := by
  induction n with
  | zero =>
      simp [truncatedStaircaseRookPolynomial_one_row]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right,
        Nat.add_sub_cancel_right, tsub_zero]
      change truncatedStaircaseRookPolynomial (n + 1) 1 +
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 - c - 1) 1).sum =
        C ((n + 1 : ℕ) : ℝ) + C (Nat.choose (n + 1 + 1) 2 : ℝ) * X
      rw [ih, truncatedStaircaseRookPolynomial_one_row]
      have hchoose :
          Nat.choose (n + 1 + 1) 2 = Nat.choose (n + 1) 2 + (n + 1) := by
        rw [show n + 1 + 1 = Nat.succ (n + 1) by rfl]
        rw [show 2 = Nat.succ 1 by rfl, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      rw [hchoose]
      simp [Nat.cast_add, Polynomial.C_add, add_comm, add_left_comm, add_assoc,
        add_mul]

/-- Tail sum of one-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_one_row_tail_sum (n : ℕ) :
    ((List.range (n - 1)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 1).sum =
      C ((n - 1 : ℕ) : ℝ) + C (Nat.choose n 2 : ℝ) * X := by
  by_cases hn : n = 0
  · subst n
    simp [truncatedStaircaseRookPolynomial_one_row]
  · have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
    simpa [hnsub] using
      truncatedStaircaseRookPolynomial_one_row_tail_sum_direct (n - 1)

/-- The two-row truncated staircase with row lengths `n` and `n - 1` has rook
polynomial `1 + (2n - 1)X + binom(n,2)X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_rows (n : ℕ) :
    truncatedStaircaseRookPolynomial n 2 =
      1 + C ((2 * n - 1 : ℕ) : ℝ) * X + C (Nat.choose n 2 : ℝ) * X ^ 2 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 1
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_one_row,
    truncatedStaircaseRookPolynomial_one_row_tail_sum n] at hbottom
  rw [hbottom]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn_pos]
      norm_num
    rw [hcast_sub]
    have hC2n : (C ((2 * n - 1 : ℕ) : ℝ) : ℝ[X]) = C ((2 : ℝ) * n - 1) := by
      rw [show ((2 * n - 1 : ℕ) : ℝ) = (2 : ℝ) * n - 1 by
        rw [Nat.cast_sub (by lia : 1 ≤ 2 * n)]
        norm_num]
    rw [hC2n]
    have hXcoeff :
        C (n : ℝ) + C ((n : ℝ) - 1) = (C ((2 : ℝ) * n - 1) : ℝ[X]) := by
      rw [← Polynomial.C_add]
      ring_nf
    calc
      1 + C (n : ℝ) * X + X * (C ((n : ℝ) - 1) +
            C (Nat.choose n 2 : ℝ) * X)
          = 1 + (C (n : ℝ) + C ((n : ℝ) - 1)) * X +
              C (Nat.choose n 2 : ℝ) * X ^ 2 := by
            ring_nf
      _ = 1 + C ((2 : ℝ) * n - 1) * X +
            C (Nat.choose n 2 : ℝ) * X ^ 2 := by
            rw [hXcoeff]

/-- Tail sum of two-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_two_rows_tail_sum_direct (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 2 - c - 1) 2).sum =
      C (n : ℝ) + C ((n * (n + 2) : ℕ) : ℝ) * X +
        C (Nat.choose (n + 2) 3 : ℝ) * X ^ 2 := by
  induction n with
  | zero =>
      simp [truncatedStaircaseRookPolynomial_two_rows]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 2 - 0 - 1 = n + 2 := by
        lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 2 - (c + 1) - 1) 2).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 2 - c - 1) 2).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih, truncatedStaircaseRookPolynomial_two_rows]
      have hchoose :
          Nat.choose (n + 1 + 2) 3 =
            Nat.choose (n + 2) 2 + Nat.choose (n + 2) 3 := by
        calc
          Nat.choose (n + 1 + 2) 3 =
              Nat.choose (Nat.succ (n + 2)) 3 := by
                rfl
          _ = Nat.choose (n + 2) 2 + Nat.choose (n + 2) 3 :=
              by simpa using Nat.choose_succ_succ (n + 2) 2
      have hchoose2 :
          Nat.choose (n + 2) 2 = (n + 1) + Nat.choose (n + 1) 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ (n + 1) 1
      rw [hchoose, hchoose2]
      have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
      simp only [Order.lt_two_iff, zero_le, mul_pos_iff_of_pos_left, add_pos_iff,
        or_true, Nat.cast_pred, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        map_sub, map_mul, map_add, map_natCast, map_one, Nat.cast_one]
      rw [hC2]
      ring_nf

/-- Tail sum of two-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_two_rows_tail_sum (n : ℕ)
    (hn : 2 ≤ n) :
    ((List.range (n - 2)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 2).sum =
      C ((n - 2 : ℕ) : ℝ) + C (((n - 2) * n : ℕ) : ℝ) * X +
        C (Nat.choose n 3 : ℝ) * X ^ 2 := by
  have hnsub : n - 2 + 2 = n := Nat.sub_add_cancel hn
  simpa [hnsub] using
    truncatedStaircaseRookPolynomial_two_rows_tail_sum_direct (n - 2)

/-- The three-row truncated staircase with row lengths `n`, `n - 1`, and
`n - 2` has rook polynomial
`1 + 3(n - 1)X + (binom(n,2) + n(n - 2))X^2 + binom(n,3)X^3`. -/
theorem truncatedStaircaseRookPolynomial_three_rows (n : ℕ) (hn : 3 ≤ n) :
    truncatedStaircaseRookPolynomial n 3 =
      1 + C ((3 * n - 3 : ℕ) : ℝ) * X +
        C ((Nat.choose n 2 + (n - 2) * n : ℕ) : ℝ) * X ^ 2 +
          C (Nat.choose n 3 : ℝ) * X ^ 3 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 2
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_two_rows,
    truncatedStaircaseRookPolynomial_two_rows_tail_sum n (by lia : 2 ≤ n)] at hbottom
  rw [hbottom]
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 3) hn
  have hn_two : 2 ≤ n := by lia
  have hcast_sub_two : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn_two]
    norm_num
  rw [hcast_sub_two]
  have hC2n :
      (C ((2 * n - 1 : ℕ) : ℝ) : ℝ[X]) = C ((2 : ℝ) * n - 1) := by
    rw [show ((2 * n - 1 : ℕ) : ℝ) = (2 : ℝ) * n - 1 by
      rw [Nat.cast_sub (by lia : 1 ≤ 2 * n)]
      norm_num]
  have hCtail :
      (C (((n - 2) * n : ℕ) : ℝ) : ℝ[X]) = C (((n : ℝ) - 2) * n) := by
    rw [Nat.cast_mul, hcast_sub_two]
  have hC3n :
      (C ((3 * n - 3 : ℕ) : ℝ) : ℝ[X]) = C ((3 : ℝ) * n - 3) := by
    rw [show ((3 * n - 3 : ℕ) : ℝ) = (3 : ℝ) * n - 3 by
      rw [Nat.cast_sub (by lia : 3 ≤ 3 * n)]
      norm_num]
  have hCtwo :
      (C ((Nat.choose n 2 + (n - 2) * n : ℕ) : ℝ) : ℝ[X]) =
        C ((Nat.choose n 2 : ℝ) + ((n : ℝ) - 2) * n) := by
    rw [Nat.cast_add, Nat.cast_mul, hcast_sub_two]
  rw [hC2n, hCtail, hC3n, hCtwo]
  have hXcoeff :
      C ((2 : ℝ) * n - 1) + C ((n : ℝ) - 2) =
        (C ((3 : ℝ) * n - 3) : ℝ[X]) := by
    rw [← Polynomial.C_add]
    ring_nf
  calc
    1 + C ((2 : ℝ) * n - 1) * X + C (Nat.choose n 2 : ℝ) * X ^ 2 +
        X * (C ((n : ℝ) - 2) + C (((n : ℝ) - 2) * n) * X +
          C (Nat.choose n 3 : ℝ) * X ^ 2)
        = 1 + (C ((2 : ℝ) * n - 1) + C ((n : ℝ) - 2)) * X +
          (C (Nat.choose n 2 : ℝ) + C (((n : ℝ) - 2) * n)) * X ^ 2 +
            C (Nat.choose n 3 : ℝ) * X ^ 3 := by
          ring_nf
    _ = 1 + C ((3 : ℝ) * n - 3) * X +
        C ((Nat.choose n 2 : ℝ) + ((n : ℝ) - 2) * n) * X ^ 2 +
          C (Nat.choose n 3 : ℝ) * X ^ 3 := by
        rw [hXcoeff, ← Polynomial.C_add]

/-- Tail sum of three-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_three_rows_tail_sum_direct
    (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 3 - c - 1) 3).sum =
      C (n : ℝ) +
        C ((3 : ℝ) * (Nat.choose (n + 2) 2 : ℝ) - 3) * X +
          C ((3 : ℝ) * (Nat.choose (n + 3) 3 : ℝ) -
            (Nat.choose (n + 3) 2 : ℝ)) * X ^ 2 +
            C (Nat.choose (n + 3) 4 : ℝ) * X ^ 3 := by
  induction n with
  | zero =>
      norm_num [Nat.choose]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 3 - 0 - 1 = n + 3 := by
        lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 3 - (c + 1) - 1) 3).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 3 - c - 1) 3).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih,
        truncatedStaircaseRookPolynomial_three_rows (n + 3) (by lia)]
      have hCheadX :
          (C ((3 * (n + 3) - 3 : ℕ) : ℝ) : ℝ[X]) =
            C ((3 : ℝ) * (n + 3) - 3) := by
        rw [show ((3 * (n + 3) - 3 : ℕ) : ℝ) =
            (3 : ℝ) * (n + 3) - 3 by
          rw [Nat.cast_sub (by lia : 3 ≤ 3 * (n + 3))]
          norm_num]
      have hCheadX2 :
          (C ((Nat.choose (n + 3) 2 + (n + 3 - 2) * (n + 3) : ℕ) : ℝ) :
              ℝ[X]) =
            C ((Nat.choose (n + 3) 2 : ℝ) + ((n : ℝ) + 1) * ((n : ℝ) + 3)) := by
        have hsub : ((n + 3 - 2 : ℕ) : ℝ) = (n : ℝ) + 1 := by
          rw [Nat.cast_sub (by lia : 2 ≤ n + 3)]
          norm_num
          ring_nf
        rw [show ((Nat.choose (n + 3) 2 + (n + 3 - 2) * (n + 3) : ℕ) : ℝ) =
            (Nat.choose (n + 3) 2 : ℝ) +
              ((n : ℝ) + 1) * ((n : ℝ) + 3) by
          rw [Nat.cast_add, Nat.cast_mul, hsub]
          norm_num
          ]
      have hchoose3 :
          Nat.choose (n + 1 + 3) 3 =
            Nat.choose (n + 3) 2 + Nat.choose (n + 3) 3 := by
        calc
          Nat.choose (n + 1 + 3) 3 =
              Nat.choose (Nat.succ (n + 3)) 3 := by
                rfl
          _ = Nat.choose (n + 3) 2 + Nat.choose (n + 3) 3 :=
              by simpa using Nat.choose_succ_succ (n + 3) 2
      have hchoose2 :
          Nat.choose (n + 1 + 3) 2 =
            Nat.choose (n + 3) 1 + Nat.choose (n + 3) 2 := by
        calc
          Nat.choose (n + 1 + 3) 2 =
              Nat.choose (Nat.succ (n + 3)) 2 := by
                rfl
          _ = Nat.choose (n + 3) 1 + Nat.choose (n + 3) 2 :=
              by simpa using Nat.choose_succ_succ (n + 3) 1
      have hchoose4 :
          Nat.choose (n + 1 + 3) 4 =
            Nat.choose (n + 3) 3 + Nat.choose (n + 3) 4 := by
        calc
          Nat.choose (n + 1 + 3) 4 =
              Nat.choose (Nat.succ (n + 3)) 4 := by
                rfl
          _ = Nat.choose (n + 3) 3 + Nat.choose (n + 3) 4 :=
              by simpa using Nat.choose_succ_succ (n + 3) 3
      have hchoose2_prev :
          ((Nat.choose (n + 2) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
        have h := nat_choose_two_cast_real (n + 2)
        norm_num at h
        linarith
      have hchoose2_head :
          ((Nat.choose (n + 3) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 3) * ((n : ℝ) + 2) / 2 := by
        have h := nat_choose_two_cast_real (n + 3)
        norm_num at h
        linarith
      rw [hCheadX, hCheadX2, hchoose3, hchoose2, hchoose4]
      rw [add_cubic_coeffs]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [hchoose2_prev, hchoose2_head]
      congr 1
      all_goals ring_nf

/-- Tail sum of three-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_three_rows_tail_sum (n : ℕ)
    (hn : 3 ≤ n) :
    ((List.range (n - 3)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 3).sum =
      C ((n - 3 : ℕ) : ℝ) +
        C ((3 : ℝ) * (Nat.choose (n - 1) 2 : ℝ) - 3) * X +
          C ((3 : ℝ) * (Nat.choose n 3 : ℝ) -
            (Nat.choose n 2 : ℝ)) * X ^ 2 +
            C (Nat.choose n 4 : ℝ) * X ^ 3 := by
  have hnsub_three : n - 3 + 3 = n := Nat.sub_add_cancel hn
  have hnsub_two : n - 3 + 2 = n - 1 := by
    lia
  simpa [hnsub_three, hnsub_two] using
    truncatedStaircaseRookPolynomial_three_rows_tail_sum_direct (n - 3)

/-- The four-row truncated staircase with row lengths `n`, `n - 1`, `n - 2`,
and `n - 3` has rook polynomial
`1 + (4n - 6)X + n(3n - 7)X^2 +
(4 binom(n,3) - binom(n,2))X^3 + binom(n,4)X^4`. -/
theorem truncatedStaircaseRookPolynomial_four_rows (n : ℕ) (hn : 4 ≤ n) :
    truncatedStaircaseRookPolynomial n 4 =
      1 + C ((4 : ℝ) * n - 6) * X +
        C ((n : ℝ) * ((3 : ℝ) * n - 7)) * X ^ 2 +
          C ((4 : ℝ) * (Nat.choose n 3 : ℝ) -
            (Nat.choose n 2 : ℝ)) * X ^ 3 +
            C (Nat.choose n 4 : ℝ) * X ^ 4 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 3
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_three_rows n (by lia),
    truncatedStaircaseRookPolynomial_three_rows_tail_sum n (by lia)] at hbottom
  rw [hbottom]
  have hn_three : 3 ≤ n := by
    lia
  have hn_two : 2 ≤ n := by
    lia
  have hcast_sub_three : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub hn_three]
    norm_num
  have hcast_sub_two : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn_two]
    norm_num
  rw [hcast_sub_three]
  have hC3n :
      (C ((3 * n - 3 : ℕ) : ℝ) : ℝ[X]) = C ((3 : ℝ) * n - 3) := by
    rw [show ((3 * n - 3 : ℕ) : ℝ) = (3 : ℝ) * n - 3 by
      rw [Nat.cast_sub (by lia : 3 ≤ 3 * n)]
      norm_num]
  have hCthree :
      (C ((Nat.choose n 2 + (n - 2) * n : ℕ) : ℝ) : ℝ[X]) =
        C ((Nat.choose n 2 : ℝ) + ((n : ℝ) - 2) * n) := by
    rw [Nat.cast_add, Nat.cast_mul, hcast_sub_two]
  rw [hC3n, hCthree]
  have hchoose2_n : ((Nat.choose n 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    nat_choose_two_cast_real n
  have hchoose2_tail :
      ((Nat.choose (n - 1) 2 : ℕ) : ℝ) =
        ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 := by
    rw [nat_choose_two_cast_real]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ n)]
      norm_num
    rw [hcast]
    ring_nf
  rw [add_X_mul_cubic_coeffs, hchoose2_n, hchoose2_tail]
  congr 1
  all_goals ring_nf

/-- Tail sum of four-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_four_rows_tail_sum_direct
    (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 4 - c - 1) 4).sum =
      C (n : ℝ) + C ((2 : ℝ) * n * ((n : ℝ) + 4)) * X +
        C ((6 : ℝ) * (Nat.choose (n + 4) 3 : ℝ) -
          (4 : ℝ) * (Nat.choose (n + 4) 2 : ℝ)) * X ^ 2 +
        C ((4 : ℝ) * (Nat.choose (n + 4) 4 : ℝ) -
          (Nat.choose (n + 4) 3 : ℝ)) * X ^ 3 +
        C (Nat.choose (n + 4) 5 : ℝ) * X ^ 4 := by
  induction n with
  | zero =>
      norm_num [Nat.choose]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 4 - 0 - 1 = n + 4 := by
        lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 4 - (c + 1) - 1) 4).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 4 - c - 1) 4).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih,
        truncatedStaircaseRookPolynomial_four_rows (n + 4) (by lia)]
      have hchoose2_succ :
          Nat.choose (n + 1 + 4) 2 =
            Nat.choose (n + 4) 1 + Nat.choose (n + 4) 2 := by
        calc
          Nat.choose (n + 1 + 4) 2 =
              Nat.choose (Nat.succ (n + 4)) 2 := by
                rfl
          _ = Nat.choose (n + 4) 1 + Nat.choose (n + 4) 2 :=
              by simpa using Nat.choose_succ_succ (n + 4) 1
      have hchoose3_succ :
          Nat.choose (n + 1 + 4) 3 =
            Nat.choose (n + 4) 2 + Nat.choose (n + 4) 3 := by
        calc
          Nat.choose (n + 1 + 4) 3 =
              Nat.choose (Nat.succ (n + 4)) 3 := by
                rfl
          _ = Nat.choose (n + 4) 2 + Nat.choose (n + 4) 3 :=
              by simpa using Nat.choose_succ_succ (n + 4) 2
      have hchoose4_succ :
          Nat.choose (n + 1 + 4) 4 =
            Nat.choose (n + 4) 3 + Nat.choose (n + 4) 4 := by
        calc
          Nat.choose (n + 1 + 4) 4 =
              Nat.choose (Nat.succ (n + 4)) 4 := by
                rfl
          _ = Nat.choose (n + 4) 3 + Nat.choose (n + 4) 4 :=
              by simpa using Nat.choose_succ_succ (n + 4) 3
      have hchoose5_succ :
          Nat.choose (n + 1 + 4) 5 =
            Nat.choose (n + 4) 4 + Nat.choose (n + 4) 5 := by
        calc
          Nat.choose (n + 1 + 4) 5 =
              Nat.choose (Nat.succ (n + 4)) 5 := by
                rfl
          _ = Nat.choose (n + 4) 4 + Nat.choose (n + 4) 5 :=
              by simpa using Nat.choose_succ_succ (n + 4) 4
      have hchoose2_head :
          ((Nat.choose (n + 4) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 4) * ((n : ℝ) + 3) / 2 := by
        have h := nat_choose_two_cast_real (n + 4)
        norm_num at h
        linarith
      rw [add_quartic_coeffs, hchoose2_succ, hchoose3_succ, hchoose4_succ,
        hchoose5_succ]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [hchoose2_head]
      congr 1
      all_goals ring_nf

/-- Tail sum of four-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_four_rows_tail_sum (n : ℕ)
    (hn : 4 ≤ n) :
    ((List.range (n - 4)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 4).sum =
      C ((n - 4 : ℕ) : ℝ) +
        C ((2 : ℝ) * ((n - 4 : ℕ) : ℝ) * (((n - 4 : ℕ) : ℝ) + 4)) * X +
        C ((6 : ℝ) * (Nat.choose n 3 : ℝ) -
          (4 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 2 +
        C ((4 : ℝ) * (Nat.choose n 4 : ℝ) -
          (Nat.choose n 3 : ℝ)) * X ^ 3 +
        C (Nat.choose n 5 : ℝ) * X ^ 4 := by
  have hnsub_four : n - 4 + 4 = n := Nat.sub_add_cancel hn
  simpa [hnsub_four] using
    truncatedStaircaseRookPolynomial_four_rows_tail_sum_direct (n - 4)

/-- The five-row truncated staircase with row lengths `n`, `n - 1`, `n - 2`,
`n - 3`, and `n - 4` has rook polynomial
`1 + (5n - 10)X + 5n(n - 3)X^2
+ (10 binom(n,3) - 5 binom(n,2))X^3
+ (5 binom(n,4) - binom(n,3))X^4 + binom(n,5)X^5`. -/
theorem truncatedStaircaseRookPolynomial_five_rows (n : ℕ) (hn : 5 ≤ n) :
    truncatedStaircaseRookPolynomial n 5 =
      1 + C ((5 : ℝ) * n - 10) * X +
        C ((5 : ℝ) * n * ((n : ℝ) - 3)) * X ^ 2 +
        C ((10 : ℝ) * (Nat.choose n 3 : ℝ) -
          (5 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 3 +
        C ((5 : ℝ) * (Nat.choose n 4 : ℝ) -
          (Nat.choose n 3 : ℝ)) * X ^ 4 +
        C (Nat.choose n 5 : ℝ) * X ^ 5 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 4
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_four_rows n (by lia),
    truncatedStaircaseRookPolynomial_four_rows_tail_sum n (by lia)] at hbottom
  rw [hbottom]
  have hcast_sub_four : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    rw [Nat.cast_sub (by lia : 4 ≤ n)]
    norm_num
  rw [hcast_sub_four]
  have hchoose2_n : ((Nat.choose n 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    nat_choose_two_cast_real n
  rw [add_X_mul_quartic_coeffs, hchoose2_n]
  congr 1
  all_goals ring_nf

/-- Tail sum of five-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_five_rows_tail_sum_direct
    (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 5 - c - 1) 5).sum =
      C (n : ℝ) + C ((5 : ℝ) * n * ((n : ℝ) + 5) / 2) * X +
        C ((10 : ℝ) * (Nat.choose (n + 5) 3 : ℝ) -
          (10 : ℝ) * (Nat.choose (n + 5) 2 : ℝ)) * X ^ 2 +
        C ((10 : ℝ) * (Nat.choose (n + 5) 4 : ℝ) -
          (5 : ℝ) * (Nat.choose (n + 5) 3 : ℝ)) * X ^ 3 +
        C ((5 : ℝ) * (Nat.choose (n + 5) 5 : ℝ) -
          (Nat.choose (n + 5) 4 : ℝ)) * X ^ 4 +
        C (Nat.choose (n + 5) 6 : ℝ) * X ^ 5 := by
  induction n with
  | zero =>
      norm_num [Nat.choose]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 5 - 0 - 1 = n + 5 := by
        lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 5 - (c + 1) - 1) 5).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 5 - c - 1) 5).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih,
        truncatedStaircaseRookPolynomial_five_rows (n + 5) (by lia)]
      have hchoose2_succ :
          Nat.choose (n + 1 + 5) 2 =
            Nat.choose (n + 5) 1 + Nat.choose (n + 5) 2 := by
        calc
          Nat.choose (n + 1 + 5) 2 =
              Nat.choose (Nat.succ (n + 5)) 2 := by
                rfl
          _ = Nat.choose (n + 5) 1 + Nat.choose (n + 5) 2 :=
              by simpa using Nat.choose_succ_succ (n + 5) 1
      have hchoose3_succ :
          Nat.choose (n + 1 + 5) 3 =
            Nat.choose (n + 5) 2 + Nat.choose (n + 5) 3 := by
        calc
          Nat.choose (n + 1 + 5) 3 =
              Nat.choose (Nat.succ (n + 5)) 3 := by
                rfl
          _ = Nat.choose (n + 5) 2 + Nat.choose (n + 5) 3 :=
              by simpa using Nat.choose_succ_succ (n + 5) 2
      have hchoose4_succ :
          Nat.choose (n + 1 + 5) 4 =
            Nat.choose (n + 5) 3 + Nat.choose (n + 5) 4 := by
        calc
          Nat.choose (n + 1 + 5) 4 =
              Nat.choose (Nat.succ (n + 5)) 4 := by
                rfl
          _ = Nat.choose (n + 5) 3 + Nat.choose (n + 5) 4 :=
              by simpa using Nat.choose_succ_succ (n + 5) 3
      have hchoose5_succ :
          Nat.choose (n + 1 + 5) 5 =
            Nat.choose (n + 5) 4 + Nat.choose (n + 5) 5 := by
        calc
          Nat.choose (n + 1 + 5) 5 =
              Nat.choose (Nat.succ (n + 5)) 5 := by
                rfl
          _ = Nat.choose (n + 5) 4 + Nat.choose (n + 5) 5 :=
              by simpa using Nat.choose_succ_succ (n + 5) 4
      have hchoose6_succ :
          Nat.choose (n + 1 + 5) 6 =
            Nat.choose (n + 5) 5 + Nat.choose (n + 5) 6 := by
        calc
          Nat.choose (n + 1 + 5) 6 =
              Nat.choose (Nat.succ (n + 5)) 6 := by
                rfl
          _ = Nat.choose (n + 5) 5 + Nat.choose (n + 5) 6 :=
              by simpa using Nat.choose_succ_succ (n + 5) 5
      have hchoose2_head :
          ((Nat.choose (n + 5) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 5) * ((n : ℝ) + 4) / 2 := by
        have h := nat_choose_two_cast_real (n + 5)
        norm_num at h
        linarith
      rw [add_quintic_coeffs, hchoose2_succ, hchoose3_succ, hchoose4_succ,
        hchoose5_succ, hchoose6_succ]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [hchoose2_head]
      congr 1
      all_goals ring_nf

/-- Tail sum of five-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_five_rows_tail_sum (n : ℕ)
    (hn : 5 ≤ n) :
    ((List.range (n - 5)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 5).sum =
      C ((n - 5 : ℕ) : ℝ) +
        C ((5 : ℝ) * ((n - 5 : ℕ) : ℝ) *
          (((n - 5 : ℕ) : ℝ) + 5) / 2) * X +
        C ((10 : ℝ) * (Nat.choose n 3 : ℝ) -
          (10 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 2 +
        C ((10 : ℝ) * (Nat.choose n 4 : ℝ) -
          (5 : ℝ) * (Nat.choose n 3 : ℝ)) * X ^ 3 +
        C ((5 : ℝ) * (Nat.choose n 5 : ℝ) -
          (Nat.choose n 4 : ℝ)) * X ^ 4 +
        C (Nat.choose n 6 : ℝ) * X ^ 5 := by
  have hnsub_five : n - 5 + 5 = n := Nat.sub_add_cancel hn
  simpa [hnsub_five] using
    truncatedStaircaseRookPolynomial_five_rows_tail_sum_direct (n - 5)

/-- The six-row truncated staircase with row lengths `n`, `n - 1`, `n - 2`,
`n - 3`, `n - 4`, and `n - 5` has rook polynomial
`1 + (6n - 15)X + (5n(3n - 11)/2)X^2
+ (20 binom(n,3) - 15 binom(n,2))X^3
+ (15 binom(n,4) - 6 binom(n,3))X^4
+ (6 binom(n,5) - binom(n,4))X^5 + binom(n,6)X^6`. -/
theorem truncatedStaircaseRookPolynomial_six_rows (n : ℕ) (hn : 6 ≤ n) :
    truncatedStaircaseRookPolynomial n 6 =
      1 + C ((6 : ℝ) * n - 15) * X +
        C ((5 : ℝ) * n * ((3 : ℝ) * n - 11) / 2) * X ^ 2 +
        C ((20 : ℝ) * (Nat.choose n 3 : ℝ) -
          (15 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 3 +
        C ((15 : ℝ) * (Nat.choose n 4 : ℝ) -
          (6 : ℝ) * (Nat.choose n 3 : ℝ)) * X ^ 4 +
        C ((6 : ℝ) * (Nat.choose n 5 : ℝ) -
          (Nat.choose n 4 : ℝ)) * X ^ 5 +
        C (Nat.choose n 6 : ℝ) * X ^ 6 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 5
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_five_rows n (by lia),
    truncatedStaircaseRookPolynomial_five_rows_tail_sum n (by lia)] at hbottom
  rw [hbottom]
  have hcast_sub_five : ((n - 5 : ℕ) : ℝ) = (n : ℝ) - 5 := by
    rw [Nat.cast_sub (by lia : 5 ≤ n)]
    norm_num
  rw [hcast_sub_five]
  rw [add_X_mul_quintic_coeffs]
  congr 1
  all_goals ring_nf

/-- The auxiliary polynomial `G_n` as a finite sum over truncated staircase
rook polynomials. -/
def auxiliaryG : ℕ → ℝ[X] :=
  fun n => ((List.range n).map fun i => truncatedStaircaseRookPolynomial n i).sum

/-- The finite-board auxiliary polynomial `G_0` is zero. -/
@[simp] theorem auxiliaryG_zero :
    auxiliaryG 0 = 0 := by
  simp [auxiliaryG]

/-- The finite-board auxiliary polynomial `G_1` is one. -/
@[simp] theorem auxiliaryG_one :
    auxiliaryG 1 = 1 := by
  simp [auxiliaryG]

/-- The finite-board auxiliary polynomial `G_2` is `2 + 2X`. -/
@[simp] theorem auxiliaryG_two :
    auxiliaryG 2 = 2 + C (2 : ℝ) * X := by
  rw [auxiliaryG, show List.range 2 = [0, 1] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_two_one]
  ring_nf

/-- The finite-board auxiliary polynomial `G_3` is `3 + 8X + 3X^2`. -/
@[simp] theorem auxiliaryG_three :
    auxiliaryG 3 = 3 + C (8 : ℝ) * X + C (3 : ℝ) * X ^ 2 := by
  rw [auxiliaryG, show List.range 3 = [0, 1, 2] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_three_one,
    truncatedStaircaseRookPolynomial_three_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC8 : (C (8 : ℝ) : ℝ[X]) = 8 := Polynomial.C_eq_natCast (R := ℝ) 8
  rw [hC3, hC5, hC8]
  ring_nf

/-- The expected `G_4` finite-board value follows from the remaining two-row
and three-row truncated-staircase computations. -/
theorem auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_two_three
    (h42 : truncatedStaircaseRookPolynomial 4 2 =
      1 + C (7 : ℝ) * X + C (6 : ℝ) * X ^ 2)
    (h43 : truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 := by
  rw [auxiliaryG, show List.range 4 = [0, 1, 2, 3] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_four_one, h42, h43]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 := Polynomial.C_eq_natCast (R := ℝ) 14
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 := Polynomial.C_eq_natCast (R := ℝ) 20
  rw [hC4, hC6, hC7, hC9, hC14, hC20]
  ring_nf

/-- The expected `G_4` finite-board value now follows from the remaining
three-row truncated-staircase computation. -/
theorem auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_three
    (h43 : truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 :=
  auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_two_three
    truncatedStaircaseRookPolynomial_four_two h43

/-- The finite-board auxiliary polynomial `G_4` is `4 + 20X + 20X^2 + 4X^3`. -/
@[simp] theorem auxiliaryG_four :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 :=
  auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_three
    truncatedStaircaseRookPolynomial_four_three

/-- The expected `G_5` finite-board value follows from the remaining
three-row and four-row truncated-staircase computations. -/
theorem auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
    (h53 : truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (h54 : truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4) :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 := by
  rw [auxiliaryG, show List.range 5 = [0, 1, 2, 3, 4] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_five_one,
    truncatedStaircaseRookPolynomial_five_two, h53, h54]
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  have hC12 : (C (12 : ℝ) : ℝ[X]) = 12 :=
    Polynomial.C_eq_natCast (R := ℝ) 12
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 :=
    Polynomial.C_eq_natCast (R := ℝ) 14
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  have hC30 : (C (30 : ℝ) : ℝ[X]) = 30 :=
    Polynomial.C_eq_natCast (R := ℝ) 30
  have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
    Polynomial.C_eq_natCast (R := ℝ) 40
  have hC75 : (C (75 : ℝ) : ℝ[X]) = 75 :=
    Polynomial.C_eq_natCast (R := ℝ) 75
  rw [hC5, hC9, hC10, hC12, hC14, hC25, hC30, hC40, hC75]
  ring_nf

/-- The expected three-row `n = 5` truncated-staircase computation follows
from the bottom-row expansion into two-row truncated staircases. -/
theorem truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion
    (hbottom : truncatedStaircaseRookPolynomial 5 3 =
      truncatedStaircaseRookPolynomial 5 2 +
        X * (truncatedStaircaseRookPolynomial 4 2 +
          truncatedStaircaseRookPolynomial 3 2 +
            truncatedStaircaseRookPolynomial 2 2)) :
    truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3 := by
  rw [hbottom, truncatedStaircaseRookPolynomial_five_two,
    truncatedStaircaseRookPolynomial_four_two,
    truncatedStaircaseRookPolynomial_three_two,
    truncatedStaircaseRookPolynomial_two_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  have hC12 : (C (12 : ℝ) : ℝ[X]) = 12 :=
    Polynomial.C_eq_natCast (R := ℝ) 12
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  rw [hC3, hC5, hC6, hC7, hC9, hC10, hC12, hC25]
  ring_nf

/-- The bottom-row expansion holds for the three-row staircase with row
lengths three, two, and one. -/
theorem truncatedStaircaseBottomRowExpansion_three_two :
    truncatedStaircaseBottomRowExpansion 3 2 := by
  dsimp [truncatedStaircaseBottomRowExpansion]
  simp only [add_zero]
  rw [truncatedStaircaseRookPolynomial_three_three,
    truncatedStaircaseRookPolynomial_three_two,
    truncatedStaircaseRookPolynomial_two_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  rw [hC3, hC5, hC6]
  ring_nf

/-- The bottom-row expansion holds for the three-row staircase with row
lengths four, three, and two. -/
theorem truncatedStaircaseBottomRowExpansion_four_two :
    truncatedStaircaseBottomRowExpansion 4 2 := by
  dsimp [truncatedStaircaseBottomRowExpansion]
  rw [show List.range 2 = [0, 1] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_four_three,
    truncatedStaircaseRookPolynomial_four_two,
    truncatedStaircaseRookPolynomial_three_two,
    truncatedStaircaseRookPolynomial_two_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 :=
    Polynomial.C_eq_natCast (R := ℝ) 14
  rw [hC3, hC4, hC5, hC6, hC7, hC9, hC14]
  ring_nf

/-- The expected three-row `n = 5` truncated-staircase computation follows
from the named bottom-row expansion predicate. -/
theorem truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion_statement
    (hbottom : truncatedStaircaseBottomRowExpansion 5 2) :
    truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3 :=
  truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
    rw [show List.range (5 - 2) = [0, 1, 2] by rfl] at hbottom
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom
    simpa [add_assoc] using hbottom)

/-- The expected four-row `n = 5` truncated-staircase computation follows
from the bottom-row expansion into three-row truncated staircases. -/
theorem truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion
    (h53 : truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (hbottom : truncatedStaircaseRookPolynomial 5 4 =
      truncatedStaircaseRookPolynomial 5 3 +
        X * (truncatedStaircaseRookPolynomial 4 3 +
          truncatedStaircaseRookPolynomial 3 3)) :
    truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 := by
  rw [hbottom, h53, truncatedStaircaseRookPolynomial_four_three,
    truncatedStaircaseRookPolynomial_three_three]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  have hC12 : (C (12 : ℝ) : ℝ[X]) = 12 :=
    Polynomial.C_eq_natCast (R := ℝ) 12
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 :=
    Polynomial.C_eq_natCast (R := ℝ) 14
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  have hC30 : (C (30 : ℝ) : ℝ[X]) = 30 :=
    Polynomial.C_eq_natCast (R := ℝ) 30
  have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
    Polynomial.C_eq_natCast (R := ℝ) 40
  rw [hC4, hC5, hC6, hC9, hC10, hC12, hC14, hC25, hC30, hC40]
  ring_nf

/-- The expected four-row `n = 5` truncated-staircase computation follows
from the named bottom-row expansion predicate. -/
theorem truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion_statement
    (h53 : truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (hbottom : truncatedStaircaseBottomRowExpansion 5 3) :
    truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion h53 (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
    rw [show List.range (5 - 3) = [0, 1] by rfl] at hbottom
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom
    simpa [add_assoc] using hbottom)

/-- The expected `G_5` finite-board value follows from the two bottom-row
expansions needed for the remaining `n = 5` truncated-staircase rows. -/
theorem auxiliaryG_five_of_bottom_row_expansions
    (hbottom53 : truncatedStaircaseRookPolynomial 5 3 =
      truncatedStaircaseRookPolynomial 5 2 +
        X * (truncatedStaircaseRookPolynomial 4 2 +
          truncatedStaircaseRookPolynomial 3 2 +
            truncatedStaircaseRookPolynomial 2 2))
    (hbottom54 : truncatedStaircaseRookPolynomial 5 4 =
      truncatedStaircaseRookPolynomial 5 3 +
        X * (truncatedStaircaseRookPolynomial 4 3 +
          truncatedStaircaseRookPolynomial 3 3)) :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
    (truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion
      hbottom53)
    (truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion
      (truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion
        hbottom53)
      hbottom54)

/-- The expected `G_5` finite-board value follows from the named bottom-row
expansion predicate in the two remaining `n = 5` rows. -/
theorem auxiliaryG_five_of_bottom_row_expansion_statements
    (hbottom53 : truncatedStaircaseBottomRowExpansion 5 2)
    (hbottom54 : truncatedStaircaseBottomRowExpansion 5 3) :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  auxiliaryG_five_of_bottom_row_expansions (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom53
    rw [show List.range (5 - 2) = [0, 1, 2] by rfl] at hbottom53
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom53
    simpa [add_assoc] using hbottom53) (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom54
    rw [show List.range (5 - 3) = [0, 1] by rfl] at hbottom54
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom54
    simpa [add_assoc] using hbottom54)

/-- The three-row `n = 5` truncated-staircase rook polynomial. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_three :
    truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3 :=
  truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion_statement
    (truncatedStaircaseBottomRowExpansion_all 5 2)

/-- The four-row `n = 5` truncated-staircase rook polynomial. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_four :
    truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 5 (by norm_num)]
  norm_num [Nat.choose]

/-- The finite-board auxiliary polynomial `G_5` is
`5 + 40X + 75X^2 + 40X^3 + 5X^4`. -/
@[simp] theorem auxiliaryG_five :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  auxiliaryG_five_of_bottom_row_expansion_statements
    (truncatedStaircaseBottomRowExpansion_all 5 2)
    (truncatedStaircaseBottomRowExpansion_all 5 3)

/-- The one-row truncated staircase with one cell has rook polynomial
`1 + X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_one_one :
    truncatedStaircaseRookPolynomial 1 1 = 1 + X := by
  rw [truncatedStaircaseRookPolynomial_one_row]
  norm_num

/-- The one-row truncated staircase with six cells has rook polynomial
`1 + 6X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_one :
    truncatedStaircaseRookPolynomial 6 1 = 1 + C (6 : ℝ) * X :=
  truncatedStaircaseRookPolynomial_one_row 6

/-- The two-row truncated staircase with row lengths six and five has rook
polynomial `1 + 11X + 15X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_two :
    truncatedStaircaseRookPolynomial 6 2 =
      1 + C (11 : ℝ) * X + C (15 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
    Polynomial.C_eq_natCast (R := ℝ) 15
  rw [hC15]
  norm_num [Nat.choose]
  exact hC15

/-- The three-row truncated staircase with row lengths six, five, and four has
rook polynomial `1 + 15X + 39X^2 + 20X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_three :
    truncatedStaircaseRookPolynomial 6 3 =
      1 + C (15 : ℝ) * X + C (39 : ℝ) * X ^ 2 +
        C (20 : ℝ) * X ^ 3 := by
  rw [truncatedStaircaseRookPolynomial_three_rows 6 (by norm_num)]
  norm_num [Nat.choose]

/-- The four-row truncated staircase with row lengths four, three, two, and one
has rook polynomial `1 + 10X + 20X^2 + 10X^3 + X^4`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_four :
    truncatedStaircaseRookPolynomial 4 4 =
      1 + C (10 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
        C (10 : ℝ) * X ^ 3 + X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 4 (by norm_num)]
  norm_num [Nat.choose]

/-- The four-row truncated staircase with row lengths six, five, four, and
three has rook polynomial `1 + 18X + 66X^2 + 65X^3 + 15X^4`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_four :
    truncatedStaircaseRookPolynomial 6 4 =
      1 + C (18 : ℝ) * X + C (66 : ℝ) * X ^ 2 +
        C (65 : ℝ) * X ^ 3 + C (15 : ℝ) * X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 6 (by norm_num)]
  norm_num [Nat.choose]

/-- The five-row truncated staircase with row lengths six, five, four, three,
and two has rook polynomial
`1 + 20X + 90X^2 + 125X^3 + 55X^4 + 6X^5`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_five :
    truncatedStaircaseRookPolynomial 6 5 =
      1 + C (20 : ℝ) * X + C (90 : ℝ) * X ^ 2 +
        C (125 : ℝ) * X ^ 3 + C (55 : ℝ) * X ^ 4 +
          C (6 : ℝ) * X ^ 5 := by
  rw [truncatedStaircaseRookPolynomial_five_rows 6 (by norm_num)]
  norm_num [Nat.choose]

/-- The five-row truncated staircase with row lengths five, four, three, two,
and one has rook polynomial
`1 + 15X + 50X^2 + 50X^3 + 15X^4 + X^5`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_five :
    truncatedStaircaseRookPolynomial 5 5 =
      1 + C (15 : ℝ) * X + C (50 : ℝ) * X ^ 2 +
        C (50 : ℝ) * X ^ 3 + C (15 : ℝ) * X ^ 4 + X ^ 5 := by
  rw [truncatedStaircaseRookPolynomial_five_rows 5 (by norm_num)]
  norm_num [Nat.choose]

/-- The finite-board auxiliary polynomial `G_6` is
`6 + 70X + 210X^2 + 210X^3 + 70X^4 + 6X^5`. -/
@[simp] theorem auxiliaryG_six :
    auxiliaryG 6 =
      6 + C (70 : ℝ) * X + C (210 : ℝ) * X ^ 2 +
        C (210 : ℝ) * X ^ 3 + C (70 : ℝ) * X ^ 4 +
          C (6 : ℝ) * X ^ 5 := by
  rw [auxiliaryG, show List.range 6 = [0, 1, 2, 3, 4, 5] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_six_one,
    truncatedStaircaseRookPolynomial_six_two,
    truncatedStaircaseRookPolynomial_six_three,
    truncatedStaircaseRookPolynomial_six_four,
    truncatedStaircaseRookPolynomial_six_five]
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC11 : (C (11 : ℝ) : ℝ[X]) = 11 :=
    Polynomial.C_eq_natCast (R := ℝ) 11
  have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
    Polynomial.C_eq_natCast (R := ℝ) 15
  have hC18 : (C (18 : ℝ) : ℝ[X]) = 18 :=
    Polynomial.C_eq_natCast (R := ℝ) 18
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 :=
    Polynomial.C_eq_natCast (R := ℝ) 20
  have hC39 : (C (39 : ℝ) : ℝ[X]) = 39 :=
    Polynomial.C_eq_natCast (R := ℝ) 39
  have hC55 : (C (55 : ℝ) : ℝ[X]) = 55 :=
    Polynomial.C_eq_natCast (R := ℝ) 55
  have hC65 : (C (65 : ℝ) : ℝ[X]) = 65 :=
    Polynomial.C_eq_natCast (R := ℝ) 65
  have hC66 : (C (66 : ℝ) : ℝ[X]) = 66 :=
    Polynomial.C_eq_natCast (R := ℝ) 66
  have hC70 : (C (70 : ℝ) : ℝ[X]) = 70 :=
    Polynomial.C_eq_natCast (R := ℝ) 70
  have hC90 : (C (90 : ℝ) : ℝ[X]) = 90 :=
    Polynomial.C_eq_natCast (R := ℝ) 90
  have hC125 : (C (125 : ℝ) : ℝ[X]) = 125 :=
    Polynomial.C_eq_natCast (R := ℝ) 125
  have hC210 : (C (210 : ℝ) : ℝ[X]) = 210 :=
    Polynomial.C_eq_natCast (R := ℝ) 210
  rw [hC6, hC11, hC15, hC18, hC20, hC39, hC55, hC65, hC66, hC70,
    hC90, hC125, hC210]
  ring_nf

/-- The one-row truncated staircase with seven cells has rook polynomial
`1 + 7X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_one :
    truncatedStaircaseRookPolynomial 7 1 = 1 + C (7 : ℝ) * X :=
  truncatedStaircaseRookPolynomial_one_row 7

/-- The two-row truncated staircase with row lengths seven and six has rook
polynomial `1 + 13X + 21X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_two :
    truncatedStaircaseRookPolynomial 7 2 =
      1 + C (13 : ℝ) * X + C (21 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  have hC21 : (C (21 : ℝ) : ℝ[X]) = 21 :=
    Polynomial.C_eq_natCast (R := ℝ) 21
  rw [hC21]
  norm_num [Nat.choose]
  exact hC21

/-- The three-row truncated staircase with row lengths seven, six, and five
has rook polynomial `1 + 18X + 56X^2 + 35X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_three :
    truncatedStaircaseRookPolynomial 7 3 =
      1 + C (18 : ℝ) * X + C (56 : ℝ) * X ^ 2 +
        C (35 : ℝ) * X ^ 3 := by
  rw [truncatedStaircaseRookPolynomial_three_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The four-row truncated staircase with row lengths seven, six, five, and
four has rook polynomial `1 + 22X + 98X^2 + 119X^3 + 35X^4`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_four :
    truncatedStaircaseRookPolynomial 7 4 =
      1 + C (22 : ℝ) * X + C (98 : ℝ) * X ^ 2 +
        C (119 : ℝ) * X ^ 3 + C (35 : ℝ) * X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The five-row truncated staircase with row lengths seven, six, five, four,
and three has rook polynomial
`1 + 25X + 140X^2 + 245X^3 + 140X^4 + 21X^5`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_five :
    truncatedStaircaseRookPolynomial 7 5 =
      1 + C (25 : ℝ) * X + C (140 : ℝ) * X ^ 2 +
        C (245 : ℝ) * X ^ 3 + C (140 : ℝ) * X ^ 4 +
          C (21 : ℝ) * X ^ 5 := by
  rw [truncatedStaircaseRookPolynomial_five_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The six-row truncated staircase with row lengths seven, six, five, four,
three, and two has rook polynomial
`1 + 27X + 175X^2 + 385X^3 + 315X^4 + 91X^5 + 7X^6`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_six :
    truncatedStaircaseRookPolynomial 7 6 =
      1 + C (27 : ℝ) * X + C (175 : ℝ) * X ^ 2 +
        C (385 : ℝ) * X ^ 3 + C (315 : ℝ) * X ^ 4 +
          C (91 : ℝ) * X ^ 5 + C (7 : ℝ) * X ^ 6 := by
  rw [truncatedStaircaseRookPolynomial_six_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The finite-board auxiliary polynomial `G_7` is
`7 + 112X + 490X^2 + 784X^3 + 490X^4 + 112X^5 + 7X^6`. -/
@[simp] theorem auxiliaryG_seven :
    auxiliaryG 7 =
      7 + C (112 : ℝ) * X + C (490 : ℝ) * X ^ 2 +
        C (784 : ℝ) * X ^ 3 + C (490 : ℝ) * X ^ 4 +
          C (112 : ℝ) * X ^ 5 + C (7 : ℝ) * X ^ 6 := by
  rw [auxiliaryG, show List.range 7 = [0, 1, 2, 3, 4, 5, 6] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_seven_one,
    truncatedStaircaseRookPolynomial_seven_two,
    truncatedStaircaseRookPolynomial_seven_three,
    truncatedStaircaseRookPolynomial_seven_four,
    truncatedStaircaseRookPolynomial_seven_five,
    truncatedStaircaseRookPolynomial_seven_six]
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC13 : (C (13 : ℝ) : ℝ[X]) = 13 :=
    Polynomial.C_eq_natCast (R := ℝ) 13
  have hC18 : (C (18 : ℝ) : ℝ[X]) = 18 :=
    Polynomial.C_eq_natCast (R := ℝ) 18
  have hC21 : (C (21 : ℝ) : ℝ[X]) = 21 :=
    Polynomial.C_eq_natCast (R := ℝ) 21
  have hC22 : (C (22 : ℝ) : ℝ[X]) = 22 :=
    Polynomial.C_eq_natCast (R := ℝ) 22
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  have hC27 : (C (27 : ℝ) : ℝ[X]) = 27 :=
    Polynomial.C_eq_natCast (R := ℝ) 27
  have hC35 : (C (35 : ℝ) : ℝ[X]) = 35 :=
    Polynomial.C_eq_natCast (R := ℝ) 35
  have hC56 : (C (56 : ℝ) : ℝ[X]) = 56 :=
    Polynomial.C_eq_natCast (R := ℝ) 56
  have hC91 : (C (91 : ℝ) : ℝ[X]) = 91 :=
    Polynomial.C_eq_natCast (R := ℝ) 91
  have hC98 : (C (98 : ℝ) : ℝ[X]) = 98 :=
    Polynomial.C_eq_natCast (R := ℝ) 98
  have hC112 : (C (112 : ℝ) : ℝ[X]) = 112 :=
    Polynomial.C_eq_natCast (R := ℝ) 112
  have hC119 : (C (119 : ℝ) : ℝ[X]) = 119 :=
    Polynomial.C_eq_natCast (R := ℝ) 119
  have hC140 : (C (140 : ℝ) : ℝ[X]) = 140 :=
    Polynomial.C_eq_natCast (R := ℝ) 140
  have hC175 : (C (175 : ℝ) : ℝ[X]) = 175 :=
    Polynomial.C_eq_natCast (R := ℝ) 175
  have hC245 : (C (245 : ℝ) : ℝ[X]) = 245 :=
    Polynomial.C_eq_natCast (R := ℝ) 245
  have hC315 : (C (315 : ℝ) : ℝ[X]) = 315 :=
    Polynomial.C_eq_natCast (R := ℝ) 315
  have hC385 : (C (385 : ℝ) : ℝ[X]) = 385 :=
    Polynomial.C_eq_natCast (R := ℝ) 385
  have hC490 : (C (490 : ℝ) : ℝ[X]) = 490 :=
    Polynomial.C_eq_natCast (R := ℝ) 490
  have hC784 : (C (784 : ℝ) : ℝ[X]) = 784 :=
    Polynomial.C_eq_natCast (R := ℝ) 784
  rw [hC7, hC13, hC18, hC21, hC22, hC25, hC27, hC35, hC56, hC91,
    hC98, hC112, hC119, hC140, hC175, hC245, hC315, hC385, hC490,
    hC784]
  ring_nf

/-- The finite-board version of `G_n` has nonnegative coefficients. -/
theorem auxiliaryG_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (auxiliaryG n) := by
  refine listSum_hasNonnegCoeffs ?_
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _hi, rfl⟩
  exact rookPolynomial_hasNonnegCoeffs _

end FiniteSkewBoard

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

/-- Statement interface for Braun--Jal Theorem 4.1, with the non-nesting rook
polynomial supplied as a parameter. -/
def Theorem41NonNestingRookStatement (M : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (M w ≠ 0 ∧ (M w).Splits) ∧
      Interlaces (M w.deleteFinal) (M w)

/-- Compatibility alias with a name that is easy to find from the paper title. -/
abbrev BraunJalGeneralizedSnakeRealRootedStatement
    (M : SnakeWord → ℝ[X]) : Prop :=
  Theorem41NonNestingRookStatement M

/-- Compatibility alias matching the first milestone note. -/
abbrev GeneralizedSnakeNonNestingRookInterlacesStatement
    (M : SnakeWord → ℝ[X]) : Prop :=
  Theorem41NonNestingRookStatement M

/-- Theorem 4.1 expressed for an abstract squarecase/non-nesting rook model. -/
abbrev SquarecaseRookModelTheorem41Statement
    (model : SquarecaseRookModel) : Prop :=
  Theorem41NonNestingRookStatement model.snakePolynomial

/-- The real-rootedness part of Braun--Jal Theorem 4.1. -/
theorem nonNestingRook_ne_zero_and_splits_of_theorem41
    {M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    M w ≠ 0 ∧ (M w).Splits :=
  (hBJ (w := w) hw).1

/-- The final-letter-deletion interlacing part of Braun--Jal Theorem 4.1. -/
theorem nonNestingRook_deleteFinal_interlaces_of_theorem41
    {M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    Interlaces (M w.deleteFinal) (M w) :=
  (hBJ (w := w) hw).2

/-! ## Narayana and recurrence interfaces from Section 3 -/

/-- A family `P` is the modified Narayana family attached to Narayana
polynomials `N` when `N_{n+1} = X * P_n`, i.e. `P_n(t) = t^{-1} N_{n+1}(t)`.
-/
def ModifiedNarayanaFamilyStatement
    (N P : ℕ → ℝ[X]) : Prop :=
  P 0 = 1 ∧ ∀ n : ℕ, N (n + 1) = X * P n

/-- The auxiliary polynomial `G_n` as the sum of non-nesting rook polynomials
of truncated staircases `mu_{n,i}` for `i = 0, ..., n - 1`. -/
def AuxiliaryGMatchesTruncatedStaircasesStatement
    (Mtrunc : ℕ → ℕ → ℝ[X]) (G : ℕ → ℝ[X]) : Prop :=
  ∀ n : ℕ, G n = ((List.range n).map fun i => Mtrunc n i).sum

/-- The finite-board definition of `G_n` satisfies the truncated-staircase
interface. -/
theorem FiniteSkewBoard.auxiliaryG_matchesTruncatedStaircases :
    AuxiliaryGMatchesTruncatedStaircasesStatement
      FiniteSkewBoard.truncatedStaircaseRookPolynomial
      FiniteSkewBoard.auxiliaryG := by
  intro n
  rfl

/-- Equation (2) of Braun--Jal: `X * G_{n-1} = P_n - (1 + X) * P_{n-1}`. -/
def NarayanaAuxiliaryGRecurrenceStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Lemma 3.3 statement: the auxiliary `G_n` interlaces the modified Narayana
polynomial `P_n`. -/
def Lemma33AuxiliaryGInterlacesStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → Prec (G n) (P n)

/-- Lemma 3.4 statement for the modified Narayana family. -/
def Lemma34ModifiedNarayanaInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Difference `Q_n = P_n - P_{n-1}` used in the Theorem 4.1 matrix step. -/
def narayanaDifference (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  P n - P (n - 1)

/-- Shifted nonnegative-parameter form of Braun--Jal Lemma 3.4, obtained from
the paper statement by writing `mu = nu + 1`.  This is the form that matches
the nonnegative matrix parameters in the Theorem 4.1 induction step. -/
def Lemma34ModifiedNarayanaShiftedInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)
      ((C lam * X + C mu) * P m + narayanaDifference P (m + 1))

/-- The shifted nonnegative-parameter Lemma 3.4 form implies the paper's
`nu ≥ -1` form. -/
theorem lemma34ModifiedNarayanaInterlacing_of_shifted
    {P : ℕ → ℝ[X]}
    (h : Lemma34ModifiedNarayanaShiftedInterlacingStatement P) :
    Lemma34ModifiedNarayanaInterlacingStatement P := by
  intro m lam nu hm hlam hnu
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase := h (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
  have hC : (C (nu + 1) : ℝ[X]) = C nu + 1 := by
    simp
  have hleft :
      ((C lam * X + C (nu + 1)) * P (m - 1) + narayanaDifference P m) =
        ((C lam * X + C nu) * P (m - 1) + P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (nu + 1)) * P m + narayanaDifference P (m + 1)) =
        ((C lam * X + C nu) * P m + P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- The paper's `nu ≥ -1` Lemma 3.4 form implies the shifted
nonnegative-parameter form. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_of_lemma34
    {P : ℕ → ℝ[X]}
    (h : Lemma34ModifiedNarayanaInterlacingStatement P) :
    Lemma34ModifiedNarayanaShiftedInterlacingStatement P := by
  intro m lam mu hm hlam hmu
  have hnu : -1 ≤ mu - 1 := by linarith
  have hbase := h (m := m) (lam := lam) (nu := mu - 1) hm hlam hnu
  have hC : (C (mu - 1) : ℝ[X]) = C mu - 1 := by
    simp
  have hleft :
      ((C lam * X + C (mu - 1)) * P (m - 1) + P m) =
        ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (mu - 1)) * P m + P (m + 1)) =
        ((C lam * X + C mu) * P m + narayanaDifference P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- Equivalence between the paper's Lemma 3.4 statement and the shifted
nonnegative-parameter form. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_iff_lemma34
    (P : ℕ → ℝ[X]) :
    Lemma34ModifiedNarayanaShiftedInterlacingStatement P ↔
      Lemma34ModifiedNarayanaInterlacingStatement P :=
  ⟨lemma34ModifiedNarayanaInterlacing_of_shifted,
    lemma34ModifiedNarayanaShiftedInterlacing_of_lemma34⟩

/-- Bounded form of Braun--Jal equation (2), useful while finite initial
cases are being formalized before the all-`n` recurrence is available. -/
def NarayanaAuxiliaryGRecurrenceUpToStatement
    (P G : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N →
    X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Bounded form of Braun--Jal Lemma 3.3. -/
def Lemma33AuxiliaryGInterlacesUpToStatement
    (P G : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N → Prec (G n) (P n)

/-- Bounded form of Braun--Jal Lemma 3.4. -/
def Lemma34ModifiedNarayanaInterlacingUpToStatement
    (P : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → m ≤ N → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Bounded shifted nonnegative-parameter form of Braun--Jal Lemma 3.4. -/
def Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement
    (P : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → m ≤ N → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)
      ((C lam * X + C mu) * P m + narayanaDifference P (m + 1))

/-- The all-`n` recurrence implies every bounded recurrence package. -/
theorem narayanaAuxiliaryGRecurrenceUpTo_of_statement
    {P G : ℕ → ℝ[X]} (h : NarayanaAuxiliaryGRecurrenceStatement P G)
    (N : ℕ) :
    NarayanaAuxiliaryGRecurrenceUpToStatement P G N := by
  intro n hn _hnN
  exact h hn

/-- The all-`n` Lemma 3.3 statement implies every bounded Lemma 3.3 package. -/
theorem lemma33AuxiliaryGInterlacesUpTo_of_statement
    {P G : ℕ → ℝ[X]} (h : Lemma33AuxiliaryGInterlacesStatement P G)
    (N : ℕ) :
    Lemma33AuxiliaryGInterlacesUpToStatement P G N := by
  intro n hn _hnN
  exact h hn

/-- The all-`n` Lemma 3.4 statement implies every bounded Lemma 3.4 package. -/
theorem lemma34ModifiedNarayanaInterlacingUpTo_of_statement
    {P : ℕ → ℝ[X]} (h : Lemma34ModifiedNarayanaInterlacingStatement P)
    (N : ℕ) :
    Lemma34ModifiedNarayanaInterlacingUpToStatement P N := by
  intro m lam nu hm _hmN hlam hnu
  exact h hm hlam hnu

/-- The all-`n` shifted Lemma 3.4 statement implies every bounded shifted
Lemma 3.4 package. -/
theorem lemma34ModifiedNarayanaShiftedInterlacingUpTo_of_statement
    {P : ℕ → ℝ[X]}
    (h : Lemma34ModifiedNarayanaShiftedInterlacingStatement P) (N : ℕ) :
    Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N := by
  intro m lam mu hm _hmN hlam hmu
  exact h hm hlam hmu

/-- A bounded shifted Lemma 3.4 package implies the bounded paper-shaped
`nu ≥ -1` package. -/
theorem lemma34ModifiedNarayanaInterlacingUpTo_of_shifted
    {P : ℕ → ℝ[X]} {N : ℕ}
    (h : Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N) :
    Lemma34ModifiedNarayanaInterlacingUpToStatement P N := by
  intro m lam nu hm hmN hlam hnu
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase := h (m := m) (lam := lam) (mu := nu + 1) hm hmN hlam hmu
  have hC : (C (nu + 1) : ℝ[X]) = C nu + 1 := by
    simp
  have hleft :
      ((C lam * X + C (nu + 1)) * P (m - 1) + narayanaDifference P m) =
        ((C lam * X + C nu) * P (m - 1) + P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (nu + 1)) * P m + narayanaDifference P (m + 1)) =
        ((C lam * X + C nu) * P m + P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- A bounded paper-shaped Lemma 3.4 package implies the bounded shifted
nonnegative-parameter package. -/
theorem lemma34ModifiedNarayanaShiftedInterlacingUpTo_of_lemma34
    {P : ℕ → ℝ[X]} {N : ℕ}
    (h : Lemma34ModifiedNarayanaInterlacingUpToStatement P N) :
    Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N := by
  intro m lam mu hm hmN hlam hmu
  have hnu : -1 ≤ mu - 1 := by linarith
  have hbase := h (m := m) (lam := lam) (nu := mu - 1) hm hmN hlam hnu
  have hC : (C (mu - 1) : ℝ[X]) = C mu - 1 := by
    simp
  have hleft :
      ((C lam * X + C (mu - 1)) * P (m - 1) + P m) =
        ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (mu - 1)) * P m + P (m + 1)) =
        ((C lam * X + C mu) * P m + narayanaDifference P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- Bounded equivalence between the paper-shaped Lemma 3.4 statement and the
shifted nonnegative-parameter form. -/
theorem lemma34ModifiedNarayanaShiftedInterlacingUpTo_iff_lemma34
    (P : ℕ → ℝ[X]) (N : ℕ) :
    Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N ↔
      Lemma34ModifiedNarayanaInterlacingUpToStatement P N :=
  ⟨lemma34ModifiedNarayanaInterlacingUpTo_of_shifted,
    lemma34ModifiedNarayanaShiftedInterlacingUpTo_of_lemma34⟩

/-- Difference `H_n = G_n - G_{n-1}` used in the Theorem 4.1 matrix step. -/
def auxiliaryDifference (G : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  G n - G (n - 1)

/-- The claim labeled `(6)` in Braun--Jal's proof of Theorem 4.1. -/
def Theorem41MatrixClaimStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m)
      ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)

/-- The reindexed claim labeled `(7)` in Braun--Jal's proof of Theorem 4.1. -/
def Theorem41Claim7Statement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * G (m - 1) + G m)
      ((C lam * X + C nu) * P (m - 1) + P m)

/-- Equation `(2)` rewrites the next modified Narayana combination in the
form used in Braun--Jal's proof of Claim `(7)`. -/
theorem theorem41Claim7_next_eq_of_narayanaAuxiliaryGRecurrence
    {P G : ℕ → ℝ[X]} (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    {m : ℕ} (hm : 2 ≤ m) (lam nu : ℝ) :
    (C lam * X + C nu) * P m + P (m + 1) =
      (1 + X) * ((C lam * X + C nu) * P (m - 1) + P m) +
        X * ((C lam * X + C nu) * G (m - 1) + G m) := by
  have hrec_m : X * G (m - 1) = P m - (1 + X) * P (m - 1) :=
    hrec (n := m) (by linarith)
  have hrec_succ : X * G m = P (m + 1) - (1 + X) * P m := by
    simpa using hrec (n := m + 1) (by linarith)
  rw [show
      (1 + X) * ((C lam * X + C nu) * P (m - 1) + P m) +
          X * ((C lam * X + C nu) * G (m - 1) + G m) =
        (C lam * X + C nu) * ((1 + X) * P (m - 1) + X * G (m - 1)) +
          ((1 + X) * P m + X * G m) by ring]
  rw [hrec_m, hrec_succ]
  ring

/-- Assembly theorem for Braun--Jal Claim `(7)` from equation `(2)`, Lemma
3.4, and the local side conditions used by the univariate conversion step.

Lemma 3.3 is not hidden in this theorem: the remaining `G`-side root and degree
facts are passed explicitly so later concrete work can discharge them without
changing the assembly proof. -/
theorem theorem41Claim7_of_section3
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement P)
    (hW_pos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        HasPosLeadingCoeff ((C lam * X + C nu) * P m + P (m + 1)))
    (hWU_lc :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * P m + P (m + 1)).leadingCoeff =
          ((C lam * X + C nu) * P (m - 1) + P m).leadingCoeff)
    (hdeg_UW :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * P (m - 1) + P m).natDegree + 1 =
          ((C lam * X + C nu) * P m + P (m + 1)).natDegree)
    (hW_nonpos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ∀ r ∈ (((C lam * X + C nu) * P m + P (m + 1)).roots), r ≤ 0)
    (hmid_pos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        HasPosLeadingCoeff
          (((C lam * X + C nu) * P (m - 1) + P m) +
            X * ((C lam * X + C nu) * G (m - 1) + G m)))
    (hV_pos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        HasPosLeadingCoeff ((C lam * X + C nu) * G (m - 1) + G m))
    (hV_nonpos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ∀ r ∈ (((C lam * X + C nu) * G (m - 1) + G m).roots), r ≤ 0)
    (hdeg_VU :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * G (m - 1) + G m).natDegree + 1 =
          ((C lam * X + C nu) * P (m - 1) + P m).natDegree)
    (hU_bound :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ∃ c : ℝ,
          (∀ s ∈ (((C lam * X + C nu) * P (m - 1) + P m).roots), s ≤ c) ∧
            c < 0) :
    Theorem41Claim7Statement P G := by
  intro m lam nu hm hlam hnu
  let U : ℝ[X] := (C lam * X + C nu) * P (m - 1) + P m
  let V : ℝ[X] := (C lam * X + C nu) * G (m - 1) + G m
  let W : ℝ[X] := (C lam * X + C nu) * P m + P (m + 1)
  have hUW : Prec U W := by
    simpa [U, W] using h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu
  have hW_eq : W = (1 + X) * U + X * V := by
    simpa [U, V, W] using
      theorem41Claim7_next_eq_of_narayanaAuxiliaryGRecurrence hrec hm lam nu
  have hU_nonpos : ∀ r ∈ U.roots, r ≤ 0 := by
    rcases hU_bound hm hlam hnu with ⟨c, hU_le, hc_lt⟩
    intro r hr
    exact le_trans (hU_le r (by simpa [U] using hr)) (le_of_lt hc_lt)
  exact
    prec_component_of_prec_next_eq_add_X_mul hUW hW_eq
      (by simpa [W] using hW_pos hm hlam hnu)
      (by simpa [U, W] using hWU_lc hm hlam hnu)
      (by simpa [U, W] using hdeg_UW hm hlam hnu)
      (by simpa [W] using hW_nonpos hm hlam hnu)
      hU_nonpos
      (by simpa [U, V] using hmid_pos hm hlam hnu)
      (by simpa [V] using hV_pos hm hlam hnu)
      (by simpa [V] using hV_nonpos hm hlam hnu)
      (by simpa [U, V] using hdeg_VU hm hlam hnu)
      (by simpa [U] using hU_bound hm hlam hnu)

/-- The matrix claim `(6)` and the reindexed claim `(7)` in Braun--Jal's
proof of Theorem 4.1 are the same statement after writing `nu = mu - 1`. -/
theorem theorem41MatrixClaim_iff_claim7 (P G : ℕ → ℝ[X]) :
    Theorem41MatrixClaimStatement P G ↔ Theorem41Claim7Statement P G := by
  constructor
  · intro hclaim m lam nu hm hlam hnu
    have hmu : 0 ≤ nu + 1 := by linarith
    have hbase := hclaim (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
    have hC : (C (nu + 1) : ℝ[X]) = C nu + 1 := by
      simp
    have hleft :
        ((C lam * X + C (nu + 1)) * G (m - 1) + auxiliaryDifference G m) =
          ((C lam * X + C nu) * G (m - 1) + G m) := by
      rw [auxiliaryDifference, hC]
      ring_nf
    have hright :
        ((C lam * X + C (nu + 1)) * P (m - 1) + narayanaDifference P m) =
          ((C lam * X + C nu) * P (m - 1) + P m) := by
      rw [narayanaDifference, hC]
      ring_nf
    rwa [hleft, hright] at hbase
  · intro hclaim m lam mu hm hlam hmu
    have hnu : -1 ≤ mu - 1 := by linarith
    have hbase := hclaim (m := m) (lam := lam) (nu := mu - 1) hm hlam hnu
    have hC : (C (mu - 1) : ℝ[X]) = C mu - 1 := by
      simp
    have hleft :
        ((C lam * X + C (mu - 1)) * G (m - 1) + G m) =
          ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m) := by
      rw [auxiliaryDifference, hC]
      ring_nf
    have hright :
        ((C lam * X + C (mu - 1)) * P (m - 1) + P m) =
          ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m) := by
      rw [narayanaDifference, hC]
      ring_nf
    rwa [hleft, hright] at hbase

/-- The generalized snake recurrence, Theorem 3.5, in zero-based list
coordinates.  If `k` is the last position where `w` differs from its final
letter, then paper notation `w[:k+1]` and `w[:k]` become `takePrefix (k+1)`
and `takePrefix k` for the list of letters following `epsilon`. -/
def Theorem35GeneralizedSnakeRecurrenceStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- Computable form of Theorem 3.5, using `lastChangeIndex?` instead of a
separate predicate-form witness. -/
def Theorem35GeneralizedSnakeRecurrenceComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, w.lastChangeIndex? = some k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- The predicate-form recurrence implies the computable `lastChangeIndex?`
form. -/
theorem theorem35Computable_of_theorem35
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G := by
  intro w k hlast
  exact hrec (SnakeWord.not_isConstant_of_lastChangeIndex?_eq_some hlast)
    (SnakeWord.isLastChangeIndex_of_lastChangeIndex?_eq_some hlast)

/-- The computable `lastChangeIndex?` recurrence implies the predicate-form
recurrence. -/
theorem theorem35_of_theorem35Computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G) :
    Theorem35GeneralizedSnakeRecurrenceStatement M P G := by
  intro w k _hconst hlast
  exact hrec (SnakeWord.lastChangeIndex?_eq_some_of_isLastChangeIndex hlast)

/-- The predicate-form and computable forms of the generalized snake
recurrence are equivalent. -/
theorem theorem35Computable_iff_theorem35
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G ↔
      Theorem35GeneralizedSnakeRecurrenceStatement M P G :=
  ⟨theorem35_of_theorem35Computable, theorem35Computable_of_theorem35⟩

/-- Statement-level package for the induction route from the Section 3
Narayana and recurrence ingredients to Theorem 4.1. -/
def Theorem41InductionRouteStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G →
    Lemma34ModifiedNarayanaInterlacingStatement P →
    Theorem35GeneralizedSnakeRecurrenceStatement M P G →
      Theorem41NonNestingRookStatement M

/-- Computable-recursion variant of the current Theorem 4.1 induction route. -/
def Theorem41InductionRouteComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G →
    Lemma34ModifiedNarayanaInterlacingStatement P →
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G →
      Theorem41NonNestingRookStatement M

/-- The predicate-form induction route also accepts a computable recurrence
input. -/
theorem theorem41InductionRouteComputable_of_theorem41InductionRoute
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G) :
    Theorem41InductionRouteComputableStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (theorem35_of_theorem35Computable hrec)

/-- The computable-recursion induction route implies the predicate-form route. -/
theorem theorem41InductionRoute_of_theorem41InductionRouteComputable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteComputableStatement M P G) :
    Theorem41InductionRouteStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (theorem35Computable_of_theorem35 hrec)

/-- Predicate and computable forms of the Theorem 4.1 induction route are
equivalent. -/
theorem theorem41InductionRouteComputable_iff_theorem41InductionRoute
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    Theorem41InductionRouteComputableStatement M P G ↔
      Theorem41InductionRouteStatement M P G :=
  ⟨theorem41InductionRoute_of_theorem41InductionRouteComputable,
    theorem41InductionRouteComputable_of_theorem41InductionRoute⟩

/-- Bundled Section 3 ingredients needed by the current Theorem 4.1 induction
interface. -/
structure Theorem41Section3Inputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled Section 3 ingredients using the computable recurrence form. -/
structure Theorem41Section3ComputableInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Bundled Section 3 ingredients using the shifted nonnegative-parameter
Lemma 3.4 form. -/
structure Theorem41Section3ShiftedInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaShiftedInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled Section 3 ingredients using the shifted Lemma 3.4 form and the
computable recurrence form. -/
structure Theorem41Section3ComputableShiftedInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaShiftedInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Convert computable Section 3 inputs into the predicate-form bundle. -/
theorem theorem41Section3Inputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableInputs M P G) :
    Theorem41Section3Inputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := hinputs.lemma34
  recurrence := theorem35_of_theorem35Computable hinputs.recurrence

/-- Convert shifted Section 3 inputs into the paper-shaped bundle. -/
theorem theorem41Section3Inputs_of_shifted
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ShiftedInputs M P G) :
    Theorem41Section3Inputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := lemma34ModifiedNarayanaInterlacing_of_shifted hinputs.lemma34
  recurrence := hinputs.recurrence

/-- Convert computable shifted Section 3 inputs into the paper-shaped
computable bundle. -/
theorem theorem41Section3ComputableInputs_of_shifted
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableShiftedInputs M P G) :
    Theorem41Section3ComputableInputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := lemma34ModifiedNarayanaInterlacing_of_shifted hinputs.lemma34
  recurrence := hinputs.recurrence

/-- Convert computable shifted Section 3 inputs into the predicate-recurrence
shifted bundle. -/
theorem theorem41Section3ShiftedInputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableShiftedInputs M P G) :
    Theorem41Section3ShiftedInputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := hinputs.lemma34
  recurrence := theorem35_of_theorem35Computable hinputs.recurrence

/-- Feed the bundled Section 3 ingredients into the abstract Theorem 4.1
induction route. -/
theorem theorem41_of_section3Inputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3Inputs M P G) :
    Theorem41NonNestingRookStatement M :=
  hroute hinputs.lemma33 hinputs.lemma34 hinputs.recurrence

/-- Feed computable Section 3 ingredients into the abstract Theorem 4.1
induction route. -/
theorem theorem41_of_section3ComputableInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ComputableInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3Inputs hroute
    (theorem41Section3Inputs_of_computable hinputs)

/-- Feed shifted Section 3 ingredients into the abstract Theorem 4.1 induction
route. -/
theorem theorem41_of_section3ShiftedInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ShiftedInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3Inputs hroute
    (theorem41Section3Inputs_of_shifted hinputs)

/-- Feed computable shifted Section 3 ingredients into the abstract Theorem
4.1 induction route. -/
theorem theorem41_of_section3ComputableShiftedInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ComputableShiftedInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3ComputableInputs hroute
    (theorem41Section3ComputableInputs_of_shifted hinputs)

/-! ## Squarecase recurrence packages -/

/-- Existence statement for a squarecase model satisfying the computable
Braun--Jal Theorem 3.5 recurrence for some Section 3 families `P` and `G`. -/
def SquarecaseRookRecurrenceStatement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

/-- Data package for a concrete squarecase/non-nesting rook recurrence.

Later board files should construct this from the actual squarecase board model
and Braun--Jal's positive recurrence. -/
structure SquarecaseRookRecurrencePackage (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookRecurrencePackage

/-- Forget a recurrence data package to the corresponding existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    SquarecaseRookRecurrenceStatement model :=
  ⟨h.P, h.G, h.recurrence⟩

/-- A squarecase recurrence package provides the computable Theorem 3.5
interface for its attached polynomial families. -/
theorem theorem35Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial h.P h.G :=
  h.recurrence

/-- A squarecase recurrence package also provides the predicate-form Theorem
3.5 interface. -/
theorem theorem35 {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    Theorem35GeneralizedSnakeRecurrenceStatement model.snakePolynomial h.P h.G :=
  theorem35_of_theorem35Computable h.recurrence

end SquarecaseRookRecurrencePackage

/-- Existence statement for a squarecase model equipped with the Section 3
inputs needed by the current Theorem 4.1 induction route. -/
def SquarecaseRookSection3Statement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem41Section3ComputableInputs model.snakePolynomial P G

/-- Existence statement for a squarecase model equipped with Section 3 inputs
where Lemma 3.4 is supplied in shifted nonnegative-parameter form. -/
def SquarecaseRookSection3ShiftedStatement
    (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem41Section3ComputableShiftedInputs model.snakePolynomial P G

/-- Data package for the squarecase/non-nesting rook model together with the
Narayana and recurrence inputs from Braun--Jal Section 3. -/
structure SquarecaseRookSection3Package (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookSection3Package

/-- The recurrence component of a Section 3 package as a standalone squarecase
recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Forget a Section 3 data package to the corresponding existence statement.
-/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookSection3Statement model :=
  ⟨h.P, h.G, ⟨h.lemma33, h.lemma34, h.recurrence⟩⟩

/-- A squarecase Section 3 package provides the existing computable input
bundle for the attached polynomial families. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    Theorem41Section3ComputableInputs model.snakePolynomial h.P h.G where
  lemma33 := h.lemma33
  lemma34 := h.lemma34
  recurrence := h.recurrence

/-- A squarecase Section 3 package provides the predicate-form input bundle for
the attached polynomial families. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    Theorem41Section3Inputs model.snakePolynomial h.P h.G :=
  theorem41Section3Inputs_of_computable h.computableInputs

/-- Feed a squarecase Section 3 package into the abstract Theorem 4.1 induction
route. -/
theorem theorem41 {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model)
    (hroute : Theorem41InductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3Inputs hroute h.inputs

/-- Feed a squarecase Section 3 package into the computable form of the
abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  hroute h.lemma33 h.lemma34 h.recurrence

/-- A squarecase Section 3 package also gives the standalone recurrence
existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookSection3Package

/-- Data package for the squarecase/non-nesting rook model when Lemma 3.4 is
proved in shifted nonnegative-parameter form. -/
structure SquarecaseRookSection3ShiftedPackage
    (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaShiftedInterlacingStatement P
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookSection3ShiftedPackage

/-- Convert a shifted Section 3 package to the existing paper-shaped Section 3
package. -/
def section3Package {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookSection3Package model where
  P := h.P
  G := h.G
  lemma33 := h.lemma33
  lemma34 := lemma34ModifiedNarayanaInterlacing_of_shifted h.lemma34
  recurrence := h.recurrence

/-- Forget a shifted Section 3 data package to the corresponding existence
statement. -/
theorem shiftedStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookSection3ShiftedStatement model :=
  ⟨h.P, h.G, ⟨h.lemma33, h.lemma34, h.recurrence⟩⟩

/-- A shifted Section 3 package also gives the existing paper-shaped existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookSection3Statement model :=
  h.section3Package.statement

/-- A shifted Section 3 package provides the computable shifted input bundle.
-/
theorem computableShiftedInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3ComputableShiftedInputs
      model.snakePolynomial h.P h.G where
  lemma33 := h.lemma33
  lemma34 := h.lemma34
  recurrence := h.recurrence

/-- A shifted Section 3 package provides the paper-shaped computable input
bundle. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3ComputableInputs model.snakePolynomial h.P h.G :=
  theorem41Section3ComputableInputs_of_shifted h.computableShiftedInputs

/-- A shifted Section 3 package provides the predicate-form shifted input
bundle. -/
theorem shiftedInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3ShiftedInputs model.snakePolynomial h.P h.G :=
  theorem41Section3ShiftedInputs_of_computable h.computableShiftedInputs

/-- A shifted Section 3 package provides the existing predicate-form input
bundle. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3Inputs model.snakePolynomial h.P h.G :=
  theorem41Section3Inputs_of_shifted h.shiftedInputs

/-- The recurrence component of a shifted Section 3 package as a standalone
squarecase recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Feed a shifted squarecase Section 3 package into the abstract Theorem 4.1
induction route. -/
theorem theorem41 {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model)
    (hroute : Theorem41InductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3ShiftedInputs hroute h.shiftedInputs

/-- Feed a shifted squarecase Section 3 package into the computable form of
the abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model)
    (hroute :
      Theorem41InductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  hroute
    h.lemma33
    (lemma34ModifiedNarayanaInterlacing_of_shifted h.lemma34)
    h.recurrence

/-- A shifted squarecase Section 3 package also gives the standalone
recurrence existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookSection3ShiftedPackage

/-- Shifted squarecase Section 3 inputs imply the existing paper-shaped
Section 3 statement. -/
theorem squarecaseSection3Statement_of_shifted
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model) :
    SquarecaseRookSection3Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact ⟨P, G, theorem41Section3ComputableInputs_of_shifted hinputs⟩

/-- Section 3 inputs for a squarecase model include the Theorem 3.5 recurrence
input needed by the Braun--Jal induction. -/
theorem squarecaseRookRecurrenceStatement_of_section3Statement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookRecurrenceStatement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact ⟨P, G, hinputs.recurrence⟩

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3Statement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact theorem41_of_section3ComputableInputs (hroute P G) hinputs

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3ComputableStatement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact hroute P G hinputs.lemma33 hinputs.lemma34 hinputs.recurrence

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3ShiftedStatement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3ShiftedStatement model) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_squarecaseSection3Statement hroute
    (squarecaseSection3Statement_of_shifted hsection)

/-- A shifted statement-level squarecase Section 3 witness plus a computable
abstract induction route proves the non-nesting-rook Theorem 4.1 form. -/
theorem theorem41_of_squarecaseSection3ComputableShiftedStatement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3ShiftedStatement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact hroute P G hinputs.lemma33
    (lemma34ModifiedNarayanaInterlacing_of_shifted hinputs.lemma34)
    hinputs.recurrence

/-- Statement that a chosen order-polytope `h^*` model agrees with the
non-nesting rook polynomial model for generalized snake words. -/
def OrderPolytopeHStarMatchesNonNestingRook
    (hStar M : SnakeWord → ℝ[X]) : Prop :=
  ∀ w : SnakeWord, hStar w = M w

/-- Final order-polytope `h^*` real-rootedness statement, isolated from the
rook-polynomial model. -/
def OrderPolytopeHStarRealRootedStatement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length → hStar w ≠ 0 ∧ (hStar w).Splits

/-- Final order-polytope `h^*` interlacing statement, isolated from the
rook-polynomial model. -/
def OrderPolytopeHStarInterlacesStatement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    Interlaces (hStar w.deleteFinal) (hStar w)

/-- Full order-polytope `h^*` form of Braun--Jal Theorem 4.1 after the
Stanley/Alexandersson--Jal matching interface has identified the `h^*`
polynomials with non-nesting rook polynomials. -/
def OrderPolytopeHStarTheorem41Statement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (hStar w ≠ 0 ∧ (hStar w).Splits) ∧
      Interlaces (hStar w.deleteFinal) (hStar w)

/-- The full order-polytope `h^*` Theorem 4.1 wrapper implies its
real-rootedness projection. -/
theorem orderPolytopeHStarRealRooted_of_hStarTheorem41
    {hStar : SnakeWord → ℝ[X]}
    (h : OrderPolytopeHStarTheorem41Statement hStar) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  exact (h hw).1

/-- The full order-polytope `h^*` Theorem 4.1 wrapper implies its interlacing
projection. -/
theorem orderPolytopeHStarInterlaces_of_hStarTheorem41
    {hStar : SnakeWord → ℝ[X]}
    (h : OrderPolytopeHStarTheorem41Statement hStar) :
    OrderPolytopeHStarInterlacesStatement hStar := by
  intro w hw
  exact (h hw).2

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  simpa [hmatch w] using
    nonNestingRook_ne_zero_and_splits_of_theorem41 hBJ (w := w) hw

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` interlacing wrapper. -/
theorem orderPolytopeHStarInterlaces_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarInterlacesStatement hStar := by
  intro w hw
  simpa [hmatch w, hmatch w.deleteFinal] using
    nonNestingRook_deleteFinal_interlaces_of_theorem41 hBJ (w := w) hw

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface gives
the full order-polytope `h^*` version of Braun--Jal Theorem 4.1. -/
theorem orderPolytopeHStarTheorem41_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarTheorem41Statement hStar := by
  intro w hw
  exact ⟨orderPolytopeHStarRealRooted_of_theorem41 hBJ hmatch hw,
    orderPolytopeHStarInterlaces_of_theorem41 hBJ hmatch hw⟩

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (theorem41_of_squarecaseSection3Statement hroute hsection) hmatch

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the final `h^*` interlacing wrapper.
-/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (theorem41_of_squarecaseSection3Statement hroute hsection) hmatch

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the full final `h^*` Theorem 4.1
wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (theorem41_of_squarecaseSection3Statement hroute hsection) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` interlacing
wrapper. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the full final `h^*` Theorem 4.1
wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hroute hsection)
    hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
interlacing wrapper. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hroute hsection)
    hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the full final `h^*`
Theorem 4.1 wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hroute hsection)
    hmatch

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route and order-polytope matching proves `h^*` real-rootedness. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ShiftedStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3ShiftedStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_squarecaseSection3Statement hroute
    (squarecaseSection3Statement_of_shifted hsection) hmatch

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route and order-polytope matching proves `h^*` interlacing. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ShiftedStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3ShiftedStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_squarecaseSection3Statement hroute
    (squarecaseSection3Statement_of_shifted hsection) hmatch

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route and order-polytope matching proves the full `h^*` Theorem 4.1.
-/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ShiftedStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3ShiftedStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_squarecaseSection3Statement hroute
    (squarecaseSection3Statement_of_shifted hsection) hmatch

/-- A shifted squarecase Section 3 package, a matching computable induction
route, and the order-polytope matching prove `h^*` real-rootedness. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ShiftedPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedPackage model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A shifted squarecase Section 3 package, a matching computable induction
route, and the order-polytope matching prove `h^*` interlacing. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ShiftedPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedPackage model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A shifted squarecase Section 3 package, a matching computable induction
route, and the order-polytope matching prove the full `h^*` Theorem 4.1. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ShiftedPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedPackage model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

end GeneralizedSnakePosets
end RealRooted
