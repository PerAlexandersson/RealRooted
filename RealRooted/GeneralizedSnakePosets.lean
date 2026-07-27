import RealRooted.GeneralizedSnakePosets.SnakeStaircase

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


end FiniteSkewBoard

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
