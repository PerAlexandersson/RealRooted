import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Basic

/-!
# Bottom-row decomposition for truncated staircases

This module constructs the remove-and-reinsert bijection for a bottom-row rook
and derives the corresponding polynomial decomposition.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

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
    have hc : d = c := by simpa using congrArg (fun x : ℕ × ℕ => x.2) hdc
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

/-- A non-nesting placement in `mu_{n,i}` has at most one rook in each of the
`i` rows. -/
theorem card_le_rows_of_truncatedStaircase_isNonNestingPlacement
    {n i : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n i).IsNonNestingPlacement P) :
    P.card ≤ i := by
  classical
  have hcard : (P.image fun a => a.1).card = P.card := hP.card_image_fst
  have hsub : (P.image fun a => a.1) ⊆ Finset.range i := by
    intro row hrow
    rcases Finset.mem_image.mp hrow with ⟨a, haP, hrow_eq⟩
    have ha_cell := hP.1 haP
    rw [mem_truncatedStaircase_cells] at ha_cell
    rw [← hrow_eq]
    exact Finset.mem_range.mpr ha_cell.1
  have hle := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at hle
  exact hle

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
  have hrow_ne : a.1 ≠ i := by exact hP.2.1 a haP (i, c) hbottom (Finset.mem_erase.mp ha).1
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
    have hrow : a.1 = b.1 := by simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
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
    have hcell : (i, a.2) = a := by ext <;> simp [hrow]
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
  have hcell : (i, a.2) = a := by ext <;> simp [hrow]
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
    have hxa : x = a := by simpa using hxy.symm
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
    have hxa : x = a := by simpa [Nat.sub_add_cancel hc_le] using hxy.symm
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
    have hrow : a.1 = i := by simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
    have ha_cell := hQ.1 ha
    rw [mem_truncatedStaircase_cells] at ha_cell
    exact (ne_of_lt ha_cell.1 hrow).elim
  have hinj :
      Set.InjOn (fun a : ℕ × ℕ => (a.1, a.2 + (c + 1))) ↑Q := by
    intro a _ha b _hb hmap
    have hrow : a.1 = b.1 := by simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
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
  have hrow : a.1 = i := by simpa using congrArg (fun x : ℕ × ℕ => x.1) hmap
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
    _ = X * S.sum (fun P => X ^ (bottomRookRemainder i c P).card) := by rw [Finset.mul_sum]
    _ = X * T.sum (fun Q => X ^ Q.card) := by rw [← hsum_image, himage]
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

/-- A truncated-staircase rook polynomial has no coefficient above its number
of rows. -/
theorem coeff_truncatedStaircaseRookPolynomial_eq_zero_of_rows_lt
    {n i k : ℕ} (hik : i < k) :
    (truncatedStaircaseRookPolynomial n i).coeff k = 0 := by
  classical
  rw [truncatedStaircaseRookPolynomial, rookPolynomial_coeff]
  have hfilter_empty :
      ((truncatedStaircase n i).nonNestingPlacements.filter fun P => P.card = k) =
        ∅ := by
    ext P
    constructor
    · intro hPmem
      rw [Finset.mem_filter, mem_nonNestingPlacements] at hPmem
      have hcard_le :=
        card_le_rows_of_truncatedStaircase_isNonNestingPlacement hPmem.1
      have hcard_eq : P.card = k := hPmem.2
      exact False.elim ((not_le_of_gt hik) (hcard_eq ▸ hcard_le))
    · intro hPempty
      simp at hPempty
  simp [hfilter_empty]

/-- The zero-row truncated-staircase rook polynomial is one. -/
@[simp] theorem truncatedStaircaseRookPolynomial_zero_rows (n : ℕ) :
    truncatedStaircaseRookPolynomial n 0 = 1 := by
  simp [truncatedStaircaseRookPolynomial]

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
