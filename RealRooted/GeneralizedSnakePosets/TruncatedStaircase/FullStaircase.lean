import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Basic
import RealRooted.Mathlib.Combinatorics.Enumerative.OrderedSubsetPairs

/-!
# Full truncated-staircase enumeration

This module identifies non-nesting placements in a full truncated staircase
with componentwise ordered pairs of finite subsets.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

/-- Reflect the columns of a placement in the full `n` by `n` square. -/
def fullStaircaseReflectedPairs (n : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  P.image fun a => (a.1, n - 1 - a.2)

/-- Row projection of the reflected-pair encoding. -/
def fullStaircaseReflectedPairRows (n : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset ℕ :=
  (fullStaircaseReflectedPairs n P).image fun x => x.1

/-- Reflected-column projection of the reflected-pair encoding. -/
def fullStaircaseReflectedPairColumns (n : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset ℕ :=
  (fullStaircaseReflectedPairs n P).image fun x => x.2

/-- Ordered-subset-pair projection of a full-staircase placement. -/
def fullStaircasePlacementOrderedPair (n : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset ℕ × Finset ℕ :=
  (fullStaircaseReflectedPairRows n P, fullStaircaseReflectedPairColumns n P)

/-- Full-staircase placement constructed from an ordered pair of row and
reflected-column subsets. -/
def orderedSubsetPairFullStaircasePlacement (n : ℕ)
    (AB : Finset ℕ × Finset ℕ) : Finset (ℕ × ℕ) :=
  ((AB.1.sort (· ≤ ·)).zip ((AB.2.sort (· ≤ ·)).map fun b => n - 1 - b)).toFinset

/-- Reflected pairs sorted lexicographically by row, then by reflected
column. -/
def fullStaircaseReflectedPairLexList (n : ℕ) (P : Finset (ℕ × ℕ)) :
    List (ℕ × ℕ) :=
  (fullStaircaseReflectedPairs n P).sort (Prod.Lex (· < ·) (· ≤ ·))

/-- Row list of the lexicographically sorted reflected-pair encoding. -/
def fullStaircaseReflectedRowList (n : ℕ) (P : Finset (ℕ × ℕ)) : List ℕ :=
  (fullStaircaseReflectedPairLexList n P).map fun x => x.1

/-- Reflected-column list of the lexicographically sorted reflected-pair
encoding. -/
def fullStaircaseReflectedColumnList (n : ℕ) (P : Finset (ℕ × ℕ)) :
    List ℕ :=
  (fullStaircaseReflectedPairLexList n P).map fun x => x.2

/-- Membership in the reflected-pair encoding. -/
@[simp] theorem mem_fullStaircaseReflectedPairs
    {n : ℕ} {P : Finset (ℕ × ℕ)} {x : ℕ × ℕ} :
    x ∈ fullStaircaseReflectedPairs n P ↔
      ∃ a ∈ P, (a.1, n - 1 - a.2) = x := by
  classical
  simp [fullStaircaseReflectedPairs]

/-- Membership in the lexicographically sorted reflected-pair list. -/
@[simp] theorem mem_fullStaircaseReflectedPairLexList
    {n : ℕ} {P : Finset (ℕ × ℕ)} {x : ℕ × ℕ} :
    x ∈ fullStaircaseReflectedPairLexList n P ↔
      x ∈ fullStaircaseReflectedPairs n P := by
  simp [fullStaircaseReflectedPairLexList]

/-- The reflected-pair lexicographic list is pairwise lexicographically
ordered. -/
theorem fullStaircaseReflectedPairLexList_pairwise
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    (fullStaircaseReflectedPairLexList n P).Pairwise
      (Prod.Lex (· < ·) (· ≤ ·)) := by
  simp [fullStaircaseReflectedPairLexList]

/-- The reflected-pair lexicographic list has no duplicate pairs. -/
theorem fullStaircaseReflectedPairLexList_nodup
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    (fullStaircaseReflectedPairLexList n P).Nodup := by
  simp [fullStaircaseReflectedPairLexList]

/-- Membership in the row projection of the reflected-pair encoding. -/
@[simp] theorem mem_fullStaircaseReflectedPairRows
    {n row : ℕ} {P : Finset (ℕ × ℕ)} :
    row ∈ fullStaircaseReflectedPairRows n P ↔
      ∃ a ∈ P, a.1 = row := by
  classical
  simp [fullStaircaseReflectedPairRows, fullStaircaseReflectedPairs]

/-- Membership in the reflected-column projection of the reflected-pair
encoding. -/
@[simp] theorem mem_fullStaircaseReflectedPairColumns
    {n col : ℕ} {P : Finset (ℕ × ℕ)} :
    col ∈ fullStaircaseReflectedPairColumns n P ↔
      ∃ a ∈ P, n - 1 - a.2 = col := by
  classical
  simp [fullStaircaseReflectedPairColumns, fullStaircaseReflectedPairs]

/-- The row projection of the reflected-pair encoding is the original row
projection. -/
theorem fullStaircaseReflectedPairRows_eq_image_fst
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    fullStaircaseReflectedPairRows n P = P.image fun a => a.1 := by
  ext row
  simp

/-- The reflected-column projection of the reflected-pair encoding is the
column-reflection image of the original placement. -/
theorem fullStaircaseReflectedPairColumns_eq_image_reflectedColumn
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    fullStaircaseReflectedPairColumns n P = P.image fun a => n - 1 - a.2 := by
  ext col
  simp

/-- The row list of the lexicographically sorted reflected pairs has the same
underlying finite set as the row projection. -/
theorem fullStaircaseReflectedRowList_toFinset
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    (fullStaircaseReflectedRowList n P).toFinset =
      fullStaircaseReflectedPairRows n P := by
  ext row
  simp [fullStaircaseReflectedRowList, fullStaircaseReflectedPairLexList,
    fullStaircaseReflectedPairRows]

/-- The reflected-column list of the lexicographically sorted reflected pairs
has the same underlying finite set as the reflected-column projection. -/
theorem fullStaircaseReflectedColumnList_toFinset
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    (fullStaircaseReflectedColumnList n P).toFinset =
      fullStaircaseReflectedPairColumns n P := by
  ext col
  simp [fullStaircaseReflectedColumnList, fullStaircaseReflectedPairLexList,
    fullStaircaseReflectedPairColumns]

/-- The row list of the lexicographically sorted reflected pairs is weakly
increasing. -/
theorem fullStaircaseReflectedRowList_sortedLE
    (n : ℕ) (P : Finset (ℕ × ℕ)) :
    (fullStaircaseReflectedRowList n P).SortedLE := by
  rw [List.sortedLE_iff_pairwise, fullStaircaseReflectedRowList,
    List.pairwise_map]
  exact (fullStaircaseReflectedPairLexList_pairwise n P).imp (by
    intro a b h
    cases h with
    | left b1 b2 hrow => exact le_of_lt hrow
    | right a hcol => exact le_rfl)

/-- The reflected-pair encoding of a full-staircase placement has the same
cardinality as the original placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairs_card
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedPairs n P).card = P.card := by
  rw [fullStaircaseReflectedPairs]
  exact Finset.card_image_of_injOn (by
    intro a ha b hb hpair
    have hrow : a.1 = b.1 := by simpa using congrArg (fun x : ℕ × ℕ => x.1) hpair
    by_contra hne
    exact hP.row_ne ha hb hne hrow)

/-- The reflected-pair row projection of a full-staircase placement has the
same cardinality as the placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairRows_card
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedPairRows n P).card = P.card := by
  rw [fullStaircaseReflectedPairRows_eq_image_fst, hP.card_image_fst]

/-- The reflected-column projection of a full-staircase placement has the same
cardinality as the placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairColumns_card
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedPairColumns n P).card = P.card := by
  rw [fullStaircaseReflectedPairColumns_eq_image_reflectedColumn,
    hP.full_card_image_reflectedColumn]

/-- The row list of the lexicographically sorted reflected pairs has length
equal to the placement cardinality. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedRowList_length
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedRowList n P).length = P.card := by
  rw [fullStaircaseReflectedRowList, List.length_map,
    fullStaircaseReflectedPairLexList, Finset.length_sort,
    hP.fullStaircaseReflectedPairs_card]

/-- The reflected-column list of the lexicographically sorted reflected pairs
has length equal to the placement cardinality. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedColumnList_length
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedColumnList n P).length = P.card := by
  rw [fullStaircaseReflectedColumnList, List.length_map,
    fullStaircaseReflectedPairLexList, Finset.length_sort,
    hP.fullStaircaseReflectedPairs_card]

/-- The row list of the lexicographically sorted reflected pairs has no
duplicates for a valid full-staircase placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedRowList_nodup
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedRowList n P).Nodup := by
  rw [fullStaircaseReflectedRowList]
  refine List.Nodup.map_on ?_ (fullStaircaseReflectedPairLexList_nodup n P)
  intro x hx y hy hrow
  have hxP : x ∈ fullStaircaseReflectedPairs n P :=
    mem_fullStaircaseReflectedPairLexList.mp hx
  have hyP : y ∈ fullStaircaseReflectedPairs n P :=
    mem_fullStaircaseReflectedPairLexList.mp hy
  rcases mem_fullStaircaseReflectedPairs.mp hxP with ⟨a, ha, rfl⟩
  rcases mem_fullStaircaseReflectedPairs.mp hyP with ⟨b, hb, rfl⟩
  by_cases hab : a = b
  · subst b
    rfl
  · exact (hP.row_ne ha hb hab hrow).elim

/-- The reflected-column list of the lexicographically sorted reflected pairs
has no duplicates for a valid full-staircase placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedColumnList_nodup
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedColumnList n P).Nodup := by
  rw [fullStaircaseReflectedColumnList]
  refine List.Nodup.map_on ?_ (fullStaircaseReflectedPairLexList_nodup n P)
  intro x hx y hy hcol
  have hxP : x ∈ fullStaircaseReflectedPairs n P :=
    mem_fullStaircaseReflectedPairLexList.mp hx
  have hyP : y ∈ fullStaircaseReflectedPairs n P :=
    mem_fullStaircaseReflectedPairLexList.mp hy
  rcases mem_fullStaircaseReflectedPairs.mp hxP with ⟨a, ha, rfl⟩
  rcases mem_fullStaircaseReflectedPairs.mp hyP with ⟨b, hb, rfl⟩
  by_cases hab : a = b
  · subst b
    rfl
  · exact (hP.full_reflectedColumn_ne ha hb hab hcol).elim

/-- The reflected-pair row projection of a full-staircase placement lies in
`range n`. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairRows_subset_range
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    fullStaircaseReflectedPairRows n P ⊆ Finset.range n := by
  intro row hrow
  rcases mem_fullStaircaseReflectedPairRows.mp hrow with ⟨a, ha, hrow_eq⟩
  have ha_cell := hP.1 ha
  rw [mem_truncatedStaircase_full_cells_iff] at ha_cell
  rw [← hrow_eq]
  exact Finset.mem_range.mpr (by lia)

/-- The reflected-column projection of a full-staircase placement lies in
`range n`. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairColumns_subset_range
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    fullStaircaseReflectedPairColumns n P ⊆ Finset.range n := by
  intro col hcol
  rcases mem_fullStaircaseReflectedPairColumns.mp hcol with ⟨a, ha, hcol_eq⟩
  have ha_cell := hP.1 ha
  rw [mem_truncatedStaircase_full_cells_iff] at ha_cell
  rw [← hcol_eq]
  exact Finset.mem_range.mpr (by lia)

/-- Every reflected pair from a full-staircase placement lies in the upper
triangle of the `n` by `n` square. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairs_mem_bounds
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P)
    {x : ℕ × ℕ} (hx : x ∈ fullStaircaseReflectedPairs n P) :
    x.1 < n ∧ x.2 < n ∧ x.1 ≤ x.2 := by
  rcases mem_fullStaircaseReflectedPairs.mp hx with ⟨a, ha, rfl⟩
  have ha_cell := hP.1 ha
  rw [mem_truncatedStaircase_full_cells_iff] at ha_cell
  exact ⟨by lia, by lia, hP.full_row_le_reflectedColumn ha⟩

/-- Row and reflected-column lists of the lexicographically sorted
reflected-pair encoding are componentwise ordered. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedLists_forall₂_le
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    List.Forall₂ (· ≤ ·) (fullStaircaseReflectedRowList n P)
      (fullStaircaseReflectedColumnList n P) := by
  rw [fullStaircaseReflectedRowList, fullStaircaseReflectedColumnList]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  intro x hx
  have hx_pairs : x ∈ fullStaircaseReflectedPairs n P := by
    simpa [fullStaircaseReflectedPairLexList] using hx
  exact (hP.fullStaircaseReflectedPairs_mem_bounds hx_pairs).2.2

/-- Reflected columns increase with rows inside the reflected-pair encoding of
a full-staircase placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairs_snd_lt_of_fst_lt
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P)
    {x y : ℕ × ℕ} (hx : x ∈ fullStaircaseReflectedPairs n P)
    (hy : y ∈ fullStaircaseReflectedPairs n P) (hrow : x.1 < y.1) :
    x.2 < y.2 := by
  rcases mem_fullStaircaseReflectedPairs.mp hx with ⟨a, ha, rfl⟩
  rcases mem_fullStaircaseReflectedPairs.mp hy with ⟨b, hb, rfl⟩
  exact hP.full_reflectedColumn_lt_of_row_lt ha hb hrow

/-- The reflected-column list of the lexicographically sorted reflected pairs
is weakly increasing for a valid full-staircase placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedColumnList_sortedLE
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedColumnList n P).SortedLE := by
  rw [fullStaircaseReflectedColumnList]
  rw [List.sortedLE_iff_getElem_le_getElem_of_le]
  intro i j hi hj hij
  by_cases heq : i = j
  · subst j
    rfl
  have hlt : i < j := lt_of_le_of_ne hij heq
  let L := fullStaircaseReflectedPairLexList n P
  have hiL : i < L.length := by simpa [L] using hi
  have hjL : j < L.length := by simpa [L] using hj
  set x := L[i] with hx
  set y := L[j] with hy
  have hlex : Prod.Lex (· < ·) (· ≤ ·) x y := by
    simpa [x, y] using
      (List.pairwise_iff_getElem.mp
        (fullStaircaseReflectedPairLexList_pairwise n P)) i j hiL hjL hlt
  have hxi : x ∈ fullStaircaseReflectedPairs n P :=
    mem_fullStaircaseReflectedPairLexList.mp (by
      simp [x, L])
  have hxj : y ∈ fullStaircaseReflectedPairs n P :=
    mem_fullStaircaseReflectedPairLexList.mp (by
      simp [y, L])
  have hcol : x.2 ≤ y.2 := by
    rcases x with ⟨xr, xc⟩
    rcases y with ⟨yr, yc⟩
    cases hlex with
    | left b1 b2 hrow =>
        exact le_of_lt
          (hP.fullStaircaseReflectedPairs_snd_lt_of_fst_lt hxi hxj hrow)
    | right a hcol => exact hcol
  simpa [x, y, hx, hy, L] using hcol

/-- Sorting the reflected row projection recovers the reflected row list. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairRows_sort
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedPairRows n P).sort (· ≤ ·) =
      fullStaircaseReflectedRowList n P := by
  have hnodup : (fullStaircaseReflectedRowList n P).Nodup :=
    hP.fullStaircaseReflectedRowList_nodup
  rw [← fullStaircaseReflectedRowList_toFinset n P]
  exact (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr (by
    exact List.SortedLE.pairwise (fullStaircaseReflectedRowList_sortedLE n P))

/-- Sorting the reflected-column projection recovers the reflected-column
list. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairColumns_sort
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    (fullStaircaseReflectedPairColumns n P).sort (· ≤ ·) =
      fullStaircaseReflectedColumnList n P := by
  have hnodup : (fullStaircaseReflectedColumnList n P).Nodup :=
    hP.fullStaircaseReflectedColumnList_nodup
  rw [← fullStaircaseReflectedColumnList_toFinset n P]
  exact (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr (by
    exact List.SortedLE.pairwise hP.fullStaircaseReflectedColumnList_sortedLE)

/-- The ordered-subset-pair projection of a size-`k` full-staircase placement
lies in `orderedKSubsetPairs n k`. -/
theorem IsNonNestingPlacement.mem_orderedKSubsetPairs_fullStaircasePlacementOrderedPair
    {n k : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) (hcard : P.card = k) :
    fullStaircasePlacementOrderedPair n P ∈ Finset.orderedKSubsetPairs n k := by
  classical
  rw [fullStaircasePlacementOrderedPair, Finset.mem_orderedKSubsetPairs]
  refine ⟨hP.fullStaircaseReflectedPairRows_subset_range, ?_,
    hP.fullStaircaseReflectedPairColumns_subset_range, ?_, ?_⟩
  · rw [hP.fullStaircaseReflectedPairRows_card, hcard]
  · rw [hP.fullStaircaseReflectedPairColumns_card, hcard]
  · rw [hP.fullStaircaseReflectedPairRows_sort,
      hP.fullStaircaseReflectedPairColumns_sort]
    exact hP.fullStaircaseReflectedLists_forall₂_le

private theorem orderedSubsetPairFullStaircasePlacement_list_nodup
    (n : ℕ) {A B : Finset ℕ} (hcard : A.card = B.card) :
    ((A.sort (· ≤ ·)).zip ((B.sort (· ≤ ·)).map fun b => n - 1 - b)).Nodup := by
  apply List.Nodup.of_map Prod.fst
  have hlen :
      (A.sort (· ≤ ·)).length ≤ ((B.sort (· ≤ ·)).map fun b => n - 1 - b).length := by
    rw [List.length_map, Finset.length_sort, Finset.length_sort, hcard]
  rw [List.map_fst_zip hlen]
  exact A.sort_nodup (· ≤ ·)

/-- The placement constructed from an ordered `k`-subset pair has cardinality
`k`. -/
theorem orderedSubsetPairFullStaircasePlacement_card
    {n k : ℕ} {AB : Finset ℕ × Finset ℕ}
    (hAB : AB ∈ Finset.orderedKSubsetPairs n k) :
    (orderedSubsetPairFullStaircasePlacement n AB).card = k := by
  classical
  rcases AB with ⟨A, B⟩
  rw [Finset.mem_orderedKSubsetPairs] at hAB
  rcases hAB with ⟨_hA, hAcard, _hB, hBcard, _hle⟩
  rw [orderedSubsetPairFullStaircasePlacement,
    List.toFinset_card_of_nodup
      (orderedSubsetPairFullStaircasePlacement_list_nodup n (by rw [hAcard, hBcard])),
    List.length_zip, List.length_map, Finset.length_sort, Finset.length_sort,
    hAcard, hBcard, min_self]

/-- The placement constructed from an ordered subset pair is non-nesting in
the full truncated staircase. -/
theorem orderedSubsetPairFullStaircasePlacement_isNonNestingPlacement
    {n k : ℕ} {AB : Finset ℕ × Finset ℕ}
    (hAB : AB ∈ Finset.orderedKSubsetPairs n k) :
    (truncatedStaircase n n).IsNonNestingPlacement
      (orderedSubsetPairFullStaircasePlacement n AB) := by
  classical
  rcases AB with ⟨A, B⟩
  rw [Finset.mem_orderedKSubsetPairs] at hAB
  rcases hAB with ⟨_hA, hAcard, hB, hBcard, hle⟩
  let rows := A.sort (· ≤ ·)
  let cols := B.sort (· ≤ ·)
  let cols' := cols.map fun b => n - 1 - b
  let L := rows.zip cols'
  have hle_rows_cols : List.Forall₂ (· ≤ ·) rows cols := by simpa [rows, cols] using hle
  have hL_nodup : L.Nodup := by
    simpa [L, rows, cols, cols'] using
      orderedSubsetPairFullStaircasePlacement_list_nodup n (by rw [hAcard, hBcard])
  change (truncatedStaircase n n).IsNonNestingPlacement L.toFinset
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxL : x ∈ L := by simpa using hx
    rcases List.getElem_of_mem hxL with ⟨i, hi, hix⟩
    have hi_rows : i < rows.length := List.lt_length_left_of_zip hi
    have hi_cols' : i < cols'.length := List.lt_length_right_of_zip hi
    have hi_cols : i < cols.length := by simpa [cols'] using hi_cols'
    have hx_eq : x = (rows[i], n - 1 - cols[i]) := by
      rw [← hix, List.getElem_zip]
      simp [cols']
    rw [hx_eq]
    rw [mem_truncatedStaircase_full_cells_iff]
    have hcol_mem : cols[i] ∈ B := by
      rw [← Finset.mem_sort (s := B) (r := (· ≤ ·))]
      exact List.getElem_mem hi_cols
    have hcol_lt : cols[i] < n := Finset.mem_range.mp (hB hcol_mem)
    have hle_i : rows[i] ≤ cols[i] := by simpa using hle_rows_cols.get hi_rows hi_cols
    lia
  · intro x hx y hy hne hrow_eq
    have hxL : x ∈ L := by simpa using hx
    have hyL : y ∈ L := by simpa using hy
    rcases List.getElem_of_mem hxL with ⟨i, hi, hix⟩
    rcases List.getElem_of_mem hyL with ⟨j, hj, hjy⟩
    have hi_rows : i < rows.length := List.lt_length_left_of_zip hi
    have hj_rows : j < rows.length := List.lt_length_left_of_zip hj
    have hrow_L : (L[i]).1 = (L[j]).1 := by
      rw [hix, hjy]
      exact hrow_eq
    have hrow_i_j : rows[i] = rows[j] := by simpa [L, cols'] using hrow_L
    have hij : i = j := (List.getElem_inj (A.sort_nodup (· ≤ ·))).mp (by
      simpa [rows] using hrow_i_j)
    subst j
    exact hne (by rw [← hix, ← hjy])
  · intro x hx y hy hrow_lt
    have hxL : x ∈ L := by simpa using hx
    have hyL : y ∈ L := by simpa using hy
    rcases List.getElem_of_mem hxL with ⟨i, hi, hix⟩
    rcases List.getElem_of_mem hyL with ⟨j, hj, hjy⟩
    have hi_rows : i < rows.length := List.lt_length_left_of_zip hi
    have hj_rows : j < rows.length := List.lt_length_left_of_zip hj
    have hi_cols' : i < cols'.length := List.lt_length_right_of_zip hi
    have hj_cols' : j < cols'.length := List.lt_length_right_of_zip hj
    have hi_cols : i < cols.length := by simpa [cols'] using hi_cols'
    have hj_cols : j < cols.length := by simpa [cols'] using hj_cols'
    have hx_eq : x = (rows[i], n - 1 - cols[i]) := by
      rw [← hix, List.getElem_zip]
      simp [cols']
    have hy_eq : y = (rows[j], n - 1 - cols[j]) := by
      rw [← hjy, List.getElem_zip]
      simp [cols']
    have hij_lt : i < j := by
      have hrows_sorted : rows.SortedLE := by simpa [rows] using (Finset.sortedLT_sort A).sortedLE
      have hrow_ij : rows[i] < rows[j] := by simpa [hx_eq, hy_eq] using hrow_lt
      by_contra hnot
      have hji : j ≤ i := le_of_not_gt hnot
      have hle_ji : rows[j] ≤ rows[i] :=
        (List.sortedLE_iff_getElem_le_getElem_of_le.mp hrows_sorted) hji
      exact not_lt_of_ge hle_ji hrow_ij
    have hcols_pairwise : List.Pairwise (· < ·) cols := by
      simpa [cols] using (Finset.sortedLT_sort B).pairwise
    have hcol_lt : cols[i] < cols[j] := by
      exact (List.pairwise_iff_getElem.mp hcols_pairwise) i j hi_cols hj_cols hij_lt
    have hcolj_mem : cols[j] ∈ B := by
      rw [← Finset.mem_sort (s := B) (r := (· ≤ ·))]
      exact List.getElem_mem hj_cols
    have hcolj_lt : cols[j] < n := Finset.mem_range.mp (hB hcolj_mem)
    rw [hx_eq, hy_eq]
    dsimp
    lia

/-- The row projection of the placement constructed from an ordered subset pair
recovers the first subset. -/
theorem fullStaircaseReflectedPairRows_orderedSubsetPairFullStaircasePlacement
    {n k : ℕ} {A B : Finset ℕ}
    (hAB : (A, B) ∈ Finset.orderedKSubsetPairs n k) :
    fullStaircaseReflectedPairRows n
      (orderedSubsetPairFullStaircasePlacement n (A, B)) = A := by
  classical
  rw [Finset.mem_orderedKSubsetPairs] at hAB
  rcases hAB with ⟨_hA, hAcard, _hB, hBcard, _hle⟩
  rw [fullStaircaseReflectedPairRows_eq_image_fst]
  ext a
  have hlen :
      (A.sort (· ≤ ·)).length ≤ ((B.sort (· ≤ ·)).map fun b => n - 1 - b).length := by
    rw [List.length_map, Finset.length_sort, Finset.length_sort, hAcard, hBcard]
  have hmap :
      List.map Prod.fst ((A.sort (· ≤ ·)).zip
        ((B.sort (· ≤ ·)).map fun b => n - 1 - b)) = A.sort (· ≤ ·) :=
    List.map_fst_zip hlen
  constructor
  · rw [Finset.mem_image]
    rintro ⟨x, hx, rfl⟩
    rw [orderedSubsetPairFullStaircasePlacement, List.mem_toFinset] at hx
    have hxmap : x.1 ∈ List.map Prod.fst
        ((A.sort (· ≤ ·)).zip ((B.sort (· ≤ ·)).map fun b => n - 1 - b)) :=
      List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap, Finset.mem_sort] at hxmap
    exact hxmap
  · intro ha
    rw [Finset.mem_image]
    have hasort : a ∈ A.sort (· ≤ ·) := by rwa [Finset.mem_sort]
    rw [← hmap] at hasort
    rcases List.mem_map.mp hasort with ⟨x, hx, hx_fst⟩
    refine ⟨x, ?_, hx_fst⟩
    rw [orderedSubsetPairFullStaircasePlacement, List.mem_toFinset]
    exact hx

/-- The reflected-column projection of the placement constructed from an
ordered subset pair recovers the second subset. -/
theorem fullStaircaseReflectedPairColumns_orderedSubsetPairFullStaircasePlacement
    {n k : ℕ} {A B : Finset ℕ}
    (hAB : (A, B) ∈ Finset.orderedKSubsetPairs n k) :
    fullStaircaseReflectedPairColumns n
      (orderedSubsetPairFullStaircasePlacement n (A, B)) = B := by
  classical
  rw [Finset.mem_orderedKSubsetPairs] at hAB
  rcases hAB with ⟨_hA, hAcard, hB, hBcard, _hle⟩
  rw [fullStaircaseReflectedPairColumns_eq_image_reflectedColumn]
  ext b
  let rows := A.sort (· ≤ ·)
  let cols := B.sort (· ≤ ·)
  let cols' := cols.map fun b => n - 1 - b
  let L := rows.zip cols'
  have hlen : rows.length = cols.length := by simp [rows, cols, Finset.length_sort, hAcard, hBcard]
  constructor
  · rw [Finset.mem_image]
    rintro ⟨x, hx, hx_reflect⟩
    have hxL : x ∈ L := by
      simpa [orderedSubsetPairFullStaircasePlacement, L, rows, cols, cols'] using hx
    rcases List.getElem_of_mem hxL with ⟨i, hi, hix⟩
    have hi_cols' : i < cols'.length := List.lt_length_right_of_zip hi
    have hi_cols : i < cols.length := by simpa [cols'] using hi_cols'
    have hx_eq : x = (rows[i], n - 1 - cols[i]) := by
      rw [← hix, List.getElem_zip]
      simp [cols']
    have hcol_mem : cols[i] ∈ B := by
      rw [← Finset.mem_sort (s := B) (r := (· ≤ ·))]
      exact List.getElem_mem hi_cols
    have hcol_lt : cols[i] < n := Finset.mem_range.mp (hB hcol_mem)
    have hb_eq : b = cols[i] := by
      rw [← hx_reflect, hx_eq]
      dsimp
      lia
    rwa [hb_eq]
  · intro hb
    rw [Finset.mem_image]
    have hbsort : b ∈ cols := by
      change b ∈ B.sort (· ≤ ·)
      rwa [Finset.mem_sort]
    rcases List.getElem_of_mem hbsort with ⟨i, hi_cols, hib⟩
    have hi_rows : i < rows.length := by
      rw [hlen]
      exact hi_cols
    have hi_cols' : i < cols'.length := by simpa [cols'] using hi_cols
    have hiL : i < L.length := by simp [L, cols', List.length_zip, hlen, hi_cols]
    refine ⟨(rows[i], n - 1 - b), ?_, ?_⟩
    · rw [orderedSubsetPairFullStaircasePlacement, List.mem_toFinset]
      have hmemL : L[i] ∈ L := List.getElem_mem hiL
      have hmem : (rows[i], cols'[i]) ∈ L := by simpa [L, List.getElem_zip (h := hiL)] using hmemL
      simpa [L, rows, cols, cols', hib] using hmem
    · have hb_lt : b < n := Finset.mem_range.mp (hB hb)
      dsimp
      lia

/-- Projecting the placement constructed from an ordered subset pair recovers
that ordered subset pair. -/
theorem fullStaircasePlacementOrderedPair_orderedSubsetPairFullStaircasePlacement
    {n k : ℕ} {AB : Finset ℕ × Finset ℕ}
    (hAB : AB ∈ Finset.orderedKSubsetPairs n k) :
    fullStaircasePlacementOrderedPair n
      (orderedSubsetPairFullStaircasePlacement n AB) = AB := by
  rcases AB with ⟨A, B⟩
  rw [fullStaircasePlacementOrderedPair]
  exact Prod.ext
    (fullStaircaseReflectedPairRows_orderedSubsetPairFullStaircasePlacement hAB)
    (fullStaircaseReflectedPairColumns_orderedSubsetPairFullStaircasePlacement hAB)

/-- Reflecting the lexicographically sorted reflected-pair list back gives the
original placement. -/
theorem IsNonNestingPlacement.fullStaircaseReflectedPairLexList_reflectBack_toFinset
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    ((fullStaircaseReflectedPairLexList n P).map fun x => (x.1, n - 1 - x.2)).toFinset =
      P := by
  classical
  ext a
  rw [List.mem_toFinset]
  constructor
  · intro ha_map
    rcases List.mem_map.mp ha_map with ⟨x, hx, hxa⟩
    rw [← hxa]
    have hx_pairs : x ∈ fullStaircaseReflectedPairs n P :=
      mem_fullStaircaseReflectedPairLexList.mp hx
    rcases mem_fullStaircaseReflectedPairs.mp hx_pairs with ⟨b, hb, rfl⟩
    have hb_cell := hP.1 hb
    rw [mem_truncatedStaircase_full_cells_iff] at hb_cell
    have hback : (b.1, n - 1 - (n - 1 - b.2)) = b := by ext <;> simp; lia
    simpa [hback] using hb
  · intro ha
    apply List.mem_map.mpr
    refine ⟨(a.1, n - 1 - a.2), ?_, ?_⟩
    · rw [mem_fullStaircaseReflectedPairLexList]
      exact mem_fullStaircaseReflectedPairs.mpr ⟨a, ha, rfl⟩
    · have ha_cell := hP.1 ha
      rw [mem_truncatedStaircase_full_cells_iff] at ha_cell
      ext <;> simp; lia

/-- Constructing an ordered pair from a full-staircase placement and then
constructing a placement recovers the original placement. -/
theorem IsNonNestingPlacement.orderedSubsetPairFullStaircasePlacement_projection
    {n : ℕ} {P : Finset (ℕ × ℕ)}
    (hP : (truncatedStaircase n n).IsNonNestingPlacement P) :
    orderedSubsetPairFullStaircasePlacement n
      (fullStaircasePlacementOrderedPair n P) = P := by
  rw [orderedSubsetPairFullStaircasePlacement, fullStaircasePlacementOrderedPair]
  rw [hP.fullStaircaseReflectedPairRows_sort,
    hP.fullStaircaseReflectedPairColumns_sort]
  rw [fullStaircaseReflectedRowList, fullStaircaseReflectedColumnList]
  simp only [List.map_map]
  rw [List.zip_map']
  exact hP.fullStaircaseReflectedPairLexList_reflectBack_toFinset

/-- Size-`k` non-nesting placements in the full truncated staircase are counted
by ordered `k`-subset pairs. -/
theorem card_fullStaircasePlacements_eq_orderedKSubsetPairs (n k : ℕ) :
    (((truncatedStaircase n n).nonNestingPlacements.filter fun P => P.card = k).card) =
      (Finset.orderedKSubsetPairs n k).card := by
  classical
  refine Finset.card_bij'
    (fun P _hP => fullStaircasePlacementOrderedPair n P)
    (fun AB _hAB => orderedSubsetPairFullStaircasePlacement n AB)
    ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter] at hP
    have hvalid := mem_nonNestingPlacements.mp hP.1
    exact hvalid.mem_orderedKSubsetPairs_fullStaircasePlacementOrderedPair hP.2
  · intro AB hAB
    rw [Finset.mem_filter, mem_nonNestingPlacements]
    exact ⟨orderedSubsetPairFullStaircasePlacement_isNonNestingPlacement hAB,
      orderedSubsetPairFullStaircasePlacement_card hAB⟩
  · intro P hP
    rw [Finset.mem_filter] at hP
    exact (mem_nonNestingPlacements.mp hP.1).orderedSubsetPairFullStaircasePlacement_projection
  · intro AB hAB
    exact fullStaircasePlacementOrderedPair_orderedSubsetPairFullStaircasePlacement hAB

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
