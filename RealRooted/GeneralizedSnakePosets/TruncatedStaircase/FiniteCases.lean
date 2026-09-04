import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.BottomRow

/-!
# Explicit finite truncated-staircase cases

This module certifies the small truncated-staircase rook polynomials used by
the finite Braun--Jal recurrence checks.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

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
          have hne : (0, 0) ≠ (0, 1) := by norm_num
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
  have hplacements_nodup : placements.Nodup := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (1, 0)} : Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 2 2).cells = cells := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)} :
      Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 3 3).cells = cells := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)} : Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 5 1).cells = cells := by decide
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
  have hplacements_nodup : placements.Nodup := by decide
  let cells : Finset (ℕ × ℕ) :=
    ({(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2),
      (1, 3)} : Finset (ℕ × ℕ))
  have hcells : (truncatedStaircase 5 2).cells = cells := by decide
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

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
