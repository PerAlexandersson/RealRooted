import RealRooted.Compatibility.Affine
import RealRooted.Compatibility.NDCutInvariant
import RealRooted.ParkingFunctions.Descents.WeakLeftPeakCutTransform

/-!
# The ordered weak-left-peak P/Q base family

This module gives closed formulas for the rank-zero terminal-state pair mixes
and proves that they satisfy the ordered cut-compatibility invariant.  It
contains no preservation claim for later ranks.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

private theorem card_fin_le (m : ℕ) (j : Fin m) :
    (Finset.univ.filter fun i : Fin m => i ≤ j).card = j.val + 1 := by
  have hset :
      (Finset.univ.filter fun i : Fin m => i ≤ j) = Finset.Iic j := by
    ext i
    simp
  rw [hset, Fin.card_Iic]

private theorem card_fin_gt (m : ℕ) (j : Fin m) :
    (Finset.univ.filter fun i : Fin m => j < i).card =
      m - (j.val + 1) := by
  have hset :
      (Finset.univ.filter fun i : Fin m => j < i) = Finset.Ioi j := by
    ext i
    simp
  rw [hset, Fin.card_Ioi, Nat.sub_sub]
  simp [Nat.add_comm]

/-- At rank zero, the non-descent state counts letters weakly below `j`. -/
theorem terminalNonDescentReal_zero_closed (m : ℕ) (j : Fin m) :
    terminalNonDescentReal m 0 j = C ((j.val + 1 : ℕ) : ℝ) := by
  rw [terminalNonDescentReal,
    literalWordWeakLeftPeakTerminalNonDescentRefined_zero,
    Polynomial.map_sum]
  calc
    ∑ i : Fin m,
        map (Int.castRingHom ℝ) (if i ≤ j then 1 else 0) =
      ∑ i : Fin m, if i ≤ j then (1 : ℝ[X]) else 0 := by
        apply Fintype.sum_congr
        intro i
        by_cases hij : i ≤ j <;> simp [hij]
    _ = C ((j.val + 1 : ℕ) : ℝ) := by
      rw [← Finset.sum_filter]
      simp [card_fin_le]

/-- At rank zero, the descent state counts letters strictly above `j`. -/
theorem terminalDescentReal_zero_closed (m : ℕ) (j : Fin m) :
    terminalDescentReal m 0 j =
      C ((m - (j.val + 1) : ℕ) : ℝ) := by
  rw [terminalDescentReal,
    literalWordWeakLeftPeakTerminalDescentRefined_zero,
    Polynomial.map_sum]
  calc
    ∑ i : Fin m,
        map (Int.castRingHom ℝ) (if j < i then 1 else 0) =
      ∑ i : Fin m, if j < i then (1 : ℝ[X]) else 0 := by
        apply Fintype.sum_congr
        intro i
        by_cases hji : j < i <;> simp [hji]
    _ = C ((m - (j.val + 1) : ℕ) : ℝ) := by
      rw [← Finset.sum_filter]
      simp [card_fin_gt]

/-- Every rank-zero unmarked pair mix is the constant alphabet size. -/
theorem terminalPairMixReal_zero_closed (m : ℕ) (j : Fin m) :
    terminalPairMixReal m 0 j = C (m : ℝ) := by
  rw [terminalPairMixReal_eq, terminalNonDescentReal_zero_closed,
    terminalDescentReal_zero_closed, ← C_add]
  congr 1
  norm_num

/-- The rank-zero marked pair mix has the displayed positive-slope affine
form. -/
theorem terminalXPairMixReal_zero_closed (m : ℕ) (j : Fin m) :
    terminalXPairMixReal m 0 j =
      C ((j.val + 1 : ℕ) : ℝ) * X +
        C ((m - (j.val + 1) : ℕ) : ℝ) := by
  rw [terminalXPairMixReal_eq, terminalNonDescentReal_zero_closed,
    terminalDescentReal_zero_closed]
  ring

private theorem base_cross {m : ℕ} {i j : Fin m} (hij : i ≤ j) :
    ((i.val + 1 : ℕ) : ℝ) * (m - (j.val + 1) : ℕ) ≤
      ((j.val + 1 : ℕ) : ℝ) * (m - (i.val + 1) : ℕ) := by
  have hi : i.val + 1 ≤ m := Nat.succ_le_iff.mpr i.isLt
  have hj : j.val + 1 ≤ m := Nat.succ_le_iff.mpr j.isLt
  rw [Nat.cast_sub hi, Nat.cast_sub hj]
  have hij_real : (i.val : ℝ) ≤ j.val := by
    exact_mod_cast hij
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at ⊢
  have hproduct :
      0 ≤ ((j.val : ℝ) - i.val) * (m : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hij_real) hm_nonneg
  nlinarith

/-- The rank-zero weak-left-peak P/Q family satisfies all ten ordered cut
compatibility clauses, including the directed `XQ_i/Q_j` clause. -/
theorem terminalPairMixReal_orderedCutCompatible_zero (m : ℕ) :
    OrderedCutCompatible (terminalPairMixReal m 0)
      (terminalXPairMixReal m 0) := by
  have hm_pos (i : Fin m) : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hP_pos (i : Fin m) :
      HasPosLeadingCoeff (terminalPairMixReal m 0 i) := by
    rw [terminalPairMixReal_zero_closed]
    exact (hasNonnegCoeffs_C (hm_pos i).le).pos_leadingCoeff
      (C_ne_zero.mpr (hm_pos i).ne')
  have hP_nonneg (i : Fin m) :
      HasNonnegCoeffs (terminalPairMixReal m 0 i) := by
    rw [terminalPairMixReal_zero_closed]
    exact hasNonnegCoeffs_C (by positivity)
  have hP_deg (i : Fin m) :
      (terminalPairMixReal m 0 i).natDegree ≤ 1 := by
    rw [terminalPairMixReal_zero_closed]
    simp
  have hXP_pos (i : Fin m) :
      HasPosLeadingCoeff (X * terminalPairMixReal m 0 i) :=
    (hP_pos i).X_mul
  have hXP_deg (i : Fin m) :
      (X * terminalPairMixReal m 0 i).natDegree ≤ 1 := by
    rw [terminalPairMixReal_zero_closed]
    rw [natDegree_mul X_ne_zero (C_ne_zero.mpr (hm_pos i).ne')]
    simp
  have hQ_nonneg (i : Fin m) :
      HasNonnegCoeffs (terminalXPairMixReal m 0 i) := by
    rw [terminalXPairMixReal_zero_closed]
    exact
      (nonnegCoeffs_C_mul (by positivity) hasNonnegCoeffs_X).add
        (hasNonnegCoeffs_C (by positivity))
  have hQ_pos (i : Fin m) :
      HasPosLeadingCoeff (terminalXPairMixReal m 0 i) := by
    apply (hQ_nonneg i).pos_leadingCoeff
    rw [terminalXPairMixReal_zero_closed]
    exact (isRealRooted_affine_factor
      (s := (((i.val + 1 : ℕ) : ℝ)))
      (t := (((m - (i.val + 1) : ℕ) : ℝ))) (by positivity)).1
  have hQ_deg (i : Fin m) :
      (terminalXPairMixReal m 0 i).natDegree ≤ 1 := by
    rw [terminalXPairMixReal_zero_closed]
    simpa using
      (Polynomial.natDegree_linear
        (a := (((i.val + 1 : ℕ) : ℝ)))
        (b := (((m - (i.val + 1) : ℕ) : ℝ))) (by positivity)).le
  refine ⟨hP_pos, hP_nonneg, hQ_pos, hQ_nonneg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j _
    exact Compatible.of_posLeadingCoeff_natDegree_le_one
      (hP_pos j) (hP_pos i) (hP_deg j) (hP_deg i)
  · intro i j _
    exact Compatible.of_posLeadingCoeff_natDegree_le_one
      (hXP_pos j) (hP_pos i) (hXP_deg j) (hP_deg i)
  · intro i j
    exact Compatible.of_posLeadingCoeff_natDegree_le_one
      (hP_pos i) (hQ_pos j) (hP_deg i) (hQ_deg j)
  · intro i j
    exact Compatible.of_posLeadingCoeff_natDegree_le_one
      (hXP_pos i) (hQ_pos j) (hXP_deg i) (hQ_deg j)
  · intro i j _
    exact Compatible.of_posLeadingCoeff_natDegree_le_one
      (hQ_pos i) (hQ_pos j) (hQ_deg i) (hQ_deg j)
  · intro i j hij
    rw [terminalXPairMixReal_zero_closed,
      terminalXPairMixReal_zero_closed]
    exact compatible_X_mul_affine_affine_of_cross
      (by positivity) (by positivity) (by positivity) (by positivity)
      (base_cross hij)

/-- The rank-zero N/D states satisfy the structural cut invariant.  The final
descent coordinate is allowed to be zero by the zero-aware state order. -/
theorem terminalND_orderedNDCutCompatible_zero (m : ℕ) :
    OrderedNDCutCompatible (terminalNonDescentReal m 0)
      (terminalDescentReal m 0) := by
  refine ⟨?_, ?_⟩
  · change OrderedCutCompatible (terminalPairMixReal m 0)
      (terminalXPairMixReal m 0)
    exact terminalPairMixReal_orderedCutCompatible_zero m
  · apply isInterlacingSeq0NonnegRealRooted_of_mem_C_nonneg
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hp' :
        p ∈ List.ofFn (terminalNonDescentReal m 0) := by
        simpa [ndCutStateOrder] using hp
      simp only [List.mem_ofFn] at hp'
      rcases hp' with ⟨j, rfl⟩
      refine ⟨((j.val + 1 : ℕ) : ℝ), by positivity, ?_⟩
      exact terminalNonDescentReal_zero_closed m j
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨j, rfl⟩
      refine ⟨((m - (j.val + 1) : ℕ) : ℝ), by positivity, ?_⟩
      exact terminalDescentReal_zero_closed m j

end

end RealRooted.ParkingFunctions
