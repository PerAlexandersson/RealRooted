import RealRooted.Compatibility.Affine
import RealRooted.Compatibility.CutTransform
import RealRooted.SameDegreeQuadraticObstruction

/-!
# Obstruction to the ten-field cut invariant

The ordered P/Q conditions hold for the explicit two-coordinate family below,
but its first cut transform loses the all-index P/Q compatibility clause.  The
example isolates the missing opposite-direction `XP/P` relation required by a
preservation theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted.CutTransformObstruction

/-- Constant terms of the P-family. -/
def pConst : Fin 2 → ℝ := ![1, 4]

/-- The P-family in the two-coordinate obstruction. -/
def P (i : Fin 2) : ℝ[X] := C 1 * X + C (pConst i)

/-- Constant terms of the Q-family. -/
def qConst : Fin 2 → ℝ := ![1, 0]

/-- The Q-family in the two-coordinate obstruction. -/
def Q (i : Fin 2) : ℝ[X] := C 1 * X + C (qConst i)

private theorem pConst_nonneg (i : Fin 2) : 0 ≤ pConst i := by
  fin_cases i <;> norm_num [pConst]

private theorem qConst_nonneg (i : Fin 2) : 0 ≤ qConst i := by
  fin_cases i <;> norm_num [qConst]

private theorem P_nonneg (i : Fin 2) : HasNonnegCoeffs (P i) := by
  exact (nonnegCoeffs_C_mul zero_le_one hasNonnegCoeffs_X).add
    (hasNonnegCoeffs_C (pConst_nonneg i))

private theorem Q_nonneg (i : Fin 2) : HasNonnegCoeffs (Q i) := by
  exact (nonnegCoeffs_C_mul zero_le_one hasNonnegCoeffs_X).add
    (hasNonnegCoeffs_C (qConst_nonneg i))

private theorem P_pos (i : Fin 2) : HasPosLeadingCoeff (P i) := by
  apply P_nonneg i |>.pos_leadingCoeff
  exact (isRealRooted_affine_factor
    (s := 1) (t := pConst i) (by norm_num)).1

private theorem Q_pos (i : Fin 2) : HasPosLeadingCoeff (Q i) := by
  apply Q_nonneg i |>.pos_leadingCoeff
  exact (isRealRooted_affine_factor
    (s := 1) (t := qConst i) (by norm_num)).1

private theorem P_degree (i : Fin 2) : (P i).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_linear
    (a := 1) (b := pConst i) one_ne_zero).le

private theorem Q_degree (i : Fin 2) : (Q i).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_linear
    (a := 1) (b := qConst i) one_ne_zero).le

private theorem xpp_reverse {i j : Fin 2} (hij : i ≤ j) :
    Compatible (X * P j) (P i) := by
  have hcross : (1 : ℝ) * pConst i ≤ 1 * pConst j := by
    fin_cases i <;> fin_cases j
    · norm_num [pConst]
    · norm_num [pConst]
    · simp at hij
    · norm_num [pConst]
  exact compatible_X_mul_affine_affine_of_cross
    (u := 1) (v := pConst j) (U := 1) (V := pConst i)
    (by norm_num) (by norm_num) (pConst_nonneg j) (pConst_nonneg i) hcross

private theorem xpq (i j : Fin 2) : Compatible (X * P i) (Q j) := by
  apply compatible_X_mul_affine_affine_of_cross
    (u := 1) (v := pConst i) (U := 1) (V := qConst j)
  · norm_num
  · norm_num
  · exact pConst_nonneg i
  · exact qConst_nonneg j
  · fin_cases i <;> fin_cases j <;> norm_num [pConst, qConst]

private theorem xqq_forward {i j : Fin 2} (hij : i ≤ j) :
    Compatible (X * Q i) (Q j) := by
  have hcross : (1 : ℝ) * qConst j ≤ 1 * qConst i := by
    fin_cases i <;> fin_cases j
    · norm_num [qConst]
    · norm_num [qConst]
    · simp at hij
    · norm_num [qConst]
  exact compatible_X_mul_affine_affine_of_cross
    (u := 1) (v := qConst i) (U := 1) (V := qConst j)
    (by norm_num) (by norm_num) (qConst_nonneg i) (qConst_nonneg j) hcross

/-- The explicit input family satisfies every field of the initial ordered
cut invariant. -/
theorem orderedCutCompatible : OrderedCutCompatible P Q where
  p_pos := P_pos
  p_nonneg := P_nonneg
  q_pos := Q_pos
  q_nonneg := Q_nonneg
  pp_reverse := fun {_ _} _ =>
    Compatible.of_posLeadingCoeff_natDegree_le_one
      (P_pos _) (P_pos _) (P_degree _) (P_degree _)
  xpp_reverse := fun {_ _} hij => xpp_reverse hij
  pq := fun i j => Compatible.of_posLeadingCoeff_natDegree_le_one
    (P_pos i) (Q_pos j) (P_degree i) (Q_degree j)
  xpq := xpq
  qq_forward := fun {_ _} _ =>
    Compatible.of_posLeadingCoeff_natDegree_le_one
      (Q_pos _) (Q_pos _) (Q_degree _) (Q_degree _)
  xqq_forward := fun {_ _} hij => xqq_forward hij

/-- The last unmarked cut output is `2X + 5`. -/
theorem cutTransformP_one :
    cutTransformP P Q 1 = 2 * X + 5 := by
  norm_num [cutTransformP, cutPrefix, cutStrictSuffix, P, Q, pConst, qConst,
    Fin.sum_univ_two]
  have hconst : (1 : ℝ[X]) + C 4 = 5 := by
    change C 1 + C 4 = C 5
    rw [← C_add]
    norm_num
  calc
    (X : ℝ[X]) + 1 + (X + C 4) = 2 * X + (1 + C 4) := by ring
    _ = 2 * X + 5 := by rw [hconst]

/-- The first marked cut output is `X² + 2X`. -/
theorem cutTransformQ_zero :
    cutTransformQ P Q 0 = X ^ 2 + 2 * X := by
  simp [cutTransformQ, cutPrefix, cutStrictSuffix, P, Q, pConst, qConst,
    Fin.sum_univ_two]
  ring

/-- The unit-weight combination of the two selected outputs has negative
quadratic discriminant. -/
theorem cut_pair_sum :
    cutTransformP P Q 1 + cutTransformQ P Q 0 =
      X ^ 2 + 4 * X + 5 := by
  rw [cutTransformP_one, cutTransformQ_zero]
  ring

/-- The selected output P/Q pair is not compatible. -/
theorem not_compatible_cut_pair :
    ¬ Compatible (cutTransformP P Q 1) (cutTransformQ P Q 0) := by
  intro hcompatible
  have hsum := hcompatible 1 1 zero_le_one zero_le_one
  have hnot : ¬ (C 1 * X ^ 2 + C 4 * X + C 5 : ℝ[X]).Splits :=
    not_splits_quadratic_of_discrim_neg (by norm_num) (by norm_num [discrim])
  simp only [map_one, one_mul] at hsum
  rw [cut_pair_sum] at hsum
  rcases hsum with hzero | hrr
  · have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
    norm_num at hcoeff
  · apply hnot
    simpa [← map_ofNat Polynomial.C] using hrr.2

/-- The ten-field ordered invariant is not preserved by the P/Q cut
transform. -/
theorem not_preserved :
    OrderedCutCompatible P Q ∧
      ¬ OrderedCutCompatible (cutTransformP P Q) (cutTransformQ P Q) := by
  refine ⟨orderedCutCompatible, ?_⟩
  intro hout
  exact not_compatible_cut_pair (hout.pq 1 0)

end RealRooted.CutTransformObstruction
