/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.Identification
public import RealRooted.IntervalDifferential.Degree

/-!
# Degree of the finite centered zig-zag quotient

Each summand in Appendix A.6 is monic of degree `n - 2`. The alternating
class is nonempty, so its finite sum has exactly that degree.
-/

public noncomputable section

open Polynomial Finset RealRooted.IntervalDifferential

namespace RealRooted.ZigzagEulerian

open Classical in
/-- The coefficient of degree `n - 2` counts the actual alternating class. -/
theorem zigzagCenteredQuotient_top_coeff (n : ℕ) (hn : 2 ≤ n) :
    (zigzagCenteredQuotient n).coeff (n - 2) =
      (((univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown).card : ℝ) := by
  classical
  rw [zigzagCenteredQuotient, finsetSum_coeff]
  have hcoeff (π : Equiv.Perm (Fin n)) :
      (zigzagBasis (swapCount π) (n - 2 - swapCount π)).coeff (n - 2) = 1 := by
    have hd : (zigzagBasis (swapCount π) (n - 2 - swapCount π)).natDegree =
        n - 2 := by
      rw [zigzagBasis_natDegree]
      have h := swapCount_le_sub_two hn π
      lia
    simpa only [hd] using
      (zigzagBasis_monic (swapCount π) (n - 2 - swapCount π)).coeff_natDegree
  simp_rw [hcoeff]
  simp

/-- The finite centered quotient has degree exactly `n - 2`. -/
theorem zigzagCenteredQuotient_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (zigzagCenteredQuotient n).natDegree = n - 2 := by
  classical
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [zigzagCenteredQuotient]
    apply natDegree_sum_le_of_forall_le
    intro π _
    rw [zigzagBasis_natDegree]
    have h := swapCount_le_sub_two hn π
    lia
  · rw [zigzagCenteredQuotient_top_coeff n hn]
    have hw : zigzagWitness n ∈
        (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown :=
      mem_filter.mpr ⟨mem_univ _, zigzagWitness_isUpDown n⟩
    have hc := card_pos.mpr ⟨zigzagWitness n, hw⟩
    exact_mod_cast (ne_of_gt hc)

/-- The finite centered quotient never vanishes, including the constant case. -/
theorem zigzagCenteredQuotient_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    zigzagCenteredQuotient n ≠ 0 := by
  classical
  intro hzero
  have h := zigzagCenteredQuotient_top_coeff n hn
  rw [hzero, Polynomial.coeff_zero] at h
  have hw : zigzagWitness n ∈
      (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown :=
    mem_filter.mpr ⟨mem_univ _, zigzagWitness_isUpDown n⟩
  have hc := card_pos.mpr ⟨zigzagWitness n, hw⟩
  have hcReal : (0 : ℝ) <
      (((univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown).card : ℝ) := by
    exact_mod_cast hc
  linarith

end RealRooted.ZigzagEulerian
