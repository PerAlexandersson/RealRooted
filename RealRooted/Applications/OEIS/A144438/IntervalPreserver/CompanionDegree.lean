import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Degree
import RealRooted.Interlacing.ResidueCriterion

/-!
# Degree of the A144438 diagonal companion

The two nominal degree-`n` terms in the companion basis cancel.  We express
that cancellation through the existing `residueAuxiliary_degree_lt` theorem,
then transport the resulting supportwise bound through the basis transform.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Every positive-index companion basis element has degree below its index. -/
theorem a144438CompanionBasis_degree_lt {n : ℕ} (hn : 1 ≤ n) :
    (a144438CompanionBasis n).degree < n := by
  have hdeco : 1 ≤ (decoEulerian n).natDegree := by
    rw [decoEulerian_natDegree]
    exact hn
  have hzero : (0 : ℝ[X]).degree < (decoEulerian n).natDegree := by simp
  have haux := residueAuxiliary_degree_lt hdeco hzero 1 0
  have hform :
      a144438CompanionBasis n =
        residueAuxiliary 1 0 (decoEulerian n) 0 + a144438LagBasis n := by
    simp [a144438CompanionBasis, residueAuxiliary]
    ring
  rw [hform]
  apply (degree_add_le _ _).trans_lt
  rw [max_lt_iff]
  constructor
  · simpa [decoEulerian_natDegree] using haux
  · calc
      (a144438LagBasis n).degree ≤
          ((a144438LagBasis n).natDegree : WithBot ℕ) := degree_le_natDegree
      _ < n := by
        rw [a144438LagBasis_natDegree]
        exact_mod_cast Nat.sub_lt hn zero_lt_one

/-- Natural-degree form of the companion-basis cancellation, including the
zero-index case. -/
theorem a144438CompanionBasis_natDegree_le (n : ℕ) :
    (a144438CompanionBasis n).natDegree ≤ n - 1 := by
  cases n with
  | zero => simp [a144438CompanionBasis, a144438LagBasis, decoEulerian]
  | succ n =>
      have hlt := a144438CompanionBasis_degree_lt (n := n + 1) (by lia)
      by_cases hzero : a144438CompanionBasis (n + 1) = 0
      · simp [hzero]
      · have hnat : (a144438CompanionBasis (n + 1)).natDegree < n + 1 :=
          (natDegree_lt_iff_degree_lt hzero).2 hlt
        lia

/-- At positive rank the diagonal companion has degree strictly below the
diagonal transform. -/
theorem a144438DiagonalCompanion_natDegree_lt {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (a144438DiagonalCompanion n a).natDegree < n := by
  have hinputDegree : ((X + C a) ^ n).natDegree = n := by
    rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
    simp
  unfold a144438DiagonalCompanion a144438CompanionTransform
  refine lt_of_le_of_lt
    (Polynomial.basisTransform_natDegree_le_of_support ?_) (Nat.sub_lt hn zero_lt_one)
  intro m hm
  refine (a144438CompanionBasis_natDegree_le m).trans ?_
  have hmle : m ≤ n := by
    rw [← hinputDegree]
    exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hm)
  exact Nat.sub_le_sub_right hmle 1

/-- Degree form of `a144438DiagonalCompanion_natDegree_lt`, ready for the
residue expansion API. -/
theorem a144438DiagonalCompanion_degree_lt {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (a144438DiagonalCompanion n a).degree < n := by
  calc
    (a144438DiagonalCompanion n a).degree ≤
        ((a144438DiagonalCompanion n a).natDegree : WithBot ℕ) := degree_le_natDegree
    _ < n := by exact_mod_cast a144438DiagonalCompanion_natDegree_lt hn a

end RealRooted.Applications.OEIS
