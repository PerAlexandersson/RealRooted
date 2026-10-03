import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ResidueSums
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Energy

/-! # Endpoint residue sums for the weighted diagonal family -/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDecoDiagonalCompanion_eval_one_div {w : ℝ} (hw : 0 ≤ w)
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    (weightedDecoDiagonalCompanion w n a).eval 1 /
        (weightedDecoDiagonal w n a).eval 1 =
      (n : ℝ) - weightedDecoEta w n a + w * weightedDecoKappa w n a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m]
  have hp := weightedDecoDiagonal_eval_one_pos hw (n := m) ha
  have hpSucc := weightedDecoDiagonal_eval_one_pos hw (n := m + 1) ha
  rw [weightedDecoDiagonalCompanion_succ_eq]
  simp only [eval_add, eval_sub, eval_mul, eval_one, eval_X, eval_C,
    sub_self, zero_mul, zero_add]
  rw [weightedDecoEta, weightedDecoGamma, weightedDecoKappa]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    weightedDecoDiagonalAtOne, weightedDecoDiagonalLagAtOne]
  field_simp [hp.ne', hpSucc.ne']

theorem weightedDecoDiagonalLag_residue_sum_eq_kappa
    {w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hsplits : (weightedDecoDiagonal w n a).Splits)
    (hnodup : (weightedDecoDiagonal w n a).roots.Nodup) :
    ∑ r ∈ (weightedDecoDiagonal w n a).roots.toFinset,
        ((weightedDecoDiagonalLag w n a).eval r /
          (weightedDecoDiagonal w n a).derivative.eval r) / (1 - r) =
      weightedDecoKappa w n a := by
  have hpOne := weightedDecoDiagonal_eval_one_pos hw (n := n) ha
  have hsum := a144438_sum_companion_residue_div hsplits hnodup
    (by rw [weightedDecoDiagonal_natDegree]; exact hn) (by
      rw [weightedDecoDiagonal_natDegree]
      exact weightedDecoDiagonalLag_degree_lt w hn a) hpOne.ne'
  rw [← hsum]
  rfl

theorem weightedDecoDiagonalCompanion_residue_sum_eq
    {w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hsplits : (weightedDecoDiagonal w n a).Splits)
    (hnodup : (weightedDecoDiagonal w n a).roots.Nodup) :
    ∑ r ∈ (weightedDecoDiagonal w n a).roots.toFinset,
        ((weightedDecoDiagonalCompanion w n a).eval r /
          (weightedDecoDiagonal w n a).derivative.eval r) / (1 - r) =
      (n : ℝ) - weightedDecoEta w n a + w * weightedDecoKappa w n a := by
  have hpOne := weightedDecoDiagonal_eval_one_pos hw (n := n) ha
  have hsum := a144438_sum_companion_residue_div hsplits hnodup
    (by rw [weightedDecoDiagonal_natDegree]; exact hn) (by
      rw [weightedDecoDiagonal_natDegree]
      exact weightedDecoDiagonalCompanion_degree_lt w hn a) hpOne.ne'
  rw [← hsum]
  exact weightedDecoDiagonalCompanion_eval_one_div hw hn ha

end RealRooted.Applications.OEIS
