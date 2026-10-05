import RealRooted.Applications.OEIS.A144438.IntervalPreserver.CompanionDegree
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Energy

/-!
# Endpoint residue sums for the A144438 diagonal family

These are the two partial-fraction evaluations used in the Schur complement:
the lag residues sum to `κₙ` at `x = 1`, while the companion residues sum
to `n - ηₙ + κₙ`.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The value of the diagonal companion at one, normalized by the current
diagonal transform. -/
theorem a144438DiagonalCompanion_eval_one_div {n : ℕ} (hn : 1 ≤ n)
    {a : ℝ} (ha : 0 ≤ a) :
    (a144438DiagonalCompanion n a).eval 1 /
        (a144438Diagonal n a).eval 1 =
      (n : ℝ) - a144438Eta n a + a144438Kappa n a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m]
  have hp := a144438Diagonal_eval_one_pos (n := m) ha
  have hpSucc := a144438Diagonal_eval_one_pos (n := m + 1) ha
  rw [a144438DiagonalCompanion_succ_eq]
  simp only [eval_add, eval_sub, eval_mul, eval_one, eval_X, eval_C,
    sub_self, zero_mul, zero_add]
  rw [a144438Eta, a144438Gamma, a144438Kappa]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    a144438DiagonalAtOne, a144438DiagonalLagAtOne]
  field_simp [hp.ne', hpSucc.ne']

/-- Evaluation at one of the lag partial-fraction expansion. -/
theorem a144438DiagonalLag_residue_sum_eq_kappa
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hsplits : (a144438Diagonal n a).Splits)
    (hnodup : (a144438Diagonal n a).roots.Nodup) :
    ∑ r ∈ (a144438Diagonal n a).roots.toFinset,
        ((a144438DiagonalLag n a).eval r /
          (a144438Diagonal n a).derivative.eval r) / (1 - r) =
      a144438Kappa n a := by
  have hpOne := a144438Diagonal_eval_one_pos (n := n) ha
  have hsum := a144438_sum_companion_residue_div hsplits hnodup
    (by rw [a144438Diagonal_natDegree]; exact hn) (by
      rw [a144438Diagonal_natDegree]
      exact a144438DiagonalLag_degree_lt hn a) hpOne.ne'
  rw [← hsum]
  rfl

/-- Evaluation at one of the companion partial-fraction expansion. -/
theorem a144438DiagonalCompanion_residue_sum_eq
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hsplits : (a144438Diagonal n a).Splits)
    (hnodup : (a144438Diagonal n a).roots.Nodup) :
    ∑ r ∈ (a144438Diagonal n a).roots.toFinset,
        ((a144438DiagonalCompanion n a).eval r /
          (a144438Diagonal n a).derivative.eval r) / (1 - r) =
      (n : ℝ) - a144438Eta n a + a144438Kappa n a := by
  have hpOne := a144438Diagonal_eval_one_pos (n := n) ha
  have hsum := a144438_sum_companion_residue_div hsplits hnodup
    (by rw [a144438Diagonal_natDegree]; exact hn) (by
      rw [a144438Diagonal_natDegree]
      exact a144438DiagonalCompanion_degree_lt hn a) hpOne.ne'
  rw [← hsum]
  exact a144438DiagonalCompanion_eval_one_div hn ha

end RealRooted.Applications.OEIS
