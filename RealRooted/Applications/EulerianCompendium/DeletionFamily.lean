module

public import RealRooted.EulerianCompletion

/-!
# The deletion-stable family

The positive two-step definition below is equation `eq:largerDecomposition`.
It avoids subtraction in coefficient and degree inductions. The signed
one-step identity `eq:largerRecurrence` is proved from it.
-/

@[expose] public noncomputable section

open Polynomial RealRooted

namespace RealRooted.EulerianCompendium

/-- The family `Q_r^(a)` in `thm:largerFamily`, in its two-step form. -/
def deletionPolynomial (a : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C ((a : ℝ) + 1) * X
  | r + 2 => eulerInsertionStep 1 (a + r) (deletionPolynomial a r) +
      eulerInsertionStep 0 (a + r + 1) (deletionPolynomial a (r + 1))

/-- The two Euler operators differ by the identity operator. -/
private lemma eulerInsertionStep_one_sub_zero (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep 1 d p - eulerInsertionStep 0 d p = p := by
  simp only [eulerInsertionStep, map_one, map_zero]
  ring

/-- The signed one-step recurrence of `eq:largerRecurrence`. -/
theorem deletionPolynomial_recurrence (a r : ℕ) :
    deletionPolynomial a (r + 1) =
      eulerInsertionStep 1 (a + r) (deletionPolynomial a r) + C ((-1 : ℝ) ^ (r + 1)) := by
  induction r with
  | zero => simp [deletionPolynomial, eulerInsertionStep]
  | succ r ih =>
      rw [show r + 1 + 1 = r + 2 by rfl, deletionPolynomial]
      have h := eulerInsertionStep_one_sub_zero (a + r + 1)
        (deletionPolynomial a (r + 1))
      rw [pow_succ, map_mul, map_neg, map_one]
      simp only [Nat.add_assoc] at *
      linear_combination -ih - h

/-- Degree and coefficient positivity needed in `thm:largerFamily`. -/
theorem deletionPolynomial_degree_nonneg (a r : ℕ) :
    (deletionPolynomial a r).natDegree = r ∧
      HasPosLeadingCoeff (deletionPolynomial a r) ∧
      HasNonnegCoeffs (deletionPolynomial a r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [deletionPolynomial, HasPosLeadingCoeff, hasNonnegCoeffs_one]
  | one =>
      have ha : 0 < (a : ℝ) + 1 := by positivity
      refine ⟨?_, ?_, ?_⟩
      · change (C ((a : ℝ) + 1) * X).natDegree = 1
        rw [natDegree_C_mul ha.ne', natDegree_X]
      · change 0 < (C ((a : ℝ) + 1) * X).leadingCoeff
        rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
        exact ha
      · exact hasNonnegCoeffs_C_mul ha.le hasNonnegCoeffs_X
  | more r hprev hcur =>
      have hleft := eulerInsertionStep_degree_pos (c := (1 : ℝ))
        (d := a + r) (by rw [hprev.1]; lia) hprev.2.1
      have hright := eulerInsertionStep_degree_pos (c := (0 : ℝ))
        (d := a + r + 1) (by rw [hcur.1]; lia) hcur.2.1
      have hlt : (eulerInsertionStep 1 (a + r) (deletionPolynomial a r)).natDegree <
          (eulerInsertionStep 0 (a + r + 1) (deletionPolynomial a (r + 1))).natDegree := by
        rw [hleft.1, hright.1, hprev.1, hcur.1]
        lia
      refine ⟨?_, ?_, ?_⟩
      · rw [deletionPolynomial, natDegree_add_eq_right_of_natDegree_lt hlt,
          hright.1, hcur.1]
      · change 0 < (_ + _ : ℝ[X]).leadingCoeff
        rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hlt)]
        exact hright.2
      · exact (hprev.2.2.eulerInsertionStep (by norm_num) (by rw [hprev.1]; lia)).add
          (hcur.2.2.eulerInsertionStep (by norm_num) (by rw [hcur.1]; lia))

end RealRooted.EulerianCompendium
