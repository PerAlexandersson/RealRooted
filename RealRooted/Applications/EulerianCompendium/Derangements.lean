import RealRooted.Applications.EulerianCompendium.Definitions
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Descent polynomials of derangements

These lemmas concern the actual fixed-point-free permutation sum of
`thm:derangementRealRooted`, without replacing descents by excedances.
They separate nonvanishing and the sign of real roots from the remaining
splitting assertion.
-/

open Polynomial RealRooted

noncomputable section

namespace RealRooted.EulerianCompendium

/-- The descent enumerator has nonnegative coefficients. -/
theorem derangementDescentPolynomial_nonneg (n : ℕ) :
    HasNonnegCoeffs (derangementDescentPolynomial n) := by
  classical
  apply hasNonnegCoeffs_finsetSum
  intro π _
  split
  · exact hasNonnegCoeffs_X.pow _
  · exact hasNonnegCoeffs_zero

/-- Rotation supplies a derangement as soon as there are at least two letters. -/
lemma exists_derangement (n : ℕ) (hn : 2 ≤ n) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, π i ≠ i := by
  cases n with
  | zero => lia
  | succ n =>
    refine ⟨finRotate (n + 1), ?_⟩
    intro i h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    split at hv
    · subst i
      simp at hv
      lia
    · lia

/-- Evaluation at one counts exactly the fixed-point-free permutations. -/
theorem derangementDescentPolynomial_eval_one (n : ℕ) :
    (derangementDescentPolynomial n).eval 1 =
      ((Finset.univ.filter fun π : Equiv.Perm (Fin n) => ∀ i, π i ≠ i).card : ℝ) := by
  classical
  simp only [derangementDescentPolynomial, eval_finsetSum]
  simp [apply_ite, eval_pow, eval_X, eval_zero]

/-- The actual derangement descent polynomial is nonzero for `n ≥ 2`. -/
theorem derangementDescentPolynomial_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    derangementDescentPolynomial n ≠ 0 := by
  classical
  obtain ⟨π, hπ⟩ := exists_derangement n hn
  have hpos : 0 < (derangementDescentPolynomial n).eval 1 := by
    rw [derangementDescentPolynomial_eval_one]
    exact_mod_cast Finset.card_pos.mpr ⟨π, by simp [hπ]⟩
  intro h
  simp [h] at hpos

/-- Every real root is nonpositive; existence of a full real factorization is separate. -/
theorem derangementDescentPolynomial_roots_nonpos (n : ℕ) :
    ∀ r ∈ (derangementDescentPolynomial n).roots, r ≤ 0 := by
  exact roots_nonpos_of_hasNonnegCoeffs (derangementDescentPolynomial_nonneg n)

end RealRooted.EulerianCompendium
