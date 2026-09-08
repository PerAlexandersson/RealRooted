import RealRooted.ClassicalHurwitzMatrix.Routh.Sequence
import RealRooted.ClassicalHurwitzMatrix.Routh.TotallyNonnegative
import RealRooted.ClassicalHurwitzMatrix.TotallyNonnegative

/-!
# Total nonnegativity from a finite Routh sequence

This file iterates the one-step total-nonnegativity implication backward along
an algebraic Routh sequence.
-/

open Polynomial

namespace Matrix

open RealRooted

/-- Total nonnegativity at the end of a finite Routh sequence propagates back
to its initial stage when every intervening division is valid and every Routh
coefficient is nonnegative. -/
theorem IsTotallyNonneg.hurwitz_routhPolynomialAt_of_chain
    (odd even : ℝ[X]) (k n : ℕ)
    (hfinal :
      (hurwitz (routhPolynomialAt odd even (k + n)).coeff).IsTotallyNonneg)
    (hodd : ∀ i < n,
      (routhPair odd even (k + i)).1.coeff 0 ≠ 0)
    (hcoeff : ∀ i < n, 0 ≤ routhCoefficient
      (routhPair odd even (k + i)).1
      (routhPair odd even (k + i)).2) :
    (hurwitz (routhPolynomialAt odd even k).coeff).IsTotallyNonneg := by
  induction n generalizing k with
  | zero => simpa using hfinal
  | succ n ih =>
      let pair := routhPair odd even k
      have hpair : routhPair odd even (k + 1) = routhPairStep pair := by
        simp [pair]
      have htail :
          (hurwitz (routhPolynomialAt odd even (k + 1)).coeff).IsTotallyNonneg := by
        apply ih
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal
        · intro i hi
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hodd (i + 1) (by lia)
        · intro i hi
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hcoeff (i + 1) (by lia)
      have hstep := htail.hurwitz_oddEvenPolynomial_of_routhReduced_ratio
        (hcoeff 0 (by simp)) (hodd 0 (by simp))
      simpa [routhPolynomialAt, pair, hpair, routhPairStep,
        routhReducedPolynomial] using hstep

/-- A finite Routh sequence ending in a nonnegative constant polynomial has a
totally nonnegative classical Hurwitz matrix at its initial stage. -/
theorem hurwitz_routhPolynomialAt_isTotallyNonneg_of_eq_C
    (odd even : ℝ[X]) (k n : ℕ) (a : ℝ)
    (hfinal : routhPolynomialAt odd even (k + n) = C a) (ha : 0 ≤ a)
    (hodd : ∀ i < n,
      (routhPair odd even (k + i)).1.coeff 0 ≠ 0)
    (hcoeff : ∀ i < n, 0 ≤ routhCoefficient
      (routhPair odd even (k + i)).1
      (routhPair odd even (k + i)).2) :
    (hurwitz (routhPolynomialAt odd even k).coeff).IsTotallyNonneg := by
  apply IsTotallyNonneg.hurwitz_routhPolynomialAt_of_chain odd even k n
  · rw [hfinal]
    exact hurwitz_C_isTotallyNonneg a ha
  · exact hodd
  · exact hcoeff

/-- Initial-stage specialization of the constant-terminal Routh criterion. -/
theorem hurwitz_oddEvenPolynomial_isTotallyNonneg_of_routh_eq_C
    (odd even : ℝ[X]) (n : ℕ) (a : ℝ)
    (hfinal : routhPolynomialAt odd even n = C a) (ha : 0 ≤ a)
    (hodd : ∀ i < n, (routhPair odd even i).1.coeff 0 ≠ 0)
    (hcoeff : ∀ i < n, 0 ≤ routhCoefficient
      (routhPair odd even i).1 (routhPair odd even i).2) :
    (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg := by
  simpa using hurwitz_routhPolynomialAt_isTotallyNonneg_of_eq_C
    odd even 0 n a (by simpa using hfinal) (by simpa using ha)
      (by simpa using hodd) (by simpa using hcoeff)

end Matrix
