import RealRooted.ClassicalHurwitzMatrix.Routh.Determinant

/-!
# Iterated algebraic Routh reduction

This file packages repeated Routh steps and derives the product formula for
the leading classical Hurwitz determinants.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- One step on the pair `(odd, even)` representing
`even(X²) + X * odd(X²)`. -/
def routhPairStep (pair : ℝ[X] × ℝ[X]) : ℝ[X] × ℝ[X] :=
  (routhReducedOddPart (routhCoefficient pair.1 pair.2) pair.1 pair.2, pair.1)

/-- The pair of odd and even parts after `n` algebraic Routh steps. -/
def routhPair (odd even : ℝ[X]) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (odd, even)
  | n + 1 => routhPairStep (routhPair odd even n)

@[simp]
theorem routhPair_zero (odd even : ℝ[X]) :
    routhPair odd even 0 = (odd, even) :=
  rfl

@[simp]
theorem routhPair_succ (odd even : ℝ[X]) (n : ℕ) :
    routhPair odd even (n + 1) = routhPairStep (routhPair odd even n) :=
  rfl

/-- The polynomial represented after `n` algebraic Routh steps. -/
def routhPolynomialAt (odd even : ℝ[X]) (n : ℕ) : ℝ[X] :=
  oddEvenPolynomial (routhPair odd even n).1 (routhPair odd even n).2

@[simp]
theorem routhPolynomialAt_zero (odd even : ℝ[X]) :
    routhPolynomialAt odd even 0 = oddEvenPolynomial odd even :=
  rfl

/-- The product of the next `n` even-part constant coefficients, beginning at
Routh stage `k`. -/
def routhPivotProduct (odd even : ℝ[X]) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | k, n + 1 =>
      (routhPair odd even k).2.coeff 0 * routhPivotProduct odd even (k + 1) n

@[simp]
theorem routhPivotProduct_zero (odd even : ℝ[X]) (k : ℕ) :
    routhPivotProduct odd even k 0 = 1 :=
  rfl

@[simp]
theorem routhPivotProduct_succ (odd even : ℝ[X]) (k n : ℕ) :
    routhPivotProduct odd even k (n + 1) =
      (routhPair odd even k).2.coeff 0 *
        routhPivotProduct odd even (k + 1) n :=
  rfl

theorem routhPivotProduct_pos {odd even : ℝ[X]} {k n : ℕ}
    (hpivot : ∀ i < n, 0 < (routhPair odd even (k + i)).2.coeff 0) :
    0 < routhPivotProduct odd even k n := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      rw [routhPivotProduct_succ]
      apply mul_pos (hpivot 0 (by simp))
      apply ih
      intro i hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hpivot (i + 1) (by lia)

end

end RealRooted

namespace Matrix

open RealRooted

/-- The order-`n` leading Hurwitz determinant at Routh stage `k` is the
product of the next `n` Routh pivots. Only those `n` odd-part constant
coefficients are required to be nonzero. -/
theorem hurwitzLeadingPrincipal_routhPolynomialAt_det
    (odd even : ℝ[X]) (k n : ℕ)
    (hodd : ∀ i < n,
      (routhPair odd even (k + i)).1.coeff 0 ≠ 0) :
    (hurwitzLeadingPrincipal (routhPolynomialAt odd even k).coeff n).det =
      routhPivotProduct odd even k n := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      let pair := routhPair odd even k
      have hpair : routhPair odd even (k + 1) = routhPairStep pair := by
        simp [pair]
      have hhead : pair.1.coeff 0 ≠ 0 := by
        simpa [pair] using hodd 0 (by simp)
      have hrec := hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_ratio
        pair.1 pair.2 hhead n
      have htail :
          (hurwitzLeadingPrincipal
            (routhPolynomialAt odd even (k + 1)).coeff n).det =
            routhPivotProduct odd even (k + 1) n := by
        apply ih
        intro i hi
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hodd (i + 1) (by lia)
      rw [routhPivotProduct_succ, ← htail]
      simpa [routhPolynomialAt, pair, hpair, routhPairStep,
        routhReducedPolynomial] using hrec

/-- Positive Routh pivots make the corresponding leading Hurwitz determinant
positive. -/
theorem hurwitzLeadingPrincipal_routhPolynomialAt_det_pos
    (odd even : ℝ[X]) (k n : ℕ)
    (hodd : ∀ i < n,
      (routhPair odd even (k + i)).1.coeff 0 ≠ 0)
    (hpivot : ∀ i < n,
      0 < (routhPair odd even (k + i)).2.coeff 0) :
    0 < (hurwitzLeadingPrincipal
      (routhPolynomialAt odd even k).coeff n).det := by
  rw [hurwitzLeadingPrincipal_routhPolynomialAt_det odd even k n hodd]
  exact routhPivotProduct_pos hpivot

/-- The leading Hurwitz determinant of the original odd/even polynomial is
the product of its first `n` Routh pivots. -/
theorem hurwitzLeadingPrincipal_oddEvenPolynomial_det_eq_routhPivotProduct
    (odd even : ℝ[X]) (n : ℕ)
    (hodd : ∀ i < n, (routhPair odd even i).1.coeff 0 ≠ 0) :
    (hurwitzLeadingPrincipal (oddEvenPolynomial odd even).coeff n).det =
      routhPivotProduct odd even 0 n := by
  simpa using hurwitzLeadingPrincipal_routhPolynomialAt_det
    odd even 0 n (by simpa using hodd)

/-- Positive initial Routh pivots give positivity of the corresponding
leading Hurwitz determinant. -/
theorem hurwitzLeadingPrincipal_oddEvenPolynomial_det_pos
    (odd even : ℝ[X]) (n : ℕ)
    (hodd : ∀ i < n, (routhPair odd even i).1.coeff 0 ≠ 0)
    (hpivot : ∀ i < n, 0 < (routhPair odd even i).2.coeff 0) :
    0 < (hurwitzLeadingPrincipal
      (oddEvenPolynomial odd even).coeff n).det := by
  simpa using hurwitzLeadingPrincipal_routhPolynomialAt_det_pos
    odd even 0 n (by simpa using hodd) (by simpa using hpivot)

end Matrix
