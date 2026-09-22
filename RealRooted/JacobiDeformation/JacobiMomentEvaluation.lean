import RealRooted.JacobiDeformation.JacobiMomentCompletion
import RealRooted.JacobiDeformation.JacobiMomentSum

/-!
# Evaluation of normalized Jacobi moments

The preceding leaf reduces the functional to a finite sum.  This module uses
the released terminating Chu--Vandermonde identity to evaluate that sum.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem finiteVandermonde_rising_eq_risingFactorial (x : ℝ) (n : ℕ) :
    FiniteVandermonde.rising x n = risingFactorial x n := by
  induction n with
  | zero => simp [FiniteVandermonde.rising, risingFactorial]
  | succ n ih =>
      rw [FiniteVandermonde.rising_succ, ih]
      unfold risingFactorial
      rw [ascPochhammer_succ_eval]

private theorem finiteVandermonde_falling_eq_fallingFactorial (x : ℝ) (n : ℕ) :
    FiniteVandermonde.falling x n = fallingFactorial x n := by
  induction n with
  | zero => simp [FiniteVandermonde.falling, fallingFactorial]
  | succ n ih =>
      rw [FiniteVandermonde.falling_succ, ih]
      unfold fallingFactorial
      rw [descPochhammer_succ_eval]

/-- The all-degree normalized shifted-Jacobi moment.  The terminating
Chu--Vandermonde identity includes the `j > k` vanishing case. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j k : ℕ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) =
      fallingFactorial (k : ℝ) j * risingFactorial d k /
        risingFactorial (c + d) (k + j) := by
  have hs : 0 < c + d := by linarith
  have hsum := normalizedJacobiMoment_vandermonde_sum j k (c + d) hs
  simp_rw [finiteVandermonde_rising_eq_risingFactorial,
    finiteVandermonde_falling_eq_fallingFactorial] at hsum
  have hnum : (j : ℝ) + (c + d) - 1 = (j : ℝ) + c + d - 1 := by ring
  rw [hnum] at hsum
  rw [normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_sum
    hc hd j k, hsum]
  have hsk : 0 < risingFactorial (c + d) k := risingFactorial_pos k hs
  have hskj : 0 < risingFactorial (c + d + k) j := by
    apply risingFactorial_pos
    positivity
  have htotal : 0 < risingFactorial (c + d) (k + j) :=
    risingFactorial_pos (k + j) hs
  have hsplit := risingFactorial_mul_shift (c + d) k j
  field_simp [hsk.ne', hskj.ne', htotal.ne']
  rw [← hsplit]
  ring

end RealRooted.JacobiDeformation
