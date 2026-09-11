import RealRooted.BrandenLeite.ChainPolynomial.Algebra
import RealRooted.BrandenLeite.Resolvable

/-!
# Resolution algebra for chain polynomials

This module bridges generic resolvability data to the chain-polynomial
subdivision operator.  The interlacing induction is deliberately separate.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.BrandenLeite

/-- The subdivision recursion written in terms of one resolving row. -/
theorem chainPolynomial_succ_eq_resolution_sum
    {S : Type*} [CommRing S] [LE S]
    {R : LowerTriangularMatrix S} (resolution : Resolution R) (n : ℕ) :
    chainPolynomial R (n + 1) =
      X * ∑ j ∈ Finset.range (n + 1),
        C (resolution.lambda n j) *
          subdivisionOperator R (resolution.polynomial n j) := by
  have hrow :
      LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1) =
        ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) * resolution.polynomial n j := by
    rw [resolution.rowPolynomial_eq_pow_add_sum]
    ring
  calc
    chainPolynomial R (n + 1) = subdivisionOperator R (X ^ (n + 1)) := by simp
    _ = X * subdivisionOperator R
          (LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1)) :=
      subdivisionOperator_X_pow_succ_eq resolution.lowerUnitriangular n
    _ = X * subdivisionOperator R
          (∑ j ∈ Finset.range (n + 1),
            C (resolution.lambda n j) * resolution.polynomial n j) := by rw [hrow]
    _ = X * ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) := by
      rw [map_sum]
      apply congrArg (X * ·)
      apply Finset.sum_congr rfl
      intro j hj
      exact subdivisionOperator_C_mul R _ _

/-- The exact generated-family bridge used in the chain-polynomial induction. -/
theorem subdivisionOperator_resolution_recurrence
    {S : Type*} [CommRing S] [LE S]
    {R : LowerTriangularMatrix S} (resolution : Resolution R)
    {n k : ℕ} (hk : k ≤ n + 1) :
    subdivisionOperator R (resolution.polynomial (n + 1) k) =
      X * ∑ j ∈ Finset.range k,
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) +
        (1 + X) * ∑ j ∈ Finset.Ico k (n + 1),
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) := by
  let term : ℕ → S[X] := fun j =>
    C (resolution.lambda n j) * subdivisionOperator R (resolution.polynomial n j)
  have hmap :
      subdivisionOperator R (resolution.polynomial (n + 1) k) =
        chainPolynomial R (n + 1) + ∑ j ∈ Finset.Ico k (n + 1), term j := by
    rw [resolution.polynomial_eq_pow_add_sum hk, map_add, subdivisionOperator_X_pow,
      map_sum]
    apply congrArg (chainPolynomial R (n + 1) + ·)
    apply Finset.sum_congr rfl
    intro j hj
    exact subdivisionOperator_C_mul R _ _
  rw [hmap, chainPolynomial_succ_eq_resolution_sum resolution]
  have hsplit :
      (∑ j ∈ Finset.range (n + 1), term j) =
        (∑ j ∈ Finset.range k, term j) +
          ∑ j ∈ Finset.Ico k (n + 1), term j :=
    (Finset.sum_range_add_sum_Ico term hk).symm
  rw [hsplit]
  dsimp only [term]
  ring

end RealRooted.BrandenLeite
