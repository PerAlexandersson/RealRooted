import RealRooted.LowerTriangularMatrix
import RealRooted.Mathlib.Algebra.Polynomial.Chow

/-!
# Chow polynomials of lower-triangular matrices

This module gives the literal recursive matrix construction in Corollary 3.1
of Brändén--Vecchi, *Chow polynomials of totally nonnegative matrices and
posets* (2025), together with its finite reflection characterization under a
unit-diagonal hypothesis.  Its total-nonnegative real-rootedness consequences
are intentionally separate later layers.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The Chow-derangement polynomial sequence associated to a real
lower-triangular matrix.

The successor clause is the paper's recursion
`dₙ = X * Sₙ₋₁ (∑ k < n, rₙₖ dₖ)`. -/
def chowDerangement (R : LowerTriangularMatrix ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X * Polynomial.chowS n (∑ k : Fin (n + 1),
        C (R (n + 1) k) * chowDerangement R k)
  termination_by n => n
  decreasing_by exact k.isLt

/-- The Chow polynomial in row `n`, formed from the Chow-derangement sequence. -/
def chowPolynomial (R : LowerTriangularMatrix ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (R n k) * chowDerangement R k

@[simp]
theorem chowDerangement_zero (R : LowerTriangularMatrix ℝ) : chowDerangement R 0 = 1 := by
  simp [chowDerangement]

/-- The defining successor recursion for the Chow-derangement sequence. -/
theorem chowDerangement_succ (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    chowDerangement R (n + 1) =
      X * Polynomial.chowS n (∑ k : Fin (n + 1),
        C (R (n + 1) k) * chowDerangement R k) := by
  simp [chowDerangement]

/-- Chow-derangement polynomial `dₙ` has degree at most `n`, including the
zero-polynomial cases. -/
theorem natDegree_chowDerangement_le (R : LowerTriangularMatrix ℝ) :
    ∀ n, (chowDerangement R n).natDegree ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [chowDerangement_succ]
      have hsdegree :
          (chowS n (∑ k : Fin (n + 1),
            C (R (n + 1) k) * chowDerangement R k)).natDegree ≤ n := by
        let P : ℝ[X] := ∑ k : Fin (n + 1), C (R (n + 1) k) * chowDerangement R k
        have hPdegree : P.natDegree ≤ n := by
          refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
            (fun k : Fin (n + 1) => C (R (n + 1) k) * chowDerangement R k) ?_
          intro k _
          refine (natDegree_C_mul_le _ _).trans ?_
          exact (ih k k.isLt).trans (Nat.lt_succ_iff.mp k.isLt)
        exact natDegree_chowS_le n P hPdegree
      calc
        (X * chowS n (∑ k : Fin (n + 1),
          C (R (n + 1) k) * chowDerangement R k)).natDegree ≤
            X.natDegree + (chowS n (∑ k : Fin (n + 1),
              C (R (n + 1) k) * chowDerangement R k)).natDegree := natDegree_mul_le
        _ ≤ 1 + n := Nat.add_le_add natDegree_X_le hsdegree
        _ = n + 1 := by ring

private theorem natDegree_chowDerangement_input_le (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    (∑ k : Fin (n + 1), C (R (n + 1) k) * chowDerangement R k).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun k : Fin (n + 1) => C (R (n + 1) k) * chowDerangement R k) ?_
  intro k _
  refine (natDegree_C_mul_le _ _).trans ?_
  exact (natDegree_chowDerangement_le R k).trans (Nat.lt_succ_iff.mp k.isLt)

/-- The Chow-derangement polynomial `dₙ` is fixed by reflection at its
natural bound. -/
theorem reflect_chowDerangement (R : LowerTriangularMatrix ℝ) :
    ∀ n, (chowDerangement R n).reflect n = chowDerangement R n := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    let P : ℝ[X] := ∑ k : Fin (n + 1), C (R (n + 1) k) * chowDerangement R k
    have hPdegree : P.natDegree ≤ n := natDegree_chowDerangement_input_le R n
    rw [chowDerangement_succ]
    change (X * chowS n P).reflect (n + 1) = X * chowS n P
    rw [show n + 1 = 1 + n by lia,
      reflect_mul _ _ (by exact natDegree_X_le) (natDegree_chowS_le n P hPdegree)]
    simp [reflect_chowS n P hPdegree]

/-- Under the unit-diagonal condition, the positive-index Chow polynomial
`Hₙ` has the Corollary 3.1 reflection relation `Iₙ(Hₙ) = X * Hₙ`. -/
theorem reflect_chowPolynomial_succ (R : LowerTriangularMatrix ℝ)
    (hdiag : ∀ n, R n n = 1) (n : ℕ) :
    (chowPolynomial R (n + 1)).reflect (n + 1) = X * chowPolynomial R (n + 1) := by
  let P : ℝ[X] := ∑ k : Fin (n + 1), C (R (n + 1) k) * chowDerangement R k
  let S : ℝ[X] := chowS n P
  have hPdegree : P.natDegree ≤ n := natDegree_chowDerangement_input_le R n
  have hH : chowPolynomial R (n + 1) = P + chowDerangement R (n + 1) := by
    change (∑ k ∈ Finset.range (n + 2),
      C (R (n + 1) k) * chowDerangement R k) = P + chowDerangement R (n + 1)
    rw [show n + 2 = (n + 1) + 1 by lia, Finset.sum_range_succ]
    have hsum :
        (∑ k ∈ Finset.range (n + 1), C (R (n + 1) k) * chowDerangement R k) = P := by
      exact (Fin.sum_univ_eq_sum_range (fun k =>
        C (R (n + 1) k) * chowDerangement R k) (n + 1)).symm
    rw [hsum]
    simp [hdiag]
  have hd : chowDerangement R (n + 1) = X * S := by
    rw [chowDerangement_succ]
  have hS : (X - 1) * S = P.reflect n - P := by
    exact X_sub_one_mul_chowS n P hPdegree
  have hreflectP : P.reflect n = P + (X - 1) * S := by
    calc
      P.reflect n = (P.reflect n - P) + P := by ring
      _ = (X - 1) * S + P := by rw [← hS]
      _ = P + (X - 1) * S := by ring
  have hPshift : P.reflect (n + 1) = P.reflect n * X := by
    simpa [Nat.add_comm] using
      (reflect_mul P (1 : ℝ[X]) (F := n) (G := 1) hPdegree (by simp))
  rw [hH, reflect_add, reflect_chowDerangement R]
  rw [hPshift, hreflectP, hd]
  ring

/-- The defining row expansion for the Chow polynomial. -/
theorem chowPolynomial_eq (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    chowPolynomial R n = ∑ k ∈ Finset.range (n + 1), C (R n k) * chowDerangement R k :=
  rfl

/-- A unit entry at the initial diagonal position gives the expected initial
Chow polynomial. -/
theorem chowPolynomial_zero (R : LowerTriangularMatrix ℝ) (hdiag : R 0 0 = 1) :
    chowPolynomial R 0 = 1 := by
  rw [chowPolynomial_eq]
  simp [hdiag]

end

end RealRooted.BrandenVecchi
