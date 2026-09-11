import RealRooted.LowerTriangularMatrix
import RealRooted.Mathlib.Algebra.Polynomial.Chow

/-!
# Chow polynomials of lower-triangular matrices

This module gives the literal commutative-ring matrix construction in Corollary 3.1
of Brändén--Vecchi, *Chow polynomials of totally nonnegative matrices and
posets* (2025), together with its finite reflection characterization under a
unit-diagonal hypothesis.  Its total-nonnegative real-rootedness consequences
are intentionally separate later layers.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

variable {R : Type*} [CommRing R]

/-- The Chow-derangement polynomial sequence associated to a lower-triangular
matrix over a commutative ring.

The successor clause is the paper's recursion
`dₙ = X * Sₙ₋₁ (∑ k < n, rₙₖ dₖ)`. -/
def chowDerangement (A : LowerTriangularMatrix R) : ℕ → R[X]
  | 0 => 1
  | n + 1 =>
      X * Polynomial.chowS n (∑ k : Fin (n + 1),
        C (A (n + 1) k) * chowDerangement A k)
  termination_by n => n
  decreasing_by exact k.isLt

/-- The Chow polynomial in row `n`, formed from the Chow-derangement sequence. -/
def chowPolynomial (A : LowerTriangularMatrix R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), C (A n k) * chowDerangement A k

@[simp]
theorem chowDerangement_zero (A : LowerTriangularMatrix R) : chowDerangement A 0 = 1 := by
  simp [chowDerangement]

/-- The defining successor recursion for the Chow-derangement sequence. -/
theorem chowDerangement_succ (A : LowerTriangularMatrix R) (n : ℕ) :
    chowDerangement A (n + 1) =
      X * Polynomial.chowS n (∑ k : Fin (n + 1),
        C (A (n + 1) k) * chowDerangement A k) := by
  simp [chowDerangement]

/-- Chow-derangement polynomial `dₙ` has degree at most `n`, including the
zero-polynomial cases. -/
theorem natDegree_chowDerangement_le (A : LowerTriangularMatrix R) :
    ∀ n, (chowDerangement A n).natDegree ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [chowDerangement_succ]
      have hsdegree :
          (chowS n (∑ k : Fin (n + 1),
            C (A (n + 1) k) * chowDerangement A k)).natDegree ≤ n := by
        let P : R[X] := ∑ k : Fin (n + 1), C (A (n + 1) k) * chowDerangement A k
        have hPdegree : P.natDegree ≤ n := by
          refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
            (fun k : Fin (n + 1) => C (A (n + 1) k) * chowDerangement A k) ?_
          intro k _
          refine (natDegree_C_mul_le _ _).trans ?_
          exact (ih k k.isLt).trans (Nat.lt_succ_iff.mp k.isLt)
        exact natDegree_chowS_le n P hPdegree
      calc
          (X * chowS n (∑ k : Fin (n + 1),
          C (A (n + 1) k) * chowDerangement A k)).natDegree ≤
            X.natDegree + (chowS n (∑ k : Fin (n + 1),
              C (A (n + 1) k) * chowDerangement A k)).natDegree := natDegree_mul_le
        _ ≤ 1 + n := Nat.add_le_add natDegree_X_le hsdegree
        _ = n + 1 := by ring

private theorem natDegree_chowDerangement_input_le (A : LowerTriangularMatrix R) (n : ℕ) :
    (∑ k : Fin (n + 1), C (A (n + 1) k) * chowDerangement A k).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun k : Fin (n + 1) => C (A (n + 1) k) * chowDerangement A k) ?_
  intro k _
  refine (natDegree_C_mul_le _ _).trans ?_
  exact (natDegree_chowDerangement_le A k).trans (Nat.lt_succ_iff.mp k.isLt)

/-- The Chow-derangement polynomial `dₙ` is fixed by reflection at its
natural bound. -/
theorem reflect_chowDerangement (A : LowerTriangularMatrix R) :
    ∀ n, (chowDerangement A n).reflect n = chowDerangement A n := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    let P : R[X] := ∑ k : Fin (n + 1), C (A (n + 1) k) * chowDerangement A k
    have hPdegree : P.natDegree ≤ n := natDegree_chowDerangement_input_le A n
    rw [chowDerangement_succ]
    change (X * chowS n P).reflect (n + 1) = X * chowS n P
    rw [show n + 1 = 1 + n by lia,
      reflect_mul _ _ (by exact natDegree_X_le) (natDegree_chowS_le n P hPdegree)]
    simp [reflect_chowS n P hPdegree]

/-- Under the unit-diagonal condition, the positive-index Chow polynomial
`Hₙ` has the Corollary 3.1 reflection relation `Iₙ(Hₙ) = X * Hₙ`. -/
theorem reflect_chowPolynomial_succ (A : LowerTriangularMatrix R)
    (hdiag : ∀ n, A n n = 1) (n : ℕ) :
    (chowPolynomial A (n + 1)).reflect (n + 1) = X * chowPolynomial A (n + 1) := by
  let P : R[X] := ∑ k : Fin (n + 1), C (A (n + 1) k) * chowDerangement A k
  let S : R[X] := chowS n P
  have hPdegree : P.natDegree ≤ n := natDegree_chowDerangement_input_le A n
  have hH : chowPolynomial A (n + 1) = P + chowDerangement A (n + 1) := by
    change (∑ k ∈ Finset.range (n + 2),
      C (A (n + 1) k) * chowDerangement A k) = P + chowDerangement A (n + 1)
    rw [show n + 2 = (n + 1) + 1 by lia, Finset.sum_range_succ]
    have hsum :
        (∑ k ∈ Finset.range (n + 1), C (A (n + 1) k) * chowDerangement A k) = P := by
      exact (Fin.sum_univ_eq_sum_range (fun k =>
        C (A (n + 1) k) * chowDerangement A k) (n + 1)).symm
    rw [hsum]
    simp [hdiag]
  have hd : chowDerangement A (n + 1) = X * S := by
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
      (reflect_mul P (1 : R[X]) (F := n) (G := 1) hPdegree (by simp))
  rw [hH, reflect_add, reflect_chowDerangement A]
  rw [hPshift, hreflectP, hd]
  ring

/-- The reflection relation for the Chow polynomial of a lower unitriangular
matrix. -/
theorem reflect_chowPolynomial_succ_of_isLowerUnitriangular
    (A : LowerTriangularMatrix R) (hA : LowerTriangularMatrix.IsLowerUnitriangular A)
    (n : ℕ) :
    (chowPolynomial A (n + 1)).reflect (n + 1) = X * chowPolynomial A (n + 1) :=
  reflect_chowPolynomial_succ A hA.diagonal n

private theorem chowDerangement_succ_eq_of_reflection_data
    (A : LowerTriangularMatrix R) (hdiag : ∀ n, A n n = 1)
    (d H : ℕ → R[X]) (n : ℕ)
    (hdreflect : ∀ n, (d n).reflect n = d n)
    (hHreflect : ∀ n, (H (n + 1)).reflect (n + 1) = X * H (n + 1))
    (hrow : ∀ n, H n = ∑ k ∈ Finset.range (n + 1), C (A n k) * d k)
    (hdegree : ∀ n, (d n).natDegree ≤ n) :
    d (n + 1) = X * chowS n (∑ k : Fin (n + 1), C (A (n + 1) k) * d k) := by
  let P : R[X] := ∑ k : Fin (n + 1), C (A (n + 1) k) * d k
  let S : R[X] := chowS n P
  have hPdegree : P.natDegree ≤ n := by
    refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun k : Fin (n + 1) => C (A (n + 1) k) * d k) ?_
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    exact (hdegree k).trans (Nat.lt_succ_iff.mp k.isLt)
  have hH : H (n + 1) = P + d (n + 1) := by
    rw [hrow, Finset.sum_range_succ]
    have hsum :
        (∑ k ∈ Finset.range (n + 1), C (A (n + 1) k) * d k) = P := by
      exact (Fin.sum_univ_eq_sum_range (fun k => C (A (n + 1) k) * d k) (n + 1)).symm
    rw [hsum]
    simp [hdiag]
  have hPshift : P.reflect (n + 1) = P.reflect n * X := by
    simpa [Nat.add_comm] using
      (reflect_mul P (1 : R[X]) (F := n) (G := 1) hPdegree (by simp))
  have hreflection := hHreflect n
  rw [hH, reflect_add, hPshift, hdreflect] at hreflection
  have hS : (X - 1) * S = P.reflect n - P := X_sub_one_mul_chowS n P hPdegree
  have hmul : (X - 1) * d (n + 1) = X * ((X - 1) * S) := by
    calc
      (X - 1) * d (n + 1) = X * (P.reflect n - P) := by
        linear_combination -hreflection
      _ = X * ((X - 1) * S) := by rw [hS]
  apply (monic_X_sub_C (1 : R)).isRegular.left
  calc
    (X - 1) * d (n + 1) = X * ((X - 1) * S) := hmul
    _ = (X - 1) * (X * S) := by ring

/-- The defining row expansion for the Chow polynomial. -/
theorem chowPolynomial_eq (A : LowerTriangularMatrix R) (n : ℕ) :
    chowPolynomial A n = ∑ k ∈ Finset.range (n + 1), C (A n k) * chowDerangement A k :=
  rfl

/-- The bounded reflection data in Corollary 3.1 uniquely determine the
Chow-derangement and Chow-polynomial sequences of a unit-diagonal matrix. -/
theorem chowDerangement_chowPolynomial_unique (A : LowerTriangularMatrix R)
    (hdiag : ∀ n, A n n = 1) (d H : ℕ → R[X])
    (hdzero : d 0 = 1)
    (hdreflect : ∀ n, (d n).reflect n = d n)
    (hHreflect : ∀ n, (H (n + 1)).reflect (n + 1) = X * H (n + 1))
    (hrow : ∀ n, H n = ∑ k ∈ Finset.range (n + 1), C (A n k) * d k)
    (hdegree : ∀ n, (d n).natDegree ≤ n) :
    d = chowDerangement A ∧ H = chowPolynomial A := by
  have hd : ∀ n, d n = chowDerangement A n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa using hdzero
      | succ n =>
        rw [chowDerangement_succ_eq_of_reflection_data A hdiag d H n hdreflect hHreflect hrow
          hdegree, chowDerangement_succ]
        apply congrArg (fun P : R[X] => X * chowS n P)
        apply Finset.sum_congr rfl
        intro k _
        rw [ih k k.isLt]
  constructor
  · exact funext hd
  · funext n
    rw [hrow, chowPolynomial_eq]
    apply Finset.sum_congr rfl
    intro k _
    rw [hd]

/-- A unit entry at the initial diagonal position gives the expected initial
Chow polynomial. -/
theorem chowPolynomial_zero (A : LowerTriangularMatrix R) (hdiag : A 0 0 = 1) :
    chowPolynomial A 0 = 1 := by
  rw [chowPolynomial_eq]
  simp [hdiag]

end

end RealRooted.BrandenVecchi
