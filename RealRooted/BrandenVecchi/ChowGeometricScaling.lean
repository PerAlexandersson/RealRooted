import RealRooted.BrandenVecchi.Chow
import RealRooted.PolyaFrequencyConvolution.GeometricScaling

/-!
# Geometric scaling of Chow rows

Geometrically scaling a lower-triangular matrix entry in position `(i,j)` by
`c ^ (i-j)` makes every rank-`n` Chow and Chow-derangement row homogeneous of
weight `n`.  The Toeplitz specialization is the existing geometric scaling of
its coefficient sequence.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

namespace LowerTriangularMatrix

variable {R : Type*} [CommRing R]

/-- Scale a lower-triangular matrix entry in position `(i,j)` by
`c ^ (i-j)`. -/
def geometricScale (c : R) (A : LowerTriangularMatrix R) :
    LowerTriangularMatrix R :=
  fun i j => c ^ (i - j) * A i j

@[simp]
theorem geometricScale_apply (c : R) (A : LowerTriangularMatrix R)
    (i j : ℕ) :
    geometricScale c A i j = c ^ (i - j) * A i j :=
  rfl

@[simp]
theorem geometricScale_one (A : LowerTriangularMatrix R) :
    geometricScale 1 A = A := by
  funext i j
  simp

theorem IsLowerTriangular.geometricScale
    {A : LowerTriangularMatrix R} (hA : IsLowerTriangular A) (c : R) :
    IsLowerTriangular (geometricScale c A) := by
  intro i j hij
  simp [hA hij]

end LowerTriangularMatrix

namespace BrandenVecchi

variable {R : Type*} [CommRing R]

/-- Chow-derangement rows are homogeneous under geometric matrix scaling. -/
theorem chowDerangement_geometricScale
    (c : R) (A : LowerTriangularMatrix R) :
    ∀ n : ℕ,
      chowDerangement (LowerTriangularMatrix.geometricScale c A) n =
        C (c ^ n) * chowDerangement A n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          let P : R[X] := ∑ k : Fin (n + 1),
            C (A (n + 1) k) * chowDerangement A k
          have hPdegree : P.natDegree ≤ n := by
            refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
              (fun k : Fin (n + 1) =>
                C (A (n + 1) k) * chowDerangement A k) ?_
            intro k _
            exact (Polynomial.natDegree_C_mul_le _ _).trans
              ((natDegree_chowDerangement_le A k).trans
                (Nat.lt_succ_iff.mp k.isLt))
          have hsum :
              (∑ k : Fin (n + 1),
                C ((LowerTriangularMatrix.geometricScale c A)
                    (n + 1) k) *
                  chowDerangement
                    (LowerTriangularMatrix.geometricScale c A) k) =
                C (c ^ (n + 1)) * P := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [ih k k.isLt]
            have hk : (k : ℕ) ≤ n + 1 := Nat.le_of_lt k.isLt
            have hpow : c ^ (n + 1 - (k : ℕ)) * c ^ (k : ℕ) =
                c ^ (n + 1) := by
              rw [← pow_add, Nat.sub_add_cancel hk]
            simp only [LowerTriangularMatrix.geometricScale_apply]
            change
              C (c ^ (n + 1 - (k : ℕ)) * A (n + 1) k) *
                  (C (c ^ (k : ℕ)) * chowDerangement A k) =
                C (c ^ (n + 1)) *
                  (C (A (n + 1) k) * chowDerangement A k)
            simp only [map_mul]
            rw [← hpow]
            simp only [map_mul]
            ring
          rw [chowDerangement_succ, chowDerangement_succ, hsum,
            Polynomial.chowS_C_mul n (c ^ (n + 1)) P hPdegree]
          ring

/-- Chow rows are homogeneous under geometric matrix scaling. -/
theorem chowPolynomial_geometricScale
    (c : R) (A : LowerTriangularMatrix R) (n : ℕ) :
    chowPolynomial (LowerTriangularMatrix.geometricScale c A) n =
      C (c ^ n) * chowPolynomial A n := by
  rw [chowPolynomial_eq, chowPolynomial_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [chowDerangement_geometricScale]
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : c ^ (n - k) * c ^ k = c ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  simp only [LowerTriangularMatrix.geometricScale_apply]
  change C (c ^ (n - k) * A n k) *
      (C (c ^ k) * chowDerangement A k) =
    C (c ^ n) * (C (A n k) * chowDerangement A k)
  simp only [map_mul]
  rw [← hpow]
  simp only [map_mul]
  ring

@[simp]
theorem chowDerangement_geometricScale_zero_rank
    (c : R) (A : LowerTriangularMatrix R) :
    chowDerangement (LowerTriangularMatrix.geometricScale c A) 0 =
      chowDerangement A 0 := by
  simp

@[simp]
theorem chowPolynomial_geometricScale_zero_rank
    (c : R) (A : LowerTriangularMatrix R) :
    chowPolynomial (LowerTriangularMatrix.geometricScale c A) 0 =
      chowPolynomial A 0 := by
  simpa using chowPolynomial_geometricScale c A 0

@[simp]
theorem chowDerangement_geometricScale_zero_succ
    (A : LowerTriangularMatrix R) (n : ℕ) :
    chowDerangement (LowerTriangularMatrix.geometricScale 0 A) (n + 1) = 0 := by
  simpa using chowDerangement_geometricScale (0 : R) A (n + 1)

@[simp]
theorem chowPolynomial_geometricScale_zero_succ
    (A : LowerTriangularMatrix R) (n : ℕ) :
    chowPolynomial (LowerTriangularMatrix.geometricScale 0 A) (n + 1) = 0 := by
  simpa using chowPolynomial_geometricScale (0 : R) A (n + 1)

end BrandenVecchi

/-- Toeplitz formation identifies geometric sequence scaling with geometric
lower-triangular matrix scaling. -/
theorem toeplitz_geometricScale (c : ℝ) (a : ℕ → ℝ) :
    toeplitz (geometricScale c a) =
      LowerTriangularMatrix.geometricScale c (toeplitz a) := by
  funext i j
  rw [toeplitz_apply]
  by_cases hji : j ≤ i
  · change (if j ≤ i then geometricScale c a (i - j) else 0) =
      c ^ (i - j) * toeplitz a i j
    simp [hji, geometricScale]
  · simp [hji, LowerTriangularMatrix.geometricScale]

/-- Toeplitz Chow rows scale by the rank under geometric scaling of their
coefficient sequence. -/
theorem BrandenVecchi.chowPolynomial_toeplitz_geometricScale
    (c : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    chowPolynomial (toeplitz (geometricScale c a)) n =
      C (c ^ n) * chowPolynomial (toeplitz a) n := by
  rw [toeplitz_geometricScale]
  exact BrandenVecchi.chowPolynomial_geometricScale c (toeplitz a) n

end

end RealRooted
