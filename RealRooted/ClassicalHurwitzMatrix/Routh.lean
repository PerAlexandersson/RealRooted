import RealRooted.ClassicalHurwitzMatrix

/-!
# The algebraic Routh reduction

This file formalizes the polynomial and row-operation algebra in one step of
Holtz's Routh reduction. It deliberately makes no root-location claim.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The scalar eliminated in one Routh step. In the project's odd/even
argument order, this is `even(0) / odd(0)`. -/
def routhCoefficient (odd even : ℝ[X]) : ℝ :=
  even.coeff 0 / odd.coeff 0

theorem routhCoefficient_mul_coeff_zero (odd even : ℝ[X])
    (hodd : odd.coeff 0 ≠ 0) :
    even.coeff 0 = routhCoefficient odd even * odd.coeff 0 := by
  simp [routhCoefficient, hodd]

theorem routhCoefficient_pos {odd even : ℝ[X]}
    (hodd : 0 < odd.coeff 0) (heven : 0 < even.coeff 0) :
    0 < routhCoefficient odd even :=
  div_pos heven hodd

/-- The new odd part in the Routh reduction of
`even(X²) + X * odd(X²)`. -/
def routhReducedOddPart (c : ℝ) (odd even : ℝ[X]) : ℝ[X] :=
  (even - C c * odd).divX

@[simp]
theorem coeff_routhReducedOddPart (c : ℝ) (odd even : ℝ[X]) (n : ℕ) :
    (routhReducedOddPart c odd even).coeff n =
      even.coeff (n + 1) - c * odd.coeff (n + 1) := by
  simp [routhReducedOddPart, Polynomial.coeff_divX]

/-- Constant-term cancellation makes the defining numerator exactly divisible
by `X`. -/
theorem even_eq_C_mul_odd_add_X_mul_routhReducedOddPart
    (c : ℝ) (odd even : ℝ[X])
    (h0 : even.coeff 0 = c * odd.coeff 0) :
    even = C c * odd + X * routhReducedOddPart c odd even := by
  have hcoeff : (even - C c * odd).coeff 0 = 0 := by
    simp [h0]
  have hdiv := Polynomial.X_mul_divX_add (even - C c * odd)
  simp only [hcoeff, C_0, add_zero] at hdiv
  rw [routhReducedOddPart, hdiv]
  ring

theorem even_eq_C_mul_odd_add_X_mul_routhReducedOddPart_ratio
    (odd even : ℝ[X]) (hodd : odd.coeff 0 ≠ 0) :
    even = C (routhCoefficient odd even) * odd +
      X * routhReducedOddPart (routhCoefficient odd even) odd even :=
  even_eq_C_mul_odd_add_X_mul_routhReducedOddPart _ _ _
    (routhCoefficient_mul_coeff_zero odd even hodd)

/-- The polynomial after one algebraic Routh step. The old odd part becomes
the new even part. -/
def routhReducedPolynomial (c : ℝ) (odd even : ℝ[X]) : ℝ[X] :=
  oddEvenPolynomial (routhReducedOddPart c odd even) odd

/-- One Routh reduction reconstructs the original odd/even polynomial by an
explicit linear identity. -/
theorem oddEvenPolynomial_eq_X_mul_routhReducedPolynomial_add
    (c : ℝ) (odd even : ℝ[X])
    (h0 : even.coeff 0 = c * odd.coeff 0) :
    oddEvenPolynomial odd even =
      X * routhReducedPolynomial c odd even +
        C c * odd.comp (X ^ 2) := by
  let red := routhReducedOddPart c odd even
  have heven : even = C c * odd + X * red :=
    even_eq_C_mul_odd_add_X_mul_routhReducedOddPart c odd even h0
  calc
    oddEvenPolynomial odd even =
        oddEvenPolynomial odd (C c * odd + X * red) := by rw [heven]
    _ = X * oddEvenPolynomial red odd + C c * odd.comp (X ^ 2) := by
      simp only [oddEvenPolynomial, add_comp, mul_comp, C_comp, X_comp]
      ring
    _ = X * routhReducedPolynomial c odd even +
        C c * odd.comp (X ^ 2) := by
      rfl

end

end RealRooted

namespace Matrix

/-- The row-finite action of Holtz's `J(c)` on an infinite matrix. Even rows
add `c` times the current row to its successor; odd rows select their
successor. -/
def routhExpand {R : Type*} [Ring R] (c : R) (M : Matrix ℕ ℕ R) :
    Matrix ℕ ℕ R := fun i j =>
  if i % 2 = 0 then c * M i j + M (i + 1) j else M (i + 1) j

@[simp]
theorem routhExpand_even_apply {R : Type*} [Ring R]
    (c : R) (M : Matrix ℕ ℕ R) (i j : ℕ) :
    routhExpand c M (2 * i) j = c * M (2 * i) j + M (2 * i + 1) j := by
  simp [routhExpand]

@[simp]
theorem routhExpand_odd_apply {R : Type*} [Ring R]
    (c : R) (M : Matrix ℕ ℕ R) (i j : ℕ) :
    routhExpand c M (2 * i + 1) j = M (2 * i + 2) j := by
  simp [routhExpand]

open RealRooted

/-- The row-finite `J(c)` expansion reconstructs the original classical
Hurwitz matrix from its algebraically reduced polynomial. -/
theorem hurwitz_oddEvenPolynomial_eq_routhExpand
    (c : ℝ) (odd even : ℝ[X])
    (h0 : even.coeff 0 = c * odd.coeff 0) :
    hurwitz (oddEvenPolynomial odd even).coeff =
      routhExpand c (hurwitz (routhReducedPolynomial c odd even).coeff) := by
  ext i j
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show k + k = 2 * k by ring]
    simp only [routhExpand_even_apply, hurwitz_oddEvenPolynomial_even_row,
      hurwitz_oddEvenPolynomial_odd_row, routhReducedPolynomial]
    by_cases hkj : k < j
    · rw [if_pos hkj, if_pos (by lia), if_pos (by lia)]
      rw [coeff_routhReducedOddPart]
      have hindex : j - (k + 1) + 1 = j - k := by lia
      rw [hindex]
      ring
    · by_cases hEq : k = j
      · subst j
        simp [h0]
      · have hjk : j < k := by lia
        simp [show ¬k ≤ j by lia, hkj]
  · simp only [routhExpand_odd_apply, hurwitz_oddEvenPolynomial_odd_row,
      routhReducedPolynomial]
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]
    rw [hurwitz_oddEvenPolynomial_even_row]
    split_ifs with h₁ h₂
    · rfl
    · exfalso
      lia
    · exfalso
      lia
    · rfl

/-- Ratio-specialized form of the algebraic Hurwitz factorization. -/
theorem hurwitz_oddEvenPolynomial_eq_routhExpand_ratio
    (odd even : ℝ[X]) (hodd : odd.coeff 0 ≠ 0) :
    hurwitz (oddEvenPolynomial odd even).coeff =
      routhExpand (routhCoefficient odd even)
        (hurwitz
          (routhReducedPolynomial (routhCoefficient odd even) odd even).coeff) :=
  hurwitz_oddEvenPolynomial_eq_routhExpand _ _ _
    (routhCoefficient_mul_coeff_zero odd even hodd)

end Matrix
