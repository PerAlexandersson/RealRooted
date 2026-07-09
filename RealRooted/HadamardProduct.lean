import RealRooted.MultiplierSequence

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Coefficientwise Hadamard products

This file contains the small algebraic API for the coefficientwise Hadamard
product.  It is kept below the theorem-heavy `RealRooted.Hadamard` module so
other proof modules can use the product without creating import cycles.
-/

/-- Coefficientwise Hadamard product of two real polynomials. -/
def hadamardProduct (p q : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => monomial n (a * q.coeff n)

@[simp] theorem coeff_hadamardProduct (p q : ℝ[X]) (n : ℕ) :
    (hadamardProduct p q).coeff n = p.coeff n * q.coeff n := by
  classical
  rw [hadamardProduct, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hbn
    simp [hbn]
  · intro hn
    rw [(Polynomial.notMem_support_iff).mp hn]
    simp

theorem hadamardProduct_comm (p q : ℝ[X]) :
    hadamardProduct p q = hadamardProduct q p := by
  ext n
  simp [mul_comm]

/-- A Hadamard product is a diagonal operator whose diagonal is given by the
right factor's coefficients. -/
theorem hadamardProduct_eq_diagonalOperator (p q : ℝ[X]) :
    hadamardProduct p q = diagonalOperator (fun n => q.coeff n) p := by
  ext n
  rw [coeff_hadamardProduct, coeff_diagonalOperator, mul_comm]

theorem hadamardProduct_assoc (p q r : ℝ[X]) :
    hadamardProduct (hadamardProduct p q) r =
      hadamardProduct p (hadamardProduct q r) := by
  ext n
  simp [mul_assoc]

@[simp] theorem hadamardProduct_zero_left (p : ℝ[X]) :
    hadamardProduct 0 p = 0 := by
  ext n
  simp

@[simp] theorem hadamardProduct_zero_right (p : ℝ[X]) :
    hadamardProduct p 0 = 0 := by
  ext n
  simp

theorem hadamardProduct_add_left (p q r : ℝ[X]) :
    hadamardProduct (p + q) r =
      hadamardProduct p r + hadamardProduct q r := by
  simpa [hadamardProduct_eq_diagonalOperator] using
    diagonalOperator_add (fun k => r.coeff k) p q

theorem hadamardProduct_add_right (p q r : ℝ[X]) :
    hadamardProduct p (q + r) =
      hadamardProduct p q + hadamardProduct p r := by
  ext n
  simp [mul_add]

theorem hadamardProduct_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct (C a * p) q = C a * hadamardProduct p q := by
  simpa [hadamardProduct_eq_diagonalOperator] using
    diagonalOperator_C_mul (fun k => q.coeff k) a p

theorem hadamardProduct_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct p (C a * q) =
      C a * hadamardProduct p q := by
  ext n
  simp [mul_comm, mul_left_comm]

end RealRooted
