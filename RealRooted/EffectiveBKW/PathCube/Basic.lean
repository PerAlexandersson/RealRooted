module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import RealRooted.Basic.Coefficients
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path-cube transfer polynomials

The state starts at the first basis vector. Its first coordinate is the path-cube
transfer polynomial. The recursive definition exposes the four small polynomial
updates, and `state_eq_pow_mulVec` identifies it with the matrix-power definition.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

open Polynomial Matrix

/-- The path-cube transfer matrix, with the polynomial variable as its parameter. -/
noncomputable def transfer : Matrix (Fin 4) (Fin 4) ℝ[X] :=
  !![1 + X, 2 * X, 0, 0;
     1, X, 2 + X, 3 * X;
     1, X, 0, 0;
     0, 0, 1, X]

/-- One transfer step, written without a finite matrix sum. -/
noncomputable def step (v : Fin 4 → ℝ[X]) : Fin 4 → ℝ[X] :=
  ![(1 + X) * v 0 + 2 * X * v 1,
    v 0 + X * v 1 + (2 + X) * v 2 + 3 * X * v 3,
    v 0 + X * v 1,
    v 2 + X * v 3]

/-- The four transfer coordinates after `r` steps. -/
noncomputable def state : ℕ → Fin 4 → ℝ[X]
  | 0 => ![1, 0, 0, 0]
  | r + 1 => step (state r)

/-- The first coordinate of the path-cube transfer orbit. -/
noncomputable def row (r : ℕ) : ℝ[X] := state r 0

/-- The explicit update is multiplication by the transfer matrix. -/
theorem step_eq_mulVec (v : Fin 4 → ℝ[X]) : step v = transfer *ᵥ v := by
  ext i
  fin_cases i <;> simp [step, transfer, mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

/-- The recursive state is the orbit of the first basis vector under matrix powers. -/
theorem state_eq_pow_mulVec (r : ℕ) : state r = transfer ^ r *ᵥ ![1, 0, 0, 0] := by
  induction r with
  | zero => simp [state]
  | succ r ih => rw [state, step_eq_mulVec, ih, pow_succ', mulVec_mulVec]

/-- In particular, the row is the first coordinate of the specified matrix orbit. -/
theorem row_eq_pow_mulVec (r : ℕ) :
    row r = (transfer ^ r *ᵥ ![1, 0, 0, 0]) 0 := by
  rw [row, state_eq_pow_mulVec]

/-- The zeroth row is the constant one polynomial. -/
@[simp] theorem row_zero : row 0 = 1 := rfl

/-- The first row is `1 + X`. -/
@[simp] theorem row_one : row 1 = 1 + X := by simp [row, state, step]

/-- The second transfer row. -/
theorem row_two : row 2 = 1 + 4 * X + X ^ 2 := by
  simp [row, state, step]
  ring

/-- The third transfer row. -/
theorem row_three : row 3 = 1 + 11 * X + 11 * X ^ 2 + X ^ 3 := by
  simp [row, state, step]
  ring

/-- The order-four scalar recurrence follows by expanding four transfer steps. -/
theorem row_add_four (r : ℕ) :
    row (r + 4) = (1 + 3 * X) * row (r + 3) +
      2 * X * (1 - X) * row (r + 2) +
      X * (2 - X - X ^ 2) * row (r + 1) + X ^ 2 * (1 - X) ^ 2 * row r := by
  simp only [row, state, step, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

private theorem state_coeff_above (r : ℕ) (i : Fin 4) (k : ℕ) (hk : r < k) :
    (state r i).coeff k = 0 := by
  induction r generalizing i k with
  | zero => fin_cases i <;> simp [state, coeff_one, ne_of_gt hk]
  | succ r ih =>
    cases k with
    | zero => lia
    | succ k =>
      have h₀ (j : Fin 4) := ih j (k + 1) (by lia)
      have h₁ (j : Fin 4) := ih j k (by lia)
      fin_cases i <;>
        simp [state, step, add_mul, mul_assoc, coeff_X_mul, h₀, h₁]

/-- Every transfer coordinate has degree at most the number of steps. -/
theorem state_natDegree_le (r : ℕ) (i : Fin 4) : (state r i).natDegree ≤ r :=
  natDegree_le_iff_coeff_eq_zero.mpr (state_coeff_above r i)

private theorem state_coeff_top (r : ℕ) (i : Fin 4) :
    (state r i).coeff r = if i = 0 then 1 else 0 := by
  induction r generalizing i with
  | zero => fin_cases i <;> simp [state]
  | succ r ih =>
    have h₀ (j : Fin 4) := state_coeff_above r j (r + 1) (by lia)
    fin_cases i <;>
      simp [state, step, add_mul, mul_assoc, coeff_X_mul, h₀, ih]

/-- The path-cube row has exact degree `r` for every natural index. -/
@[simp] theorem row_natDegree (r : ℕ) : (row r).natDegree = r := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (state_natDegree_le r 0)
  simp [state_coeff_top]

/-- Every path-cube row is monic. -/
theorem row_monic (r : ℕ) : (row r).Monic := by
  rw [Monic, leadingCoeff, row_natDegree]
  exact state_coeff_top r 0

private theorem state_coeff_zero (r : ℕ) : (state r 0).coeff 0 = 1 := by
  induction r with
  | zero => simp [state]
  | succ r ih => simpa [state, step, add_mul, mul_assoc] using ih

/-- The constant coefficient is always one. -/
@[simp] theorem row_coeff_zero (r : ℕ) : (row r).coeff 0 = 1 := state_coeff_zero r

private theorem state_hasNonnegCoeffs (r : ℕ) (i : Fin 4) :
    HasNonnegCoeffs (state r i) := by
  induction r generalizing i with
  | zero =>
    fin_cases i
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_zero
    · exact hasNonnegCoeffs_zero
    · exact hasNonnegCoeffs_zero
  | succ r ih =>
    have h₂ : HasNonnegCoeffs (2 : ℝ[X]) := by
      rintro (_ | k) <;> simp
    have h₃ : HasNonnegCoeffs (3 : ℝ[X]) := by
      rintro (_ | k) <;> simp
    fin_cases i
    · exact ((hasNonnegCoeffs_one.add hasNonnegCoeffs_X).mul (ih 0)).add
        ((h₂.mul hasNonnegCoeffs_X).mul (ih 1))
    · exact (((ih 0).add (hasNonnegCoeffs_X.mul (ih 1))).add
        ((h₂.add hasNonnegCoeffs_X).mul (ih 2))).add
        ((h₃.mul hasNonnegCoeffs_X).mul (ih 3))
    · exact (ih 0).add (hasNonnegCoeffs_X.mul (ih 1))
    · exact (ih 2).add (hasNonnegCoeffs_X.mul (ih 3))

/-- Nonnegativity follows from the four updates, at every index. -/
theorem row_hasNonnegCoeffs (r : ℕ) : HasNonnegCoeffs (row r) :=
  state_hasNonnegCoeffs r 0

/-- Every real root is strictly negative, independently of a splitting proof. -/
theorem row_roots_neg (r : ℕ) : ∀ x ∈ (row r).roots, x < 0 :=
  roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (row_hasNonnegCoeffs r)
    (by rw [row_coeff_zero]; norm_num)

end RealRooted.EffectiveBKW.PathCube
