module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import RealRooted.Mathlib.RingTheory.Polynomial.Chebyshev.Bounds

/-!
# Chebyshev values and the cofactor of `X ^ 2 - 2 x X + 1`

`chebU x n` is the value of the Chebyshev polynomial of the second kind `U_n` at `x`.  The
polynomials `qPoly x k` are the quotients of `X ^ (k + 1)` by `X ^ 2 - 2 x X + 1`; their
coefficients are values of `U`, which gives the coefficient bounds used for the signed
Toeplitz perturbation.
-/

@[expose] public section

open Polynomial

noncomputable section


namespace RealRooted.ToeplitzPerturbation

/-- Chebyshev polynomial of the second kind `U_n` evaluated at `x`. -/
def chebU (x : ℝ) (n : ℕ) : ℝ := (Chebyshev.U ℝ n).eval x

/-- `U_{k-1}(x)`, with the convention `U_{-1} = 0`. -/
def chebUPred (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => chebU x k

@[simp] theorem chebU_zero (x : ℝ) : chebU x 0 = 1 := by simp [chebU]

@[simp] theorem chebU_one (x : ℝ) : chebU x 1 = 2 * x := by simp [chebU]

theorem chebU_add_two (x : ℝ) (n : ℕ) : chebU x (n + 2) = 2 * x * chebU x (n + 1) - chebU x n := by
  have := Chebyshev.U_add_two ℝ (n : ℤ)
  simp only [chebU]
  push_cast at this ⊢
  simp [this]

theorem chebU_succ (x : ℝ) (k : ℕ) : chebU x (k + 1) = 2 * x * chebU x k - chebUPred x k := by
  cases k with
  | zero => simp [chebUPred]
  | succ k => simpa [chebUPred] using chebU_add_two x k

theorem chebU_mul_sin (θ : ℝ) (n : ℕ) :
    chebU (Real.cos θ) n * Real.sin θ = Real.sin ((n + 1) * θ) := by
  simp [chebU]

theorem chebUPred_mul_sin (θ : ℝ) (n : ℕ) :
    chebUPred (Real.cos θ) n * Real.sin θ = Real.sin (n * θ) := by
  cases n with
  | zero => simp [chebUPred]
  | succ n => simp [chebUPred, chebU_mul_sin θ n]

/-- `|U_n(x)| ≤ n + 1` on `[-1, 1]`; this is `Polynomial.Chebyshev.abs_eval_U_le`. -/
theorem abs_chebU_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) : |chebU x n| ≤ n + 1 :=
  Polynomial.Chebyshev.abs_eval_U_le (K := ℝ) n hx

theorem abs_chebUPred_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) : |chebUPred x n| ≤ n := by
  cases n with
  | zero => simp [chebUPred]
  | succ n => simpa [chebUPred] using abs_chebU_le hx n

/-- The quotient of `X ^ (k + 1)` by `X ^ 2 - 2 x X + 1`. -/
def qPoly (x : ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | k + 1 => X * qPoly x k + C (chebU x k)

theorem X_pow_succ_eq (x : ℝ) (k : ℕ) :
    (X ^ 2 - C (2 * x) * X + 1) * qPoly x k + C (chebU x k) * X - C (chebUPred x k) =
      X ^ (k + 1) := by
  induction k with
  | zero => simp [qPoly, chebUPred]
  | succ k ih =>
    have h1 : C (chebU x (k + 1)) = C (2 * x) * C (chebU x k) - C (chebUPred x k) := by
      rw [chebU_succ, map_sub, map_mul]
    rw [show X ^ (k + 1 + 1) = X * X ^ (k + 1) by ring, ← ih, qPoly, h1]
    simp only [chebUPred]
    ring

theorem coeff_qPoly (x : ℝ) (j m : ℕ) :
    (qPoly x j).coeff m = if m < j then chebU x (j - 1 - m) else 0 := by
  induction j generalizing m with
  | zero => simp [qPoly]
  | succ j ih =>
    cases m with
    | zero => simp [qPoly]
    | succ m =>
      simp only [qPoly, coeff_add, coeff_X_mul, ih, coeff_C, Nat.succ_ne_zero, ite_false, add_zero]
      split_ifs <;> first | rfl | (congr 1; lia)

end RealRooted.ToeplitzPerturbation
