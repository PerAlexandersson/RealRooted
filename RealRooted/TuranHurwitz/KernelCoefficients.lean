module

public import RealRooted.TuranHurwitz.FormalKernel
public import RealRooted.TuranHurwitz.IntervalOperator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Even coefficients of the formal hyperbolic kernel

The formal PDE gives the coefficient recurrence. Multiplication by `(2n)!`
identifies the even coefficients with the interval-rooted algebraic rows.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The coefficient recurrence obtained from the formal PDE. -/
theorem coeff_hyperbolicKernel_step (d : ℝ) (k : ℕ) :
    C ((k + 1 : ℝ) * (k + 2 : ℝ)) * PowerSeries.coeff (k + 2) (hyperbolicKernel d) =
      X * intervalOperator d (PowerSeries.coeff k (hyperbolicKernel d)) := by
  have hA : (4 * PowerSeries.C (X : ℝ[X]) ^ 2 * (1 + PowerSeries.C X)) =
      PowerSeries.C (4 * X ^ 2 * (1 + X)) := by
    simp only [map_mul, map_add, map_pow, map_ofNat, map_one]
  have hB : PowerSeries.C (X : ℝ[X]) *
      (4 + PowerSeries.C (C (4 * d + 6)) * PowerSeries.C X) =
      PowerSeries.C (X * (4 + C (4 * d + 6) * X)) := by
    simp only [map_mul, map_add, map_ofNat]
  have hC : PowerSeries.C (C (2 * d)) * PowerSeries.C (X : ℝ[X]) =
      PowerSeries.C (C (2 * d) * X) := by simp only [map_mul]
  have h := congrArg (PowerSeries.coeff k) (hyperbolicKernel_pde d)
  rw [hA, hB, hC, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
  rw [(PowerSeries.coeff k).map_add, (PowerSeries.coeff k).map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at h
  simp only [parameterDerivative, PowerSeries.coeff_mapDerivation,
    Polynomial.derivative'_apply, Nat.cast_add, Nat.cast_one] at h
  rw [show k + 1 + 1 = k + 2 by lia] at h
  simp only [intervalOperator, map_mul, map_add, map_natCast, map_one, map_ofNat] at h ⊢
  linear_combination h

/-- Factorially normalized even coefficients of `(1-z sinh(t)²)^(-d)`. -/
@[expose] noncomputable def kernelEvenRow (d : ℝ) (n : ℕ) : ℝ[X] :=
  C ((2 * n).factorial : ℝ) * PowerSeries.coeff (2 * n) (hyperbolicKernel d)

/-- The kernel's zeroth coefficient is one. -/
@[simp] theorem kernelEvenRow_zero (d : ℝ) : kernelEvenRow d 0 = 1 := by
  simp [kernelEvenRow]

/-- The factorial normalization gives exactly the algebraic interval-row recurrence. -/
theorem kernelEvenRow_succ (d : ℝ) (n : ℕ) :
    kernelEvenRow d (n + 1) = X * intervalOperator d (kernelEvenRow d n) := by
  have h := coeff_hyperbolicKernel_step d (2 * n)
  have hfac : ((2 * (n + 1)).factorial : ℝ) =
      ((2 * n).factorial : ℝ) * (2 * n + 1 : ℝ) * (2 * n + 2 : ℝ) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by lia,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [kernelEvenRow, hfac]
  simp only [map_mul]
  change C ((2 * n).factorial : ℝ) * C (2 * n + 1 : ℝ) * C (2 * n + 2 : ℝ) *
      PowerSeries.coeff (2 * n + 2) (hyperbolicKernel d) = _
  rw [kernelEvenRow]
  rw [intervalOperator_C_mul]
  simp only [Nat.cast_mul, Nat.cast_ofNat, map_mul] at h ⊢
  linear_combination C ((2 * n).factorial : ℝ) * h

/-- The paper's coefficient identification, proved without Taylor convergence. -/
theorem kernelEvenRow_eq_intervalRow (d : ℝ) (n : ℕ) :
    kernelEvenRow d n = intervalRow d n := by
  induction n with
  | zero => simp [intervalRow]
  | succ n ih => rw [kernelEvenRow_succ, ih, intervalRow]

/-- The even kernel coefficient is the interval row divided by its factorial normalization. -/
theorem coeff_even_hyperbolicKernel (d : ℝ) (n : ℕ) :
    PowerSeries.coeff (2 * n) (hyperbolicKernel d) =
      C (((2 * n).factorial : ℝ)⁻¹) * intervalRow d n := by
  have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h := kernelEvenRow_eq_intervalRow d n
  rw [kernelEvenRow] at h
  calc
    _ = C (((2 * n).factorial : ℝ)⁻¹) *
        (C ((2 * n).factorial : ℝ) * PowerSeries.coeff (2 * n) (hyperbolicKernel d)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hfac, map_one, one_mul]
    _ = _ := by rw [h]

/-- Every even coefficient has exactly the degree claimed in the coefficient lemma. -/
theorem natDegree_coeff_even_hyperbolicKernel {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (PowerSeries.coeff (2 * n) (hyperbolicKernel d)).natDegree = n := by
  have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [coeff_even_hyperbolicKernel, natDegree_C_mul (inv_ne_zero hfac)]
  exact (intervalRow_natDegree_and_leadingCoeff_pos hd n).1

/-- Every even coefficient is nonzero and all its roots lie in `[-1, 0]`. -/
theorem coeff_even_hyperbolicKernel_roots {d : ℝ} (hd : 0 < d) (n : ℕ) :
    PowerSeries.coeff (2 * n) (hyperbolicKernel d) ≠ 0 ∧
      (PowerSeries.coeff (2 * n) (hyperbolicKernel d)).Splits ∧
      ∀ r ∈ (PowerSeries.coeff (2 * n) (hyperbolicKernel d)).roots,
        r ∈ Set.Icc (-1 : ℝ) 0 := by
  have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hrow := intervalRow_splits_and_roots_mem_Icc hd n
  have hne : intervalRow d n ≠ 0 := leadingCoeff_ne_zero.mp
    (intervalRow_natDegree_and_leadingCoeff_pos hd n).2.ne'
  rw [coeff_even_hyperbolicKernel]
  refine ⟨mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hfac)) hne,
    hrow.1.C_mul _, ?_⟩
  rw [roots_C_mul _ (inv_ne_zero hfac)]
  exact hrow.2

end RealRooted.TuranHurwitz
