module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic

import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Derivative
import RealRooted.Hermite.GaussianCoefficients
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Gaussian differential symbols and the heat sum

The full differential-symbol coefficient series of `exp (-t z²)` is exactly
the even-derivative heat series, including after every spatial derivative.
This fixes the parity and factorial normalizations needed for infinite-symbol
Laguerre--Pólya preservation.
-/

public section

open Complex

namespace RealRooted

/-- The ordinary Gaussian differential-symbol series sums to the corresponding
Taylor derivative of the entire heat image. -/
theorem hasSum_gaussian_differential {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t : ℂ) (k : ℕ) :
    HasSum (fun j : ℕ => iteratedDeriv j (fun z => exp (-t * z ^ 2)) 0 *
      iteratedDeriv (k + j) f 0 / (j.factorial : ℂ))
      (iteratedDeriv k (heatOperator t f) 0) := by
  let A : ℕ → ℂ := fun j => iteratedDeriv j (fun z => exp (-t * z ^ 2)) 0 *
    iteratedDeriv (k + j) f 0 / (j.factorial : ℂ)
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k (WithTop.coe_lt_top _)
  have he : HasSum (fun n : ℕ => (-t) ^ n / (n.factorial : ℂ) *
      iteratedDeriv (2 * n) (iteratedDeriv k f) 0) (heatOperator t (iteratedDeriv k f) 0) :=
    (summable_norm_heatOperator hdf (horder.iteratedDeriv hf k) hρ t 0).of_norm.hasSum
  have heven : HasSum (fun n => A (2 * n)) (heatOperator t (iteratedDeriv k f) 0) := by
    apply he.congr
    intro S
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [A]
    rw [iteratedDeriv_exp_mul_sq_zero_even]
    simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm k]
    have hfac : ((2 * n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * n).factorial_ne_zero
    field_simp
  have hodd : HasSum (fun n => A (2 * n + 1)) 0 := by
    simp only [A, iteratedDeriv_exp_mul_sq_zero_odd, zero_mul, zero_div]
    exact hasSum_zero
  have h := heven.even_add_odd hodd
  rw [add_zero, ← congrFun (iteratedDeriv_heatOperator hf horder hρ t k) 0] at h
  exact h

end RealRooted
