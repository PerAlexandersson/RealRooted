module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Analytic generalized Laguerre coefficients

The coefficient of `t^(2n)` in `f(x + i t) f(x - i t)` is the generalized
Laguerre coefficient of order `n`. For a real entire function the product is
even and agrees with the squared modulus on the real axis.
-/

@[expose] public section

open Complex
open scoped ComplexConjugate

noncomputable section

namespace RealRooted

/-- The product of the two opposite imaginary translates of `f` at `x`. -/
def laguerreProduct (f : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  f (x + z * I) * f (x - z * I)

/-- The generalized Laguerre coefficient: the coefficient of `z^(2n)` in the
Taylor expansion of `laguerreProduct f x` at zero. -/
def laguerreCoefficient (f : ℂ → ℂ) (x : ℝ) (n : ℕ) : ℝ :=
  (iteratedDeriv (2 * n) (laguerreProduct f x) 0).re / (2 * n).factorial

/-- The Laguerre product of an entire function is entire. -/
theorem differentiable_laguerreProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℝ) :
    Differentiable ℂ (laguerreProduct f x) := by
  exact (hf.comp (by fun_prop)).mul (hf.comp (by fun_prop))

/-- The Laguerre product is even. -/
@[simp]
theorem laguerreProduct_neg (f : ℂ → ℂ) (x : ℝ) (z : ℂ) :
    laguerreProduct f x (-z) = laguerreProduct f x z := by
  simp [laguerreProduct, sub_eq_add_neg, mul_comm]

/-- Conjugation symmetry is inherited by the Laguerre product. -/
theorem laguerreProduct_conj {f : ℂ → ℂ}
    (hf : ∀ z, f (conj z) = conj (f z)) (x : ℝ) (z : ℂ) :
    laguerreProduct f x (conj z) = conj (laguerreProduct f x z) := by
  rw [laguerreProduct, laguerreProduct, map_mul, ← hf, ← hf]
  simp [mul_comm, sub_eq_add_neg]

/-- On the real axis the Laguerre product is the squared modulus. -/
theorem laguerreProduct_ofReal {f : ℂ → ℂ}
    (hf : ∀ z, f (conj z) = conj (f z)) (x y : ℝ) :
    laguerreProduct f x y = (‖f (x + (y : ℂ) * I)‖ ^ 2 : ℝ) := by
  have h : (x : ℂ) - y * I = conj ((x : ℂ) + y * I) := by simp [sub_eq_add_neg]
  rw [laguerreProduct, h, hf, mul_conj, normSq_eq_norm_sq]

end RealRooted
