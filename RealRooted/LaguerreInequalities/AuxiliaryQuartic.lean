module

public import RealRooted.Basic.Coefficients
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A quartic auxiliary polynomial and its translated exponential product

The even monic polynomial `X^4 + 4` has nonnegative coefficients and nonreal
zeros. Its four slopes cancel the first three mixed powers in the translated
product of `exp (-z^4)`. These are the algebraic ingredients of the counterexample
in `LaguerreInequalities.AuxiliaryCounterexample`.
-/

@[expose] public section

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

namespace RealRooted

/-- The even quartic auxiliary polynomial `X^4 + 4`. -/
def quarticAuxiliary : ℝ[X] := X ^ 4 + C 4

/-- The four slopes in the factorization of `X^4 + 4`. -/
def quarticSlope : Fin 4 → ℂ := ![1 + I, 1 - I, -1 + I, -1 - I]

/-- A real entire zero-free function outside the Laguerre--Pólya class. -/
def quarticDecay (z : ℂ) : ℂ := exp (-(z ^ 4))

/-- The translated product associated to the four quartic slopes. -/
def quarticTranslateProduct (x t : ℂ) : ℂ :=
  ∏ j : Fin 4, quarticDecay (x + quarticSlope j * t)

/-- All coefficients of the quartic auxiliary polynomial are nonnegative. -/
theorem hasNonnegCoeffs_quarticAuxiliary : HasNonnegCoeffs quarticAuxiliary :=
  (hasNonnegCoeffs_X.pow 4).add (hasNonnegCoeffs_C (by norm_num))

/-- The quartic auxiliary is even as a polynomial, not merely on the real axis. -/
theorem quarticAuxiliary_comp_neg_X : quarticAuxiliary.comp (-X) = quarticAuxiliary := by
  simp only [quarticAuxiliary, add_comp, pow_comp, X_comp, C_comp]
  ring

/-- The quartic auxiliary is monic. -/
theorem monic_quarticAuxiliary : quarticAuxiliary.Monic := by
  exact monic_X_pow_add_C 4 (by norm_num)

private theorem four_linear_factors {R : Type*} [CommRing R] (z i : R)
    (hi : i ^ 2 = -1) :
    (z + (1 + i)) * (z + (1 - i)) * (z + (-1 + i)) * (z + (-1 - i)) =
      z ^ 4 + 4 := by
  calc
    _ = z ^ 4 - 2 * z ^ 2 * i ^ 2 - 2 * z ^ 2 + (i ^ 2) ^ 2 - 2 * i ^ 2 + 1 := by
      ring
    _ = _ := by rw [hi]; ring

/-- The displayed slopes give the complete monic factorization over the complex numbers. -/
theorem map_quarticAuxiliary :
    quarticAuxiliary.map ofRealHom = ∏ j : Fin 4, (X + C (quarticSlope j)) := by
  rw [Fin.prod_univ_four]
  simp only [quarticAuxiliary, Polynomial.map_add, Polynomial.map_pow, map_X,
    quarticSlope, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_ofNat]
  convert (four_linear_factors (X : ℂ[X]) (C I) ?_).symm using 1 <;>
    simp [map_add, map_sub, map_neg, map_one, ← map_pow]

/-- The auxiliary polynomial has a nonreal zero, as required in Cardon's criterion. -/
theorem quarticAuxiliary_nonreal_zero :
    (quarticAuxiliary.map ofRealHom).eval (1 + I) = 0 ∧ (1 + I).im ≠ 0 := by
  constructor
  · rw [map_quarticAuxiliary, Fin.prod_univ_four]
    simp only [eval_mul, eval_add, eval_X, eval_C, quarticSlope,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  · simp

/-- The quartic exponential is entire. -/
theorem differentiable_quarticDecay : Differentiable ℂ quarticDecay := by
  unfold quarticDecay
  fun_prop

/-- The quartic exponential is real entire, expressed by conjugation symmetry. -/
theorem quarticDecay_conj (z : ℂ) : quarticDecay (conj z) = conj (quarticDecay z) := by
  simp [quarticDecay, ← Complex.exp_conj]

/-- The quartic exponential has no zeros, so in particular is not the zero function. -/
theorem quarticDecay_ne_zero (z : ℂ) : quarticDecay z ≠ 0 := Complex.exp_ne_zero _

/-- The four translated quartic exponentials have a particularly simple product. -/
theorem quarticTranslateProduct_eq (x t : ℂ) :
    quarticTranslateProduct x t = exp (-4 * x ^ 4) * exp (16 * t ^ 4) := by
  simp only [quarticTranslateProduct, Fin.prod_univ_four, quarticSlope,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    quarticDecay, ← Complex.exp_add]
  congr 1
  calc
    _ = -4 * x ^ 4 - 24 * x ^ 2 * t ^ 2 * (1 + I ^ 2) -
        4 * t ^ 4 * (1 + 6 * I ^ 2 + (I ^ 2) ^ 2) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The translated quartic product is entire in the translation parameter. -/
theorem differentiable_quarticTranslateProduct (x : ℂ) :
    Differentiable ℂ (quarticTranslateProduct x) := by
  have h : quarticTranslateProduct x = fun t =>
      exp (-4 * x ^ 4) * exp (16 * t ^ 4) := funext (quarticTranslateProduct_eq x)
  rw [h]
  fun_prop

end RealRooted
