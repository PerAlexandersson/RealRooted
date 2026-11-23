/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Contraction

/-!
# Translation of formal Jacobi coefficients

A binomial transform adds its parameter to every diagonal coefficient of
a Jacobi fraction and leaves its outgoing numerator unchanged. This is a
formal identity over a commutative ring, including zero coefficients and
terminating fractions.

See Barry, J. Integer Sequences 12 (2009), Proposition 4, and Sokal-Walrad,
arXiv:2404.12131v1, equations (7)-(9).
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Binomial transformation shifts the diagonal of one Jacobi step. -/
theorem binomialTransform_jacobiStep (c b d : R) (f : R⟦X⟧) :
    binomialTransform c (jacobiStep b d f) =
      jacobiStep (b + c) d (binomialTransform c f) := by
  let G : R⟦X⟧ := stieltjesStep c 1
  let y : R⟦X⟧ := X * G
  have hy : HasSubst y := .of_constantCoeff_zero' (by simp [y])
  have hG : (1 - C c * X) * G = 1 := by
    simpa only [G, mul_one] using one_sub_mul_stieltjesStep c (1 : R⟦X⟧)
  have hs := congrArg (substAlgHom (R := R) hy) (one_sub_mul_jacobiStep b d f)
  simp only [map_mul, map_sub, map_one, map_pow, coe_substAlgHom, subst_C, ← C_apply,
    subst_X hy] at hs
  apply eq_jacobiStep_of_mul_eq_one
  change (1 - C (b + c) * X - C d * X ^ 2 * (G * f.subst y)) *
    (G * (jacobiStep b d f).subst y) = 1
  simp only [map_add]
  dsimp only [y] at hs ⊢
  linear_combination hs + (jacobiStep b d f).subst (X * G) * hG

/-- Every member of a formal Jacobi tail family undergoes the same diagonal shift. -/
theorem binomialTransform_jacobiTail_eq_step (c : R) {b d : ℕ → R}
    {F : ℕ → R⟦X⟧}
    (hF : ∀ n, F n = jacobiStep (b n) (d n) (F (n + 1))) (n : ℕ) :
    binomialTransform c (F n) =
      jacobiStep (b n + c) (d n) (binomialTransform c (F (n + 1))) := by
  rw [hF n, binomialTransform_jacobiStep]

/-- Equal contracted Jacobi data identify a translated Stieltjes fraction.
No standard-tail or nonvanishing condition is required. -/
theorem binomialTransform_stieltjesTail_eq {a a' : ℕ → R} (c : R)
    (hd : ∀ n, stieltjesJacobiDiagonal a' n = stieltjesJacobiDiagonal a n + c)
    (hn : ∀ n, stieltjesJacobiNumerator a' n = stieltjesJacobiNumerator a n) :
    binomialTransform c (stieltjesTail a 0) = stieltjesTail a' 0 := by
  have h : (fun n => binomialTransform c (stieltjesJacobiTail a n)) =
      stieltjesJacobiTail a' := by
    apply eq_of_jacobiStep_eq
    · intro n
      rw [stieltjesJacobiTail_eq_step, binomialTransform_jacobiStep, ← hd n, ← hn n]
    · exact stieltjesJacobiTail_eq_step a'
  exact congrFun h 0

end PowerSeries
