/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.OfFn
import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Strict positivity of Hankel moment matrices

A nonnegative measure with all polynomial moments and infinitely many
positive atoms gives positive definite Hankel matrices at every natural shift.
A nonzero polynomial cannot vanish at all those atoms, so its weighted square
has strictly positive integral.
-/

public section

open MeasureTheory Polynomial

namespace MeasureTheory

private theorem integral_weighted_eval_sq_pos
    {mu : Measure ℝ} (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hinf : Set.Infinite {x : ℝ | 0 < x ∧ 0 < mu {x}})
    {p : ℝ[X]} (hp : p ≠ 0) (r : ℕ) :
    0 < ∫ x : ℝ, x ^ r * p.eval x ^ 2 ∂mu := by
  have hint : Integrable (fun x : ℝ => x ^ r * p.eval x ^ 2) mu := by
    have h := TauCeti.integrable_eval_of_forall_integrable_pow hmom (X ^ r * p ^ 2)
    apply h.congr
    filter_upwards [] with x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  apply (integral_pos_iff_support_of_nonneg_ae
    (hpos.mono fun x hx => mul_nonneg (pow_nonneg hx r) (sq_nonneg _)) hint).mpr
  obtain ⟨x, hx, hpx⟩ := (hinf.sdiff (finite_setOfPred_isRoot hp)).nonempty
  have hpne : p.eval x ≠ 0 := hpx
  have hxmem : x ∈ Function.support (fun x : ℝ => x ^ r * p.eval x ^ 2) :=
    mul_ne_zero (pow_ne_zero _ hx.1.ne') (pow_ne_zero _ hpne)
  exact hx.2.trans_le (measure_mono (Set.singleton_subset_iff.mpr hxmem))

/-- Infinitely many positive atoms force strict positivity of every shifted
Hankel moment matrix, including the empty matrix and shift zero. -/
theorem posDef_integral_pow_hankel_of_infinite_atoms
    {mu : Measure ℝ} (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hinf : Set.Infinite {x : ℝ | 0 < x ∧ 0 < mu {x}}) (n r : ℕ) :
    Matrix.PosDef (fun i j : Fin n => ∫ x : ℝ, x ^ (i.val + j.val + r) ∂mu) := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [Nat.add_comm]
  · intro v hv
    let p := Polynomial.ofFn n v
    have hp : p ≠ 0 := by
      intro hz
      apply hv
      apply Polynomial.injective_ofFn n
      simpa only [map_zero] using hz
    have heq (x : ℝ) : x ^ r * p.eval x ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, v i * (x ^ (i.val + j.val + r) * v j) := by
      simp only [p, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
        Polynomial.eval_monomial,
        pow_two, pow_add, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hint (i j : Fin n) : Integrable
        (fun x : ℝ => v i * (x ^ (i.val + j.val + r) * v j)) mu :=
      ((hmom _).mul_const _).const_mul _
    have hstrict := integral_weighted_eval_sq_pos hmom hpos hinf hp r
    simp_rw [heq] at hstrict
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))] at hstrict
    simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul,
      integral_mul_const] at hstrict
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum] using hstrict

end MeasureTheory
