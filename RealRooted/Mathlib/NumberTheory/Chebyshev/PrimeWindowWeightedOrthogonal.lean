/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowContinuous
public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowOrthogonal
import RealRooted.Mathlib.Algebra.Polynomial.Moment.FiniteAtoms
import Mathlib.Tactic.Ring

/-!
# Monic polynomials from weighted prime-window moments

The finite moment solve always defines a monic polynomial. Its orthogonality
to the actual finite weighted prime sum requires a nonsingular Hankel matrix.
No RH assumption is used in these algebraic facts.
-/

public section

open Polynomial

namespace Chebyshev

/-- The monic moment polynomial for a prime window with an additional weight.
This definition alone does not assert orthogonality for a singular moment matrix. -/
@[expose] noncomputable def primeWindowWeightedPolynomial
    (W : ℝ → ℝ) (X H : ℝ) (n : ℕ) : ℝ[X] :=
  monicMomentPolynomial (primeWindowWeightedMoment W X H) n

/-- Every weighted moment solve has the prescribed monic degree. -/
theorem isMonicOfDegree_primeWindowWeightedPolynomial
    (W : ℝ → ℝ) (X H : ℝ) (n : ℕ) :
    IsMonicOfDegree (primeWindowWeightedPolynomial W X H n) n :=
  isMonicOfDegree_monicMomentPolynomial _ _

/-- The degree-zero weighted polynomial is one even for an empty window. -/
@[simp] theorem primeWindowWeightedPolynomial_zero (W : ℝ → ℝ) (X H : ℝ) :
    primeWindowWeightedPolynomial W X H 0 = 1 := by
  simp only [primeWindowWeightedPolynomial, monicMomentPolynomial_zero]

/-- The constant unit reference weight gives the original prime-window polynomial. -/
@[simp] theorem primeWindowWeightedPolynomial_one (X H : ℝ) (n : ℕ) :
    primeWindowWeightedPolynomial (fun _ ↦ 1) X H n = primeWindowPolynomial X H n := by
  unfold primeWindowWeightedPolynomial primeWindowPolynomial
  apply congrArg (fun μ ↦ monicMomentPolynomial μ n)
  funext k
  simp only [primeWindowWeightedMoment, primeWindowMoment, mul_one]

/-- Weighted prime moments are finite atomic moments with the product weight. -/
theorem primeWindowWeightedMoment_eq_sum (W : ℝ → ℝ) (X H : ℝ) (k : ℕ) :
    primeWindowWeightedMoment W X H k =
      ∑ a ∈ primeWindow X H,
        ((Real.log a / H) * W (((a : ℝ) - X) / H)) * (((a : ℝ) - X) / H) ^ k := by
  unfold primeWindowWeightedMoment
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The weighted moment pairing is the original finite prime sum. -/
theorem momentPairing_primeWindowWeightedMoment
    (W : ℝ → ℝ) (X H : ℝ) (p q : ℝ[X]) :
    momentPairing (primeWindowWeightedMoment W X H) p q =
      ∑ a ∈ primeWindow X H, ((Real.log a / H) * W (((a : ℝ) - X) / H)) *
        p.eval (((a : ℝ) - X) / H) * q.eval (((a : ℝ) - X) / H) := by
  have hm : primeWindowWeightedMoment W X H = fun k ↦
      ∑ a ∈ primeWindow X H,
        ((Real.log a / H) * W (((a : ℝ) - X) / H)) * (((a : ℝ) - X) / H) ^ k :=
    funext (primeWindowWeightedMoment_eq_sum W X H)
  rw [hm]
  exact momentPairing_finset_sum _ _ _ _ _

/-- Nonnegative reference weights give positive semidefinite Hankel matrices
for every positive-length prime window, without any support-size assumption. -/
theorem primeWindowWeightedMoment_hankel_posSemidef {W : ℝ → ℝ} {X H : ℝ}
    (hH : 0 < H) (hW : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ W x) (n : ℕ) :
    (momentHankelMatrix (primeWindowWeightedMoment W X H) n).PosSemidef := by
  apply momentHankelMatrix_posSemidef_of_nonneg
  intro p _
  rw [momentPairing_primeWindowWeightedMoment]
  apply Finset.sum_nonneg
  intro a ha
  have hx := primeWindow_node_mem_Ioc hH ha
  have hw := mul_nonneg (primeWindow_weight_pos hH ha).le (hW _ ⟨hx.1.le, hx.2⟩)
  simpa only [pow_two, mul_assoc] using mul_nonneg hw
    (sq_nonneg (p.eval (((a : ℝ) - X) / H)))

/-- A nonsingular weighted Hankel matrix gives orthogonality in the actual
finite weighted prime sum to every lower-degree polynomial. -/
theorem sum_primeWindowWeightedPolynomial_mul_eval_eq_zero
    (W : ℝ → ℝ) (X H : ℝ) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix (primeWindowWeightedMoment W X H) n).det)
    {p : ℝ[X]} (hp : p.degree < n) :
    (∑ a ∈ primeWindow X H, ((Real.log a / H) * W (((a : ℝ) - X) / H)) *
      p.eval (((a : ℝ) - X) / H) *
      (primeWindowWeightedPolynomial W X H n).eval (((a : ℝ) - X) / H)) = 0 := by
  rw [← momentPairing_primeWindowWeightedMoment]
  exact momentPairing_monicMomentPolynomial _ n hdet hp

end Chebyshev
