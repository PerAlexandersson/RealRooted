/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindow
public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
import RealRooted.Mathlib.Algebra.Polynomial.Moment.FiniteAtoms

/-!
# Monic polynomials from finite prime-window moments

The moment solve is monic of the prescribed degree for every input. Its
orthogonality is asserted only when the finite Hankel determinant is a unit.
The orthogonality is also expressed as the original finite weighted prime sum.
-/

public section

open Polynomial

namespace Chebyshev

/-- The monic degree-`n` polynomial obtained from the finite prime-window
moment solve. Orthogonality requires invertibility of the finite moment matrix. -/
@[expose] noncomputable def primeWindowPolynomial (X H : ℝ) (n : ℕ) : ℝ[X] :=
  monicMomentPolynomial (primeWindowMoment X H) n

/-- The moment construction always has the prescribed monic degree. -/
theorem isMonicOfDegree_primeWindowPolynomial (X H : ℝ) (n : ℕ) :
    IsMonicOfDegree (primeWindowPolynomial X H n) n :=
  isMonicOfDegree_monicMomentPolynomial _ _

/-- Degree zero gives the constant polynomial one, including empty prime windows. -/
@[simp] theorem primeWindowPolynomial_zero (X H : ℝ) : primeWindowPolynomial X H 0 = 1 := by
  simp only [primeWindowPolynomial, monicMomentPolynomial_zero]

/-- Prime-window moment pairings are actual finite weighted prime sums. -/
theorem momentPairing_primeWindowMoment (X H : ℝ) (p q : ℝ[X]) :
    momentPairing (primeWindowMoment X H) p q =
      ∑ a ∈ primeWindow X H, (Real.log a / H) *
        p.eval (((a : ℝ) - X) / H) * q.eval (((a : ℝ) - X) / H) :=
  momentPairing_finset_sum _ _ _ _ _

/-- Prime-window Hankel matrices are positive semidefinite for every positive
window length; no lower bound on the number of primes is assumed. -/
theorem primeWindowMoment_hankel_posSemidef {X H : ℝ} (hH : 0 < H) (n : ℕ) :
    (momentHankelMatrix (primeWindowMoment X H) n).PosSemidef := by
  apply momentHankelMatrix_finset_sum_posSemidef
  intro p hp
  exact (primeWindow_weight_pos hH hp).le

/-- A nonsingular finite prime moment matrix gives genuine weighted-sum
orthogonality to every lower-degree polynomial. -/
theorem sum_primeWindowPolynomial_mul_eval_eq_zero (X H : ℝ) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix (primeWindowMoment X H) n).det)
    {p : ℝ[X]} (hp : p.degree < n) :
    (∑ a ∈ primeWindow X H, (Real.log a / H) *
      p.eval (((a : ℝ) - X) / H) *
      (primeWindowPolynomial X H n).eval (((a : ℝ) - X) / H)) = 0 := by
  rw [← momentPairing_primeWindowMoment]
  exact momentPairing_monicMomentPolynomial _ n hdet hp

end Chebyshev
