import RealRooted.MultiplierSequence.Bidiagonal

/-!
# Second-derivative bidiagonal normalization

This module identifies a six-parameter second-derivative polynomial operator
with a coefficient-bidiagonal operator. It is independent of PF-preserver
certificates and tactic frontends.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Quadratic coefficient shape produced by a second-derivative operator. -/
def secondDerivativeQuadraticCoeff (a b c : ℝ) (k : ℕ) : ℝ :=
  a + b * (k : ℝ) + c * (k : ℝ) * ((k : ℝ) - 1)

/-- Six-parameter second-derivative operator with lower-bidiagonal coefficient
action. -/
def secondDerivativeBidiagonalForm
    (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a0 * p +
    C a1 * (X * p) +
    C b1 * (X * p.derivative) +
    C b2 * (X * (X * p.derivative)) +
    C c2 * (X * (X * p.derivative.derivative)) +
    C c3 * (X * (X * (X * p.derivative.derivative)))

/-- The six-parameter second-derivative form is coefficient-bidiagonal. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator
        (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
        (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k)
        p := by
  ext k
  cases k with
  | zero =>
      simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
        secondDerivativeQuadraticCoeff]
  | succ k =>
      cases k with
      | zero =>
          simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
            secondDerivativeQuadraticCoeff, coeff_derivative]
          ring
      | succ k =>
          cases k with
          | zero =>
              simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
                secondDerivativeQuadraticCoeff, coeff_derivative]
              ring
          | succ k =>
              simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
                secondDerivativeQuadraticCoeff, coeff_derivative]
              ring

/-- Normalize a second-derivative form to a named coefficient-bidiagonal
operator by identifying its two quadratic coefficient functions. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq
    {alpha beta : ℕ → ℝ} {a0 a1 b1 b2 c2 c3 : ℝ} (p : ℝ[X])
    (halpha : ∀ k : ℕ, secondDerivativeQuadraticCoeff a0 b1 c2 k = alpha k)
    (hbeta : ∀ k, secondDerivativeQuadraticCoeff a1 b2 c3 k = beta k) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator alpha beta p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    exact halpha k
  · funext k
    exact hbeta k

end RealRooted
