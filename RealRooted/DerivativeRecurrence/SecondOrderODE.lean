import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Second-order recurrences with an eigen-ODE

Let `P (n + 1) = A * (P n)'' + b n * (P n)' + c n * P n` with `A` independent of `n`.
For Laguerre-type families every row is an eigenfunction of the operator
`A D² + β D`:

`A * (P n)'' + β * (P n)' = C (ev n) * P n`.

The second-order step then collapses to a first-order one,

`P (n + 1) = (b n - β) * (P n)' + (c n + C (ev n)) * P n`,

to which the first-order degree and interlacing theory applies.

`derivRec₂_ode` proves the eigen-ODE for every row from the base row and three
polynomial identities that do not mention `P`.  With `u = b n - β`,
`v = c n + C (ev n)` and `w = W n + v`, they say that

`(A D² + β D - ev (n + 1)) (u p' + v p) = u (A D² + β D - ev n)' p + w (A D² + β D - ev n) p`

holds identically, by comparing the coefficients of `p''`, `p'` and `p`.  A tactic
can find `β`, `ev` and `W` from finitely many rows and check the identities with
`ring`.

## Main results

* `derivRec₂_ode`: the eigen-ODE for every row.
* `derivRec₂_firstOrder`: the collapsed first-order recurrence.
* `div_ofNat_eq_C_mul`: `p / n = C n⁻¹ * p`, to normalize generated coefficients.
-/

open Polynomial

namespace RealRooted

/-- Division by a numeral, as generated recurrences write `(1 / 2) * X`. -/
theorem div_ofNat_eq_C_mul (p : ℝ[X]) (m : ℕ) [m.AtLeastTwo] :
    p / (no_index (OfNat.ofNat m : ℝ[X])) = C ((OfNat.ofNat m : ℝ)⁻¹) * p := by
  rw [← map_ofNat C m, div_C, mul_comm]

variable {P b c W : ℕ → ℝ[X]} {A β : ℝ[X]} {ev : ℕ → ℝ}

/-- The eigen-ODE collapses the second-order step to a first-order one. -/
theorem derivRec₂_firstOrder_of_ode
    (hrec : ∀ n, P (n + 1) =
      A * (P n).derivative.derivative + b n * (P n).derivative + c n * P n)
    {n : ℕ} (hode : A * (P n).derivative.derivative + β * (P n).derivative = C (ev n) * P n) :
    P (n + 1) = (b n - β) * (P n).derivative + (c n + C (ev n)) * P n := by
  rw [hrec n]
  linear_combination hode

/-- Every row is an eigenfunction of `A D² + β D`, given the base row and the
three coefficient identities. -/
theorem derivRec₂_ode
    (hrec : ∀ n, P (n + 1) =
      A * (P n).derivative.derivative + b n * (P n).derivative + c n * P n)
    (h0 : A * (P 0).derivative.derivative + β * (P 0).derivative = C (ev 0) * P 0)
    (h1 : ∀ n, A * (2 * derivative (b n - β) - W n) = (b n - β) * derivative A)
    (h2 : ∀ n, A * derivative (derivative (b n - β)) + 2 * A * derivative (c n + C (ev n)) +
        β * derivative (b n - β) + β * (c n + C (ev n)) - C (ev (n + 1)) * (b n - β) -
        (b n - β) * derivative β + C (ev n) * (b n - β) - (W n + (c n + C (ev n))) * β = 0)
    (h3 : ∀ n, A * derivative (derivative (c n + C (ev n))) + β * derivative (c n + C (ev n)) -
        C (ev (n + 1)) * (c n + C (ev n)) + (W n + (c n + C (ev n))) * C (ev n) = 0) :
    ∀ n, A * (P n).derivative.derivative + β * (P n).derivative = C (ev n) * P n
  | 0 => h0
  | n + 1 => by
      have ih := derivRec₂_ode hrec h0 h1 h2 h3 n
      have ihd := congrArg derivative ih
      have e1 := h1 n
      have e2 := h2 n
      have e3 := h3 n
      rw [derivRec₂_firstOrder_of_ode hrec ih]
      simp only [derivative_add, derivative_sub, derivative_mul, derivative_C, zero_mul,
        zero_add, add_zero] at ihd e1 e2 e3 ⊢
      linear_combination (b n - β) * ihd + (W n + (c n + C (ev n))) * ih +
        (P n).derivative.derivative * e1 + (P n).derivative * e2 + P n * e3

/-- The collapsed first-order recurrence, for every row. -/
theorem derivRec₂_firstOrder
    (hrec : ∀ n, P (n + 1) =
      A * (P n).derivative.derivative + b n * (P n).derivative + c n * P n)
    (h0 : A * (P 0).derivative.derivative + β * (P 0).derivative = C (ev 0) * P 0)
    (h1 : ∀ n, A * (2 * derivative (b n - β) - W n) = (b n - β) * derivative A)
    (h2 : ∀ n, A * derivative (derivative (b n - β)) + 2 * A * derivative (c n + C (ev n)) +
        β * derivative (b n - β) + β * (c n + C (ev n)) - C (ev (n + 1)) * (b n - β) -
        (b n - β) * derivative β + C (ev n) * (b n - β) - (W n + (c n + C (ev n))) * β = 0)
    (h3 : ∀ n, A * derivative (derivative (c n + C (ev n))) + β * derivative (c n + C (ev n)) -
        C (ev (n + 1)) * (c n + C (ev n)) + (W n + (c n + C (ev n))) * C (ev n) = 0) (n : ℕ) :
    P (n + 1) = (b n - β) * (P n).derivative + (c n + C (ev n)) * P n :=
  derivRec₂_firstOrder_of_ode hrec (derivRec₂_ode hrec h0 h1 h2 h3 n)

end RealRooted
