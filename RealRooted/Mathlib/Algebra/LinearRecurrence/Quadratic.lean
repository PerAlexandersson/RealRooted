import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quadratic linear recurrences

This Mathlib-shaped shim packages a second-order constant-coefficient
recurrence and its elementary factor telescoping identity. It is purely
algebraic; real root bounds and explicit quadratic formulae belong to clients.
-/

namespace LinearRecurrence

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The recurrence `S (n + 2) = p * S (n + 1) + q * S n`. -/
def quadratic (p q : R) : LinearRecurrence R :=
  ⟨2, ![q, p]⟩

/-- A sequence solves `quadratic p q` precisely when it satisfies its
second-order recurrence. -/
theorem quadratic_isSolution_iff (p q : R) (S : ℕ → R) :
    (quadratic p q).IsSolution S ↔ ∀ n, S (n + 2) = p * S (n + 1) + q * S n := by
  unfold quadratic LinearRecurrence.IsSolution
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.vecEmpty, Fin.val_zero, Fin.val_one]
  constructor <;> intro h n <;> simpa [add_comm] using h n

end CommSemiring

section CommRing

variable [CommRing R]

/-- The characteristic polynomial of `quadratic p q`. -/
theorem quadratic_charPoly (p q : R) :
    (quadratic p q).charPoly = Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X -
      Polynomial.C q := by
  unfold quadratic LinearRecurrence.charPoly
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecEmpty]
  simp [Polynomial.monomial_one_right_eq_X_pow, ← Polynomial.C_mul_X_eq_monomial]
  ring

/-- The characteristic quadratic factors when its two root data satisfy the
Vieta sum and product relations. -/
theorem quadratic_charPoly_eq_mul {p q β₁ β₂ : R} (hsum : β₁ + β₂ = p)
    (hprod : β₁ * β₂ = -q) :
    (quadratic p q).charPoly =
      (Polynomial.X - Polynomial.C β₁) * (Polynomial.X - Polynomial.C β₂) := by
  have hq : q = -(β₁ * β₂) := by
    calc
      q = -(-q) := by ring
      _ = -(β₁ * β₂) := by rw [hprod]
  rw [quadratic_charPoly, ← hsum, hq]
  simp only [map_add, map_neg, map_mul]
  ring

/-- The binary quadratic form associated to `quadratic p q`. -/
def quadraticForm (p q a b : R) : R :=
  a ^ 2 - p * a * b - q * b ^ 2

/-- One recurrence step multiplies the associated quadratic form by `-q`. -/
theorem quadratic_invariant_step {p q : R} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S) (k : ℕ) :
    quadraticForm p q (S (k + 2)) (S (k + 1)) =
      (-q) * quadraticForm p q (S (k + 1)) (S k) := by
  unfold quadraticForm
  rw [quadratic_isSolution_iff p q S |>.mp hS k]
  ring

/-- The quadratic form of a recurrence solution evolves geometrically. -/
theorem quadratic_invariant {p q : R} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S) (k : ℕ) :
    quadraticForm p q (S (k + 1)) (S k) =
      (-q) ^ k * quadraticForm p q (S 1) (S 0) := by
  induction k with
  | zero => simp [quadraticForm]
  | succ k ih =>
      rw [quadratic_invariant_step hS k, ih]
      ring

/-- A factor of the characteristic quadratic telescopes a solution without
dividing by the difference of its two roots. -/
theorem quadratic_telescope {p q β₁ β₂ : R} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S) (hsum : β₁ + β₂ = p)
    (hprod : β₁ * β₂ = -q) (k : ℕ) :
    S (k + 1) - β₁ * S k = β₂ ^ k * (S 1 - β₁ * S 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := quadratic_isSolution_iff p q S |>.mp hS k
      have hstep : S (k + 1 + 1) - β₁ * S (k + 1) =
          β₂ * (S (k + 1) - β₁ * S k) := by
        change S (k + 2) - β₁ * S (k + 1) = _
        rw [h]
        linear_combination (-(S (k + 1))) * hsum + (S k) * hprod
      calc
        S (k + 1 + 1) - β₁ * S (k + 1) = β₂ * (S (k + 1) - β₁ * S k) := hstep
        _ = β₂ * (β₂ ^ k * (S 1 - β₁ * S 0)) := by rw [ih]
        _ = β₂ ^ (k + 1) * (S 1 - β₁ * S 0) := by ring

end CommRing

end LinearRecurrence
