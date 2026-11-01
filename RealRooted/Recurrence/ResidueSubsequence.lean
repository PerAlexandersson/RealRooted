module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Residue subsequences of constant-coefficient recurrences

A sequence satisfying `P (n + 2) = a * P (n + 1) + b * P n` also satisfies
`P (n + 4) = (a ^ 2 + 2 * b) * P (n + 2) - b ^ 2 * P n`, so its even and odd
subsequences obey the same induced second-order recurrence.  Likewise every fixed-residue
subsequence modulo three of a cubic recurrence satisfies the cubic recurrence with cubed
characteristic roots.  Residual identities give division-free certificates for both passages.
-/

public section

namespace RealRooted

/-- The residual of the recurrence
`P (n + 2) = a * P (n + 1) + b * P n`. -/
@[expose] def quadraticResidual {R : Type*} [Ring R]
    (a b : R) (P : ℕ → R) (n : ℕ) : R :=
  P (n + 2) - a * P (n + 1) - b * P n

/-- Three consecutive residuals combine to the residual of the recurrence
governing steps of size two. -/
theorem quadraticResidual_gap_two {R : Type*} [CommRing R]
    (a b : R) (P : ℕ → R) (n : ℕ) :
    P (n + 4) - (a ^ 2 + 2 * b) * P (n + 2) + b ^ 2 * P n =
      quadraticResidual a b P (n + 2) + a * quadraticResidual a b P (n + 1) -
        b * quadraticResidual a b P n := by
  simp only [quadraticResidual]
  ring

/-- Every solution of a constant-coefficient quadratic recurrence satisfies
the induced recurrence with step size two. -/
theorem quadraticRecurrence_gap_two {R : Type*} [CommRing R]
    (a b : R) (P : ℕ → R)
    (hrec : ∀ n, P (n + 2) = a * P (n + 1) + b * P n) (n : ℕ) :
    P (n + 4) = (a ^ 2 + 2 * b) * P (n + 2) - b ^ 2 * P n := by
  have hzero (m : ℕ) : quadraticResidual a b P m = 0 := by
    rw [quadraticResidual, hrec]
    ring
  have h := quadraticResidual_gap_two a b P n
  simp only [hzero, mul_zero, add_zero, sub_zero] at h
  linear_combination h

/-- Every fixed parity subsequence of a constant-coefficient quadratic recurrence
satisfies the induced quadratic recurrence. -/
theorem quadraticRecurrence_residue_two {R : Type*} [CommRing R]
    (a b : R) (P : ℕ → R)
    (hrec : ∀ n, P (n + 2) = a * P (n + 1) + b * P n) (j n : ℕ) :
    P (2 * (n + 2) + j) = (a ^ 2 + 2 * b) * P (2 * (n + 1) + j) -
      b ^ 2 * P (2 * n + j) := by
  convert quadraticRecurrence_gap_two a b P hrec (2 * n + j) using 1 <;>
    congr 1 <;> lia


/-- The residual of the cubic recurrence
`H (n + 3) = p H (n + 2) - q H (n + 1) + u H n`. -/
@[expose] def cubicResidual {R : Type*} [Ring R]
    (p q u : R) (H : ℕ → R) (n : ℕ) : R :=
  H (n + 3) - p * H (n + 2) + q * H (n + 1) - u * H n

/-- Explicit factor certificate for replacing a cubic characteristic polynomial
by the characteristic polynomial governing every-third subsequences. -/
theorem cubicCharacteristic_mul_certificate {R : Type*} [CommRing R]
    (p q u z : R) :
    (z ^ 3 - p * z ^ 2 + q * z - u) *
        (z ^ 6 + p * z ^ 5 + (p ^ 2 - q) * z ^ 4 + (p * q - 2 * u) * z ^ 3 +
          (q ^ 2 - p * u) * z ^ 2 + q * u * z + u ^ 2) =
      z ^ 9 - (p ^ 3 - 3 * p * q + 3 * u) * z ^ 6 +
        (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * z ^ 3 - u ^ 3 := by
  ring

/-- The seven shifted cubic residuals combine to the residual of the
every-third recurrence. -/
theorem cubicResidual_gap_three {R : Type*} [CommRing R]
    (p q u : R) (H : ℕ → R) (m : ℕ) :
    H (m + 9) - (p ^ 3 - 3 * p * q + 3 * u) * H (m + 6) +
          (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * H (m + 3) - u ^ 3 * H m =
      cubicResidual p q u H (m + 6) + p * cubicResidual p q u H (m + 5) +
        (p ^ 2 - q) * cubicResidual p q u H (m + 4) +
        (p * q - 2 * u) * cubicResidual p q u H (m + 3) +
        (q ^ 2 - p * u) * cubicResidual p q u H (m + 2) +
        q * u * cubicResidual p q u H (m + 1) + u ^ 2 * cubicResidual p q u H m := by
  simp only [cubicResidual]
  ring

/-- Every solution of a cubic recurrence satisfies the induced gap-three recurrence. -/
theorem cubicRecurrence_gap_three {R : Type*} [CommRing R]
    (p q u : R) (H : ℕ → R)
    (hrec : ∀ n, H (n + 3) = p * H (n + 2) - q * H (n + 1) + u * H n)
    (m : ℕ) :
    H (m + 9) = (p ^ 3 - 3 * p * q + 3 * u) * H (m + 6) -
      (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * H (m + 3) + u ^ 3 * H m := by
  have hzero (n : ℕ) : cubicResidual p q u H n = 0 := by
    rw [cubicResidual, hrec]
    ring
  have h := cubicResidual_gap_three p q u H m
  simp only [hzero, mul_zero, add_zero] at h
  linear_combination h

/-- Each fixed-residue subsequence of a cubic recurrence satisfies the same
cubic recurrence with the cubed characteristic roots. -/
theorem cubicRecurrence_residue_three {R : Type*} [CommRing R]
    (p q u : R) (H : ℕ → R)
    (hrec : ∀ n, H (n + 3) = p * H (n + 2) - q * H (n + 1) + u * H n)
    (j n : ℕ) :
    H (3 * (n + 3) + j) =
      (p ^ 3 - 3 * p * q + 3 * u) * H (3 * (n + 2) + j) -
      (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * H (3 * (n + 1) + j) +
      u ^ 3 * H (3 * n + j) := by
  convert cubicRecurrence_gap_three p q u H hrec (3 * n + j) using 1 <;> congr 1 <;> lia

end RealRooted
