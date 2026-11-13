module

import RealRooted.MaWang.PersistentZero
import RealRooted.Tactic.Row.Frontend
import RealRooted.LiuWang.FiniteFamily
import RealRooted.WagnerX.AffineFactors
import RealRooted.Linear
public import RealRooted.Basic.ProperPosition

/-!
# A derivative--lag OEIS row

This file proves real-rootedness and the nonexceptional consecutive interlacing for A271697.
The row at index one is zero, so the interlacing chain starts at index two.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined A271697 row family. -/
def A271697 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      (X - X ^ 2) * (A271697 (n + 1)).derivative +
        C (1 + (n : ℝ)) * X * A271697 (n + 1) +
          C (1 + (n : ℝ)) * X * A271697 n

/-- The defining derivative--lag recurrence for A271697. -/
theorem A271697_add_two (n : ℕ) :
    A271697 (n + 2) =
      C (1 + (n : ℝ)) * X * A271697 (n + 1) +
        (X - X ^ 2) * (A271697 (n + 1)).derivative +
          C (1 + (n : ℝ)) * X * A271697 n := by
  rw [A271697]
  ring_nf

/-- The degree of A271697, including its exceptional zero row. -/
theorem A271697_natDegree (n : ℕ) : (A271697 n).natDegree = n - 1 := by
  rr_row_natDegree

/-- Consecutive A271697 rows strictly interlace from row two onward. -/
theorem A271697_strictInterl_add_two (m : ℕ) :
    StrictInterl (A271697 (m + 2)) (A271697 (m + 3)) := by
  rr_row_strictInterl

/-- Consecutive A271697 rows interlace from row two onward. -/
theorem A271697_interlaces_add_two (n : ℕ) :
    Interlaces (A271697 (n + 2)) (A271697 (n + 3)) :=
  (A271697_strictInterl_add_two n).toInterlaces (by
    rw [A271697_natDegree, A271697_natDegree]
    lia)

/-- Every A271697 row splits over the reals; row one is the zero polynomial. -/
theorem A271697_splits (n : ℕ) : (A271697 n).Splits := by
  rr_row_splits

/-- Multiplication by `X` conjugates the A271697 current to scalar
multiplier `1 + n X`, with unchanged lag multiplier. -/
theorem a271697_quotient_step (n : ℕ) (p q : ℝ[X]) :
    (X - X ^ 2) * (X * q).derivative + C ((n : ℝ) + 1) * X * (X * q) +
      C ((n : ℝ) + 1) * X * (X * p) =
    X * ((X - X ^ 2) * q.derivative + (1 + C (n : ℝ) * X) * q +
      C ((n : ℝ) + 1) * X * p) := by
  have h := PersistentZero.weylLag_mul_X_pow 1 (C ((n : ℝ) + 1) * X) (1 - X)
    (C ((n : ℝ) + 1) * X) p q
  simp only [pow_one, Nat.cast_one, C_1, one_mul] at h
  calc
    _ = C ((n : ℝ) + 1) * X * (X * q) + X * (1 - X) * (X * q).derivative +
        C ((n : ℝ) + 1) * X * (X * p) := by ring
    _ = X * (((C ((n : ℝ) + 1) * X + (1 - X)) * q +
        X * (1 - X) * q.derivative) + C ((n : ℝ) + 1) * X * p) := h
    _ = _ := by rw [C_add, C_1]; ring

/-- The A271697 and A046739 recurrences propagate the tail factorization
`P (n + 4) = X * Q n` from two consecutive seed identities. -/
theorem a271697_tail_eq {P Q : ℕ → ℝ[X]}
    (hP : ∀ n, P (n + 2) = (X - X ^ 2) * (P (n + 1)).derivative +
      C ((n : ℝ) + 1) * X * P (n + 1) + C ((n : ℝ) + 1) * X * P n)
    (hQ : ∀ n, Q (n + 2) = (X - X ^ 2) * (Q (n + 1)).derivative +
      (1 + C ((n : ℝ) + 4) * X) * Q (n + 1) + C ((n : ℝ) + 5) * X * Q n)
    (h0 : P 4 = X * Q 0) (h1 : P 5 = X * Q 1) :
    ∀ n, P (n + 4) = X * Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
      calc
        P (n + 2 + 4) = P (n + 4 + 2) := by rfl
        _ = (X - X ^ 2) * (P (n + 4 + 1)).derivative +
            C ((n + 4 : ℕ) + 1 : ℝ) * X * P (n + 4 + 1) +
            C ((n + 4 : ℕ) + 1 : ℝ) * X * P (n + 4) := hP (n + 4)
        _ = (X - X ^ 2) * (X * Q (n + 1)).derivative +
            C ((n + 4 : ℕ) + 1 : ℝ) * X * (X * Q (n + 1)) +
            C ((n + 4 : ℕ) + 1 : ℝ) * X * (X * Q n) := by
          rw [show n + 4 + 1 = n + 1 + 4 by lia, ih1, ih0]
        _ = X * ((X - X ^ 2) * (Q (n + 1)).derivative +
            (1 + C ((n + 4 : ℕ) : ℝ) * X) * Q (n + 1) +
            C ((n + 4 : ℕ) + 1 : ℝ) * X * Q n) :=
          a271697_quotient_step (n + 4) (Q n) (Q (n + 1))
        _ = X * Q (n + 2) := by rw [hQ n]; push_cast; ring

/-- The A271697 seeds `1, 0` and the A046739 seed polynomials give
the factorization `P (n + 4) = X * Q n`. -/
theorem a271697_eq_X_mul_of_recurrence {P Q : ℕ → ℝ[X]}
    (hP0 : P 0 = 1) (hP1 : P 1 = 0)
    (hQ0 : Q 0 = 1 + C 7 * X + X ^ 2)
    (hQ1 : Q 1 = 1 + C 21 * X + C 21 * X ^ 2 + X ^ 3)
    (hP : ∀ n, P (n + 2) = (X - X ^ 2) * (P (n + 1)).derivative +
      C ((n : ℝ) + 1) * X * P (n + 1) + C ((n : ℝ) + 1) * X * P n)
    (hQ : ∀ n, Q (n + 2) = (X - X ^ 2) * (Q (n + 1)).derivative +
      (1 + C ((n : ℝ) + 4) * X) * Q (n + 1) + C ((n : ℝ) + 5) * X * Q n) :
    ∀ n, P (n + 4) = X * Q n := by
  have hP2 : P 2 = X := by simpa [hP0, hP1] using hP 0
  have hP3 : P 3 = X + X ^ 2 := by
    rw [hP 1, hP2, hP1]
    norm_num [C_ofNat]
    ring
  have hP4 : P 4 = X + C 7 * X ^ 2 + X ^ 3 := by
    rw [hP 2, hP3, hP2]
    norm_num [derivative_X_pow, C_ofNat]
    ring
  apply a271697_tail_eq hP hQ
  · rw [hP4, hQ0]
    ring
  · rw [hP 3, hP4, hP3, hQ1]
    norm_num [derivative_X_pow, C_ofNat]
    ring

/-- A common `X` factor transports consecutive quotient interlacing
to the A271697 tail. -/
theorem a271697_tail_interl {P Q : ℕ → ℝ[X]}
    (hfactor : ∀ n, P (n + 4) = X * Q n)
    (hinterl : ∀ n, Interl (Q n) (Q (n + 1))) (n : ℕ) :
    Interl (P (n + 4)) (P (n + 5)) := by
  rw [show n + 5 = (n + 1) + 4 by lia, hfactor n, hfactor (n + 1)]
  simpa only [pow_one] using PersistentZero.interl_mul_X_pow (hinterl n) 1

end RealRooted.Applications.OEIS
