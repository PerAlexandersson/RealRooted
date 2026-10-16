module

public import RealRooted.GeneralizedEulerian

/-!
# Linear-factor lifts of Eulerian polynomials

Multiplying the `n`th Eulerian polynomial by a power of `1 + X` gives a reusable family
whose degree can grow by two at each step while splitting is immediate from its factors.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted

/-- The `n`th ordinary Eulerian polynomial, multiplied by `(1 + X) ^ (n + e)`. -/
def poweredEulerian (e n : ℕ) : ℝ[X] :=
  (1 + X) ^ (n + e) * generalizedEulerian 1 n

/-- Differential recurrence for the linear-factor lift of Eulerian polynomials. -/
theorem poweredEulerian_succ (e n : ℕ) :
    poweredEulerian e (n + 1) =
      (X - X ^ 3) * (poweredEulerian e n).derivative +
        (C 1 + C (2 - (e : ℝ)) * X +
          C (2 * (n : ℝ) + (e : ℝ) + 1) * X ^ 2) * poweredEulerian e n := by
  have hpow :
      ((1 + X) ^ (n + e)).derivative * (1 + X) =
        C ((n + e : ℕ) : ℝ) * (1 + X) ^ (n + e) := by
    rw [Polynomial.derivative_pow]
    simp only [Polynomial.derivative_add, Polynomial.derivative_one,
      Polynomial.derivative_X, zero_add, mul_one]
    by_cases hne : n + e = 0
    · simp only [hne, Nat.cast_zero, map_zero, zero_mul]
    · have hpos : 1 ≤ n + e := Nat.one_le_iff_ne_zero.mpr hne
      rw [show (1 + X) ^ (n + e) = (1 + X) ^ (n + e - 1) * (1 + X) by
        rw [← pow_succ, Nat.sub_add_cancel hpos]]
      ring
  rw [poweredEulerian, poweredEulerian, generalizedEulerian_succ]
  rw [show n + 1 + e = (n + e) + 1 by lia, pow_succ]
  rw [show (X : ℝ[X]) - X ^ 3 =
    X * ((1 : ℝ[X]) - X) * ((1 : ℝ[X]) + X) by ring]
  rw [Polynomial.derivative_mul]
  simp only [map_one]
  simp only [Nat.cast_add] at hpow ⊢
  simp only [map_add, map_sub, map_mul, map_one, map_ofNat] at hpow ⊢
  linear_combination
    -X * ((1 : ℝ[X]) - X) * generalizedEulerian 1 n * hpow

/-- Every linear-factor lift of an ordinary Eulerian polynomial is split. -/
theorem poweredEulerian_splits (e n : ℕ) : (poweredEulerian e n).Splits := by
  have hlinear : (1 + X : ℝ[X]).Splits := by
    simpa [add_comm] using Polynomial.Splits.X_add_C (1 : ℝ)
  exact (hlinear.pow (n + e)).mul (generalizedEulerian_splits (by norm_num) n)

end RealRooted
