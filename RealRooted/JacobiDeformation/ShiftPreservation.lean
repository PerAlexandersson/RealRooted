import RealRooted.Hadamard.Grace
import RealRooted.JacobiDeformation.ShiftRecurrence

/-!
# Real polar-shift preservation

This module proves the real-parameter polar-derivative preservation needed to
iterate equation (25).  The proof uses the finite Pólya--Schur theorem with an
explicit Jensen-polynomial factorization, so repeated roots and every degree
boundary are included.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The globally nonnegative truncation of the real polar multiplier
`k ↦ a - k`. -/
def positivePolarMultiplier (a : ℝ) (k : ℕ) : ℝ :=
  max (a - k) 0

theorem positivePolarMultiplier_nonneg (a : ℝ) (k : ℕ) :
    0 ≤ positivePolarMultiplier a k := by
  simp [positivePolarMultiplier]

theorem jensenPolynomial_positivePolarMultiplier {n : ℕ} (hn : 1 ≤ n)
    {a : ℝ} (ha : (n : ℝ) < a) :
    jensenPolynomial n (positivePolarMultiplier a) =
      (X + 1) ^ (n - 1) * (C (a - n) * X + C a) := by
  have hsame :
      jensenPolynomial n (positivePolarMultiplier a) =
        jensenPolynomial n (fun k => a - (k : ℝ)) := by
    ext k
    rw [coeff_jensenPolynomial, coeff_jensenPolynomial]
    by_cases hk : k ≤ n
    · have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
      have hak : 0 ≤ a - (k : ℝ) := by linarith
      simp only [hk, ↓reduceIte]
      rw [positivePolarMultiplier, max_eq_left hak]
    · simp [hk]
  rw [hsame, jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  have hdiag (p : ℝ[X]) :
      diagonalOperator (fun k => a - (k : ℝ)) p = C a * p - theta p := by
    ext k
    simp [coeff_theta]
    ring
  rw [hdiag]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, theta, derivative_pow,
    derivative_add, derivative_X, derivative_one, add_zero, mul_one,
    Nat.cast_add, Nat.cast_one]
  simp only [map_add, map_sub, map_one, map_natCast]
  ring

/-- The real polar multiplier preserves the PF cone through every degree
strictly below `a`. -/
theorem positivePolarMultiplier_isFinitePFMultiplierSequence (n : ℕ)
    {a : ℝ} (ha : (n : ℝ) < a) :
    IsFinitePFMultiplierSequence n (positivePolarMultiplier a) := by
  have hnonneg : ∀ k, 0 ≤ positivePolarMultiplier a k :=
    positivePolarMultiplier_nonneg a
  cases n with
  | zero =>
      intro p hp hpdeg
      exact isFinitePFMultiplierSequence_natDegree_zero
        (gamma := positivePolarMultiplier a) hnonneg hp hpdeg
  | succ n =>
      have hcoef : 0 < a - ((n + 1 : ℕ) : ℝ) := sub_pos.mpr ha
      have hn0 : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
      have ha0 : 0 ≤ a := by linarith
      have hlin :
          (C (a - ((n + 1 : ℕ) : ℝ)) * X + C a : ℝ[X]) =
            C (a - ((n + 1 : ℕ) : ℝ)) *
              (X + C (a / (a - ((n + 1 : ℕ) : ℝ)))) := by
        rw [mul_add, ← C_mul]
        congr 1
        field_simp [hcoef.ne']
      have hjensen :
          IsPFPolynomial
            (jensenPolynomial (n + 1) (positivePolarMultiplier a)) := by
        rw [jensenPolynomial_positivePolarMultiplier (by lia) ha, hlin]
        exact (isPFPolynomial_X_add_one.pow n).mul
          ((isPFPolynomial_X_add_C (div_nonneg ha0 hcoef.le)).const_mul hcoef)
      intro p hp hpdeg
      exact isFinitePFMultiplierSequence_of_finiteMultiplierSequence
        (n := n + 1) (gamma := positivePolarMultiplier a) hnonneg
        ((finitePolyaSchur_nonneg hnonneg).2 hjensen) hp hpdeg

/-- On a degree box below `a`, the positive polar multiplier realizes the
real polar derivative `a p - X p'`. -/
theorem diagonalOperator_positivePolarMultiplier_eq {n : ℕ} {a : ℝ}
    (ha : (n : ℝ) < a) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    diagonalOperator (positivePolarMultiplier a) p = C a * p - theta p := by
  ext k
  rw [coeff_diagonalOperator, coeff_sub, coeff_C_mul, coeff_theta]
  by_cases hk : k ≤ n
  · have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    rw [positivePolarMultiplier, max_eq_left (by linarith)]
    ring
  · have hpcoeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (lt_of_not_ge hk))
    rw [hpcoeff]
    ring

/-- A real polar derivative preserves the PF cone when its scalar parameter
strictly exceeds the polynomial's degree bound. -/
theorem isPFPolynomial_C_mul_sub_theta {n : ℕ} {a : ℝ}
    (ha : (n : ℝ) < a) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (C a * p - theta p) := by
  rw [← diagonalOperator_positivePolarMultiplier_eq ha hpdeg]
  exact positivePolarMultiplier_isFinitePFMultiplierSequence n ha hp hpdeg

namespace JacobiDeformation

/-- Equation (25) transports the PF property across one unit parameter shift
whenever its scalar denominator is positive. -/
theorem isPFPolynomial_polynomial_shift {m : ℕ} {δ c d U V : ℝ}
    (hb : 0 < (m : ℝ) + c + d - 1 + δ)
    (hp : IsPFPolynomial (polynomial m δ c d U V)) :
    IsPFPolynomial (polynomial m (δ + 1) c d U V) := by
  rw [polynomial_shift m δ c d U V hb.ne']
  have ha : (m : ℝ) < (m : ℝ) + c + d - 1 + δ + m := by
    linarith
  have hpolar : IsPFPolynomial
      (C ((m : ℝ) + c + d - 1 + δ + m) * polynomial m δ c d U V -
        theta (polynomial m δ c d U V)) :=
    isPFPolynomial_C_mul_sub_theta ha hp
      (natDegree_polynomial_le m δ c d U V)
  simpa [theta] using hpolar.const_mul (inv_pos.mpr hb)

end JacobiDeformation
end RealRooted
