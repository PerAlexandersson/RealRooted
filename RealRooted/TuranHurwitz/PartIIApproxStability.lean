module

public import RealRooted.TuranHurwitz.PartIICoefficients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Nonvanishing of the finite Turán approximants

Factorial coefficient extraction turns the paired derivative coefficient
into the extended Turán expression of the real approximating rows.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- A polynomial exponential coefficient family has the expected derivative coefficients. -/
theorem coeff_iterate_derivative_of_factorial_coeff {P : ℕ → ℝ[X]} {f : ℂ[X]} {z : ℂ}
    (hP : ∀ j, Polynomial.aeval z (P j) = (j.factorial : ℂ) * f.coeff j)
    (m r : ℕ) :
    (derivative^[m] f).coeff r = Polynomial.aeval z (P (m + r)) / (r.factorial : ℂ) := by
  have hfac : (r.factorial : ℂ) * ((r + m).descFactorial m : ℂ) =
      ((m + r).factorial : ℂ) := by
    have h := Nat.factorial_mul_descFactorial (Nat.le_add_left m r)
    rw [Nat.add_sub_cancel_right, Nat.add_comm r m] at h
    exact_mod_cast (by simpa only [Nat.add_comm] using h :
      r.factorial * (r + m).descFactorial m = (m + r).factorial)
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero r)).mpr
  rw [coeff_iterate_derivative, nsmul_eq_mul, hP, ← hfac]
  rw [Nat.add_comm r m]
  ring

/-- Pairing the derivative with its reflection gives the signed Turán evaluation. -/
theorem coeff_paired_iterate_derivative {P : ℕ → ℝ[X]} {f : ℂ[X]} {z : ℂ}
    (hP : ∀ j, Polynomial.aeval z (P j) = (j.factorial : ℂ) * f.coeff j)
    (m n : ℕ) :
    let q := derivative^[m] f
    (q * q.comp (-X)).coeff (2 * n) =
      (-1 : ℂ) ^ n * Polynomial.aeval z (turan m n P) := by
  dsimp only
  rw [mul_comm (derivative^[m] f), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hreflect : (-X : ℂ[X]) = C (-1) * X := by simp
  simp only [hreflect, comp_C_mul_X_coeff, coeff_iterate_derivative_of_factorial_coeff hP]
  rw [turan, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ 2 * n := by simpa using Finset.mem_range.mp hj
  have hindex : m + (2 * n - j) = m + 2 * n - j := by lia
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (n + j) = (-1 : ℂ) ^ j := by
    have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
    rw [pow_add, ← mul_assoc, hs, one_mul]
  simp only [map_mul, Polynomial.aeval_C, map_div₀, map_pow, map_neg, map_one,
    map_mul, map_natCast]
  rw [hindex]
  simp only [div_eq_mul_inv, mul_inv_rev]
  linear_combination -hsign *
    ((j.factorial : ℂ)⁻¹ * ((2 * n - j).factorial : ℂ)⁻¹ *
      Polynomial.aeval z (P (m + j)) * Polynomial.aeval z (P (m + 2 * n - j)))

/-- The finite Turán approximants exclude the required open half-plane. -/
theorem aeval_turan_partIIApproxFamily_ne_zero {c : PartIIParameters} (hc : c.Admissible)
    {k : ℕ} (hk : 0 < k) (m n : ℕ) (hmn : m + n ≤ 2 * k) {z : ℂ}
    (hz : -c.lam < z.re) : Polynomial.aeval z (turan m n (partIIApproxFamily c k)) ≠ 0 := by
  obtain ⟨N, hN⟩ := hc.integer_shift
  have hx : 0 < (z + (c.lam : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hpair := paired_coeff_partIIApproxBase (div_pos hc.a₁_pos hc.sigma_pos)
    (div_pos hc.b₂_pos hc.sigma_pos) hc.ratio_pos (one_div_pos.mpr hc.sigma_pos) N hk hx hmn
  have hidentity := coeff_paired_iterate_derivative
    (fun j => aeval_partIIApproxFamily hc hN k j z) m n
  dsimp only at hpair hidentity
  rw [hidentity] at hpair
  exact (mul_ne_zero_iff.mp hpair).2

/-- Every finite Turán approximant stays in a degree box independent of `k`. -/
theorem natDegree_turan_partIIApproxFamily_le (c : PartIIParameters) (k m n : ℕ) :
    (turan m n (partIIApproxFamily c k)).natDegree ≤ 2 * m + 2 * n := by
  rw [turan]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ 2 * n := by simpa using Finset.mem_range.mp hj
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_mul_le.trans
  have h₁ := natDegree_partIIApproxFamily_le c k (m + j)
  have h₂ := natDegree_partIIApproxFamily_le c k (m + 2 * n - j)
  lia

end RealRooted.TuranHurwitz
