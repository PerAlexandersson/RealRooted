/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentSeries
public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentChristoffel
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentShift

/-!
# Finite Euler–Gauss steps and their termination

These identities use only one Christoffel polynomial identity and its
displayed nonzero denominator norms. At the boundary, a vanishing polynomial
pairing gives equality of the last two formal series instead of requiring
division by the zero next norm.
-/

public section

namespace Polynomial

/-- Initial Euler–Gauss equation, requiring only the first two nonzero moments. -/
theorem momentOrthogonalSeries_zero_sub_one_of_ne_zero
    (μ : ℕ → ℝ) (hm0 : μ 0 ≠ 0) (hm1 : μ 1 ≠ 0) :
    momentOrthogonalSeries μ 0 - 1 =
      PowerSeries.C (momentStieltjesEven μ 0) * PowerSeries.X *
        momentOrthogonalSeries (fun k => μ (k + 1)) 0 := by
  ext k
  cases k with
  | zero =>
      simp only [map_sub, coeff_momentOrthogonalSeries_zero, PowerSeries.coeff_zero_one,
        div_self hm0, sub_self, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_zero_X_mul, mul_zero]
  | succ k =>
      simp only [map_sub, PowerSeries.coeff_one, Nat.add_one_ne_zero, ite_false,
        sub_zero, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        coeff_momentOrthogonalSeries_zero, momentStieltjesEven, momentNormSq_zero,
        Nat.zero_add]
      field_simp [hm0, hm1]

/-- An odd Euler–Gauss step from one Christoffel identity and finite nondegeneracy. -/
theorem momentOrthogonalSeries_shift_sub_of_identity (μ : ℕ → ℝ) (n : ℕ)
    (hpoly : X * monicMomentPolynomial (fun k => μ (k + 1)) n =
      monicMomentPolynomial μ (n + 1) +
        C (momentStieltjesEven μ n) * monicMomentPolynomial μ n)
    (hdet : IsUnit (momentHankelMatrix μ (n + 1)).det)
    (hA : momentNormSq μ n ≠ 0)
    (hB : momentNormSq (fun k => μ (k + 1)) n ≠ 0)
    (hC : momentNormSq μ (n + 1) ≠ 0) :
    momentOrthogonalSeries (fun k => μ (k + 1)) n - momentOrthogonalSeries μ n =
      PowerSeries.C (momentStieltjesOdd μ n) * PowerSeries.X *
        momentOrthogonalSeries μ (n + 1) := by
  have hp (k : ℕ) := congrArg (momentPairing μ (X ^ (n + k))) hpoly
  simp only [momentPairing_add_right, momentPairing_C_mul_right,
    ← momentPairing_shift] at hp
  ext k
  cases k with
  | zero =>
      have hz : momentPairing μ (X ^ n) (monicMomentPolynomial μ (n + 1)) = 0 :=
        momentPairing_X_pow_monicMomentPolynomial μ (n + 1) hdet ⟨n, by lia⟩
      simp only [map_sub, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_zero_X_mul, mul_zero, coeff_momentOrthogonalSeries]
      rw [hp 0]
      simp only [Nat.add_zero, hz, zero_add, momentStieltjesEven]
      field_simp [hA, hB]
      ring
  | succ k =>
      simp only [map_sub, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, coeff_momentOrthogonalSeries]
      rw [show n + 1 + k = n + (k + 1) by lia, hp (k + 1),
        momentStieltjesEven, momentStieltjesOdd]
      field_simp [hA, hB, hC]
      ring

/-- An even Euler–Gauss step from the second Christoffel identity. -/
theorem momentOrthogonalSeries_succ_sub_of_identity (μ : ℕ → ℝ) (n : ℕ)
    (hpoly : monicMomentPolynomial μ (n + 1) =
      monicMomentPolynomial (fun k => μ (k + 1)) (n + 1) +
        C (momentStieltjesOdd μ n) * monicMomentPolynomial (fun k => μ (k + 1)) n)
    (hdet : IsUnit (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det)
    (hA : momentNormSq μ (n + 1) ≠ 0)
    (hB : momentNormSq (fun k => μ (k + 1)) n ≠ 0)
    (hC : momentNormSq (fun k => μ (k + 1)) (n + 1) ≠ 0) :
    momentOrthogonalSeries μ (n + 1) - momentOrthogonalSeries (fun k => μ (k + 1)) n =
      PowerSeries.C (momentStieltjesEven μ (n + 1)) * PowerSeries.X *
        momentOrthogonalSeries (fun k => μ (k + 1)) (n + 1) := by
  have hp (k : ℕ) :
      momentPairing μ (X ^ ((n + 1) + k)) (monicMomentPolynomial μ (n + 1)) =
      momentPairing (fun j => μ (j + 1)) (X ^ (n + k))
          (monicMomentPolynomial (fun j => μ (j + 1)) (n + 1)) +
        momentStieltjesOdd μ n *
          momentPairing (fun j => μ (j + 1)) (X ^ (n + k))
            (monicMomentPolynomial (fun j => μ (j + 1)) n) := by
    have h := congrArg (momentPairing (fun j => μ (j + 1)) (X ^ (n + k))) hpoly
    rw [momentPairing_add_right, momentPairing_C_mul_right,
      momentPairing_shift_X_pow] at h
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  ext k
  cases k with
  | zero =>
      have hz : momentPairing (fun j => μ (j + 1)) (X ^ n)
          (monicMomentPolynomial (fun j => μ (j + 1)) (n + 1)) = 0 :=
        momentPairing_X_pow_monicMomentPolynomial _ (n + 1) hdet ⟨n, by lia⟩
      simp only [map_sub, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_zero_X_mul, mul_zero, coeff_momentOrthogonalSeries]
      rw [hp 0]
      simp only [Nat.add_zero, hz, zero_add, momentStieltjesOdd]
      field_simp [hA, hB]
      ring
  | succ k =>
      simp only [map_sub, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, coeff_momentOrthogonalSeries]
      rw [hp (k + 1), momentStieltjesOdd, momentStieltjesEven,
        show n + 1 + k = n + (k + 1) by lia]
      field_simp [hA, hB, hC]
      ring

/-- At the odd terminating position, vanishing of every pairing with the next
unshifted polynomial makes the two normalized moment series equal. -/
theorem momentOrthogonalSeries_shift_eq_of_pairing_zero (μ : ℕ → ℝ) (n : ℕ)
    (hpoly : X * monicMomentPolynomial (fun k => μ (k + 1)) n =
      monicMomentPolynomial μ (n + 1) +
        C (momentStieltjesEven μ n) * monicMomentPolynomial μ n)
    (hzero : ∀ p : ℝ[X], momentPairing μ p (monicMomentPolynomial μ (n + 1)) = 0)
    (hA : momentNormSq μ n ≠ 0)
    (hB : momentNormSq (fun k => μ (k + 1)) n ≠ 0) :
    momentOrthogonalSeries (fun k => μ (k + 1)) n = momentOrthogonalSeries μ n := by
  ext k
  have h := congrArg (momentPairing μ (X ^ (n + k))) hpoly
  rw [momentPairing_add_right, momentPairing_C_mul_right,
    ← momentPairing_shift, hzero, zero_add] at h
  rw [coeff_momentOrthogonalSeries, coeff_momentOrthogonalSeries, h,
    momentStieltjesEven]
  field_simp [hA, hB]

/-- At the even terminating position, vanishing of every shifted pairing with
the next shifted polynomial makes the last two series equal. -/
theorem momentOrthogonalSeries_succ_eq_of_pairing_zero (μ : ℕ → ℝ) (n : ℕ)
    (hpoly : monicMomentPolynomial μ (n + 1) =
      monicMomentPolynomial (fun k => μ (k + 1)) (n + 1) +
        C (momentStieltjesOdd μ n) * monicMomentPolynomial (fun k => μ (k + 1)) n)
    (hzero : ∀ p : ℝ[X], momentPairing (fun k => μ (k + 1)) p
      (monicMomentPolynomial (fun k => μ (k + 1)) (n + 1)) = 0)
    (hA : momentNormSq μ (n + 1) ≠ 0)
    (hB : momentNormSq (fun k => μ (k + 1)) n ≠ 0) :
    momentOrthogonalSeries μ (n + 1) =
      momentOrthogonalSeries (fun k => μ (k + 1)) n := by
  ext k
  have h := congrArg (momentPairing (fun j => μ (j + 1)) (X ^ (n + k))) hpoly
  rw [momentPairing_add_right, momentPairing_C_mul_right, hzero, zero_add,
    momentPairing_shift_X_pow] at h
  rw [coeff_momentOrthogonalSeries, coeff_momentOrthogonalSeries,
    show n + 1 + k = n + k + 1 by lia, h, momentStieltjesOdd]
  field_simp [hA, hB]

end Polynomial
