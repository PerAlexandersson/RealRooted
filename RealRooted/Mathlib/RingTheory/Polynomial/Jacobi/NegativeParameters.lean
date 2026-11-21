/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.Multiplicity
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.Solutions
import Mathlib.Tactic

/-!
# Two negative integer Jacobi parameters

The exact endpoint factorization follows by conjugating the differential equation
and comparing the highest coefficient. Source: unpublished proof notes in the
comment on RealRooted issue #2341, Proposition 7.
-/

public section

namespace Polynomial

/-- The two-endpoint factor solves the original Jacobi equation. -/
private theorem jacobi_equation_endpoint_factor
    (n p q : ℕ) (hs : p + q ≤ n) :
    jacobiDifferentialOperator (-(p : ℝ) + 1) (-(p : ℝ) + -(q : ℝ) + 2)
        (X ^ p * ((1 - X) ^ q * shiftedJacobi (n - (p + q)) p q)) +
      C (n * (n + -(p : ℝ) + -(q : ℝ) + 1)) *
        (X ^ p * ((1 - X) ^ q * shiftedJacobi (n - (p + q)) p q)) = 0 := by
  let N := n - (p + q)
  have hN : (N : ℝ) = n - p - q := by
    dsimp [N]
    rw [Nat.cast_sub hs, Nat.cast_add]
    ring
  have hleft := jacobiDifferentialOperator_X_pow_mul p (-(p : ℝ) + -(q : ℝ) + 2)
    (n * (n + -(p : ℝ) + -(q : ℝ) + 1))
    ((1 - X) ^ q * shiftedJacobi N p q)
  have hright := jacobiDifferentialOperator_one_sub_X_pow_mul q ((p : ℝ) + 1)
    (n * (n + -(p : ℝ) + -(q : ℝ) + 1) -
      p * (p + (-(p : ℝ) + -(q : ℝ) + 2) - 1))
    (shiftedJacobi N p q)
  have hc : -(p : ℝ) + -(q : ℝ) + 2 + 2 * p = (p : ℝ) + 1 - q + 1 := by ring
  have hc' : (p : ℝ) + 1 + q + 1 = (p : ℝ) + q + 2 := by ring
  have hD : n * (n + -(p : ℝ) + -(q : ℝ) + 1) -
      p * (p + (-(p : ℝ) + -(q : ℝ) + 2) - 1) - q * ((p : ℝ) + 1) =
        N * (N + (p : ℝ) + q + 1) := by rw [hN]; ring
  rw [show -(p : ℝ) + 1 = 1 - (p : ℝ) by ring, hleft, hc, hright, hc', hD]
  have hode : jacobiDifferentialOperator ((p : ℝ) + 1) ((p : ℝ) + q + 2)
      (shiftedJacobi N p q) + C (N * (N + (p : ℝ) + q + 1)) *
        shiftedJacobi N p q = 0 := by
    simpa only [jacobiDifferentialOperator] using shiftedJacobi_differential_equation N p q
  rw [hode, mul_zero, mul_zero]

/-- Highest coefficient of the normalized two-endpoint factor. -/
private theorem coeff_jacobi_endpoint_factor
    (n p q : ℕ) (hs : p + q ≤ n) :
    (C ((-1 : ℝ) ^ p) *
      (X ^ p * ((1 - X) ^ q * shiftedJacobi (n - (p + q)) p q))).coeff n =
        (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).coeff n := by
  let N := n - (p + q)
  have hsum : p + (q + N) = n := by dsimp [N]; lia
  have hN : (N : ℝ) = n - p - q := by
    dsimp [N]
    rw [Nat.cast_sub hs, Nat.cast_add]
    ring
  have hb : (1 - X : ℝ[X]) = -(X - C 1) := by simp
  have hbdeg : (1 - X : ℝ[X]).natDegree = 1 := by
    rw [hb, natDegree_neg, natDegree_X_sub_C]
  have hblc : (1 - X : ℝ[X]).leadingCoeff = -1 := by
    rw [hb, leadingCoeff_neg, leadingCoeff_X_sub_C]
  have hqdeg : ((1 - X : ℝ[X]) ^ q).natDegree = q := by
    rw [natDegree_pow, hbdeg, mul_one]
  have hqcoeff : ((1 - X : ℝ[X]) ^ q).coeff q = (-1 : ℝ) ^ q := by
    calc
      _ = ((1 - X : ℝ[X]) ^ q).leadingCoeff := by rw [leadingCoeff, hqdeg]
      _ = _ := by rw [leadingCoeff_pow, hblc]
  have hpoly :
      (X ^ p * ((1 - X) ^ q * shiftedJacobi N (p : ℝ) q)).coeff n =
        (-1 : ℝ) ^ q * (shiftedJacobi N (p : ℝ) q).coeff N := by
    rw [← hsum, coeff_mul_add_eq_of_natDegree_le
      (by simp) (natDegree_mul_le.trans (by
        have := natDegree_shiftedJacobi_le N (p : ℝ) q
        rw [hqdeg]
        lia)), coeff_X_pow_self, one_mul,
      coeff_mul_add_eq_of_natDegree_le hqdeg.le (natDegree_shiftedJacobi_le N (p : ℝ) q),
      hqcoeff]
  rw [coeff_C_mul, hpoly]
  simp only [coeff_shiftedJacobi, le_refl, ite_true, Nat.sub_self,
    Ring.choose_zero_right, mul_one]
  have htop0 : (N : ℝ) + p + q + N = ((n + N : ℕ) : ℝ) := by
    push_cast
    linarith
  have htop1 : (n : ℝ) + -(p : ℝ) + -(q : ℝ) + n = ((n + N : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [htop0, htop1, Ring.choose_natCast, Ring.choose_natCast, Nat.choose_symm_add]
  have hsign : (-1 : ℝ) ^ p * ((-1 : ℝ) ^ q * (-1 : ℝ) ^ N) = (-1 : ℝ) ^ n := by
    rw [← pow_add, ← pow_add, hsum]
  linear_combination (Nat.choose (n + N) N : ℝ) * hsign

/-- Exact two-negative-parameter endpoint factorization, including zero endpoint
exponents. When their sum exceeds `n`, use `shiftedJacobi_eq_zero_iff` instead. -/
theorem shiftedJacobi_neg_nat_neg_nat (n p q : ℕ) (hs : p + q ≤ n) :
    shiftedJacobi n (-(p : ℝ)) (-(q : ℝ)) =
      C ((-1 : ℝ) ^ p) *
        (X ^ p * ((1 - X) ^ q * shiftedJacobi (n - (p + q)) p q)) := by
  apply eq_of_jacobi_equation_of_coeff_eq n (-(p : ℝ)) (-(q : ℝ))
  · intro k
    have hs' : (p : ℝ) + q ≤ n := by exact_mod_cast hs
    have hk : (0 : ℝ) ≤ k := by positivity
    linarith
  · simpa only [jacobiDifferentialOperator] using
      shiftedJacobi_differential_equation n (-(p : ℝ)) (-(q : ℝ))
  · rw [jacobiDifferentialOperator_C_mul]
    have hode := jacobi_equation_endpoint_factor n p q hs
    linear_combination C ((-1 : ℝ) ^ p) * hode
  · exact (coeff_jacobi_endpoint_factor n p q hs).symm

end Polynomial
