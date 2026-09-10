import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJOutput
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize

/-!
# Bilinear BFJ output assembly

This file assembles the monomial BFJ formula over two bounded-degree
polynomials and records its shifted-binomial coefficient identity.
-/

open Polynomial

namespace MvPolynomial

noncomputable section

/-- Applying the shifted-binomial coefficient functional to the BFJ output of
two bounded homogenizations multiplies the corresponding input functionals. -/
theorem sum_coeff_mul_shifted_choose_bfjOutput_homogenize
    {R : Type*} [CommSemiring R] {p q : R[X]} {a b : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) (t : ℕ) :
    (∑ i ∈ Finset.range (a + b + 1),
      (bfjOutput (p.homogenize a) (q.homogenize b) b).coeff i *
        (Nat.choose (t + a + b - i) (a + b) : R)) =
      (∑ k ∈ Finset.range (a + 1), p.coeff k *
        (Nat.choose (t + a - k) a : R)) *
      ∑ l ∈ Finset.range (b + 1), q.coeff l *
        (Nat.choose (t + b - l) b : R) := by
  let L : R[X] →ₗ[R] R :=
    Polynomial.lsum fun i =>
      (Nat.choose (t + a + b - i) (a + b) : R) • LinearMap.id
  have hL_C_mul_X_pow (c : R) (i : ℕ) :
      L (Polynomial.C c * Polynomial.X ^ i) =
        c * (Nat.choose (t + a + b - i) (a + b) : R) := by
    change (Polynomial.C c * Polynomial.X ^ i).sum (fun j d =>
      (Nat.choose (t + a + b - j) (a + b) : R) * d) = _
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_index]
    · exact mul_comm _ _
    · simp
  have hL_range (r : R[X]) (hr : r.natDegree ≤ a + b) :
      L r = ∑ i ∈ Finset.range (a + b + 1), r.coeff i *
        (Nat.choose (t + a + b - i) (a + b) : R) := by
    change r.sum (fun i c =>
      (Nat.choose (t + a + b - i) (a + b) : R) * c) = _
    rw [Polynomial.sum_over_range' r (fun _ => by simp) (a + b + 1) (by lia)]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [← hL_range _
    (natDegree_bfjOutput_le (Polynomial.isHomogeneous_homogenize p)
      (Polynomial.isHomogeneous_homogenize q))]
  rw [Polynomial.homogenize_eq_sum_range_C_mul_X_pow hp,
    Polynomial.homogenize_eq_sum_range_C_mul_X_pow hq,
    bfjOutput_finsetSum_left]
  simp_rw [bfjOutput_C_mul_left, bfjOutput_finsetSum_right,
    bfjOutput_C_mul_right]
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.C_mul', map_smul, map_sum]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Polynomial.C_mul', map_smul]
  simp only [smul_eq_mul]
  have hmono :
      L (bfjOutput
          (X (0 : Fin 2) ^ k * X 1 ^ (a - k))
          (X (0 : Fin 2) ^ l * X 1 ^ (b - l)) b) =
        (Nat.choose (t + a - k) a : R) *
          (Nat.choose (t + b - l) b : R) := by
    rw [bfjOutput_monomial_monomial_guarded a b k l
      (by simpa using hk) (by simpa using hl)]
    rw [map_sum]
    simp_rw [← Polynomial.C_eq_natCast, ← Polynomial.C_mul,
      hL_C_mul_X_pow]
    have hn := (Nat.shifted_choose_mul_eq_sum a b k l t
      (by simpa using hk) (by simpa using hl)).symm
    simpa only [map_sum, map_mul, map_natCast, Nat.coe_castRingHom] using
      congrArg (Nat.castRingHom R) hn
  rw [hmono]
  ac_rfl

end

end MvPolynomial
