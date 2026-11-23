module

public import RealRooted.Hermite.Generalized.Basic
public import RealRooted.MultiplierSequence

/-!
# A Jensen factorization of generalized Hermite polynomials

Reversing the finite exponential sum identifies its compressed polynomial
with the Jensen polynomial of an integer-stride Mittag--Leffler function.
All factorials refer to ordinary Taylor coefficients before the Jensen
binomial factors are inserted.
-/

public section

open Polynomial Finset

namespace RealRooted

/-- The two reversed parity factors coincide. -/
private theorem neg_one_pow_sub {q k : ℕ} (hk : k ≤ q) :
    (-1 : ℝ) ^ (q - k) = (-1 : ℝ) ^ q * (-1 : ℝ) ^ k := by
  have hq : (-1 : ℝ) ^ q = (-1 : ℝ) ^ (q - k) * (-1 : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hq, mul_assoc, ← mul_pow]
  norm_num

/-- The scalar coefficients agree after reversing the summation index. -/
private theorem generalizedHermite_jensen_scalar (p s q : ℕ) {k : ℕ} (hk : k ≤ q) :
    (-1 : ℝ) ^ (q - k) * (s + p * q).factorial /
        ((q - k).factorial * (s + p * k).factorial) =
      ((-1 : ℝ) ^ q * (s + p * q).factorial / q.factorial) *
        ((q.choose k : ℝ) * ((k.factorial : ℝ) / (s + p * k).factorial)) *
          (-1 : ℝ) ^ k := by
  rw [neg_one_pow_sub hk, Nat.cast_choose ℝ hk]
  field_simp

/-- Exact Jensen normalization, including degree zero and residue zero. -/
theorem generalizedHermite_eq_jensenPolynomial {p s : ℕ} (hs : s < p) (q : ℕ) :
    generalizedHermite p (s + p * q) =
      C ((-1 : ℝ) ^ q * (s + p * q).factorial / q.factorial) * X ^ s *
        (jensenPolynomial q (fun k ↦
          (k.factorial : ℝ) / (s + p * k).factorial)).comp (-X ^ p) := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le s) hs
  have hdiv : (s + p * q) / p = q := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hs, zero_add]
  rw [generalizedHermite_eq_sum, hdiv]
  conv_lhs => rw [← Finset.sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  simp only [jensenPolynomial, Polynomial.sum_comp, monomial_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsub : s + p * q - p * (q - k) = s + p * k := by
    have heq : p * q = p * (q - k) + p * k := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hk']
    lia
  rw [hsub, generalizedHermite_jensen_scalar p s q hk']
  have hneg : (-X ^ p : ℝ[X]) ^ k = C ((-1 : ℝ) ^ k) * X ^ (p * k) := by
    simp only [map_pow, map_neg, map_one, pow_mul]
    rw [← mul_pow]
    simp only [neg_one_mul]
  rw [hneg]
  simp only [map_mul, pow_add]
  ring

end RealRooted
