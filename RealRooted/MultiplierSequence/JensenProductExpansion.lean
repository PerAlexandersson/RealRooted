module

public import RealRooted.MultiplierSequence.JensenProduct
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Mathlib.Algebra.Polynomial.Chow

/-!
# Ordinary and reciprocal Jensen product expansions

The binomial convolution of Taylor sequences has an expansion in the Jensen
polynomials of either factor. Reflection gives the reciprocal expansion in
O'Sullivan, *Zeros of Jensen polynomials and asymptotics for the Riemann xi
function*, Proposition 3.4, https://arxiv.org/abs/2007.13582.
These finite identities require no analyticity or nonvanishing assumptions.
-/

public section

open Polynomial

namespace RealRooted

/-- The ordinary Jensen product expanded in the Jensen polynomials of the
second sequence. -/
theorem jensenProductPolynomial_eq_sum (d : ℕ) (gamma delta : ℕ → ℝ) :
    jensenProductPolynomial d gamma delta =
      ∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * gamma j) *
        (X ^ j * jensenPolynomial (d - j) delta) := by
  let B (j : ℕ) : ℝ[X] := C ((d.choose j : ℝ) * gamma j) *
    (X ^ j * jensenPolynomial (d - j) delta)
  ext k
  change (jensenProductPolynomial d gamma delta).coeff k =
    (∑ j ∈ Finset.range (d + 1), B j).coeff k
  rw [finsetSum_coeff]
  by_cases hk : k ≤ d
  · rw [coeff_jensenProductPolynomial, ite_eq_left hk, binomialConvolution, Finset.mul_sum]
    symm
    calc
      ∑ j ∈ Finset.range (d + 1), (B j).coeff k =
          ∑ j ∈ Finset.range (k + 1), (B j).coeff k := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))
        intro j hjd hjk
        have hkj : k < j := by
          simp only [Finset.mem_range, not_lt] at hjk
          lia
        simp only [B, coeff_C_mul, coeff_X_pow_mul',
          ite_eq_right (Nat.not_le.mpr hkj), mul_zero]
      _ = ∑ j ∈ Finset.range (k + 1),
          (d.choose k : ℝ) * ((k.choose j : ℝ) * gamma j * delta (k - j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : k - j ≤ d - j := Nat.sub_le_sub_right hk j
        simp only [B, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hjk,
          coeff_jensenPolynomial, ite_eq_left hsub]
        have hchoose : (d.choose j : ℝ) * ((d - j).choose (k - j) : ℝ) =
            (d.choose k : ℝ) * (k.choose j : ℝ) := by
          exact_mod_cast (Nat.choose_mul (n := d) (k := k) (s := j) hjk).symm
        linear_combination gamma j * delta (k - j) * hchoose
  · rw [coeff_jensenProductPolynomial, ite_eq_right hk]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjk : j ≤ k := by lia
    have hsub : ¬ k - j ≤ d - j := by lia
    simp only [B, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hjk,
      coeff_jensenPolynomial, ite_eq_right hsub, mul_zero]

/-- The reciprocal Jensen product expanded in reciprocal Jensen polynomials
of the second sequence. Degree loss and zero polynomials are included. -/
theorem reflect_jensenProductPolynomial_eq_sum (d : ℕ) (gamma delta : ℕ → ℝ) :
    reflect d (jensenProductPolynomial d gamma delta) =
      ∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * gamma j) *
        reflect (d - j) (jensenPolynomial (d - j) delta) := by
  rw [jensenProductPolynomial_eq_sum, reflect_finset_sum_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simpa only [Nat.sub_add_cancel hjd] using
    reflect_X_pow_mul (jensenPolynomial (d - j) delta) j
      (natDegree_jensenPolynomial_le (d - j) delta)

end RealRooted
