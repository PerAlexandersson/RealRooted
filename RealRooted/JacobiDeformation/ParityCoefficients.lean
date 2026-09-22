import RealRooted.JacobiDeformation.CentralTrinomialParity
import RealRooted.JacobiDeformation.ParitySummands

/-!
# Central-trinomial forms of the parity-specialized Jacobi coefficients

The finite Jacobi coefficient sums factor through the actual central trinomial
sum in the even and odd parameter specializations.
-/

open Finset
open scoped BigOperators

namespace RealRooted.JacobiDeformation

private theorem cast_factorial_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  positivity

private theorem factorial_div_eq_choose_mul_factorial_div {n k : ℕ} (hkn : k ≤ n)
    (d : ℝ) (hd : d ≠ 0) :
    (n.factorial : ℝ) / ((k.factorial : ℝ) * d) =
      (n.choose k : ℝ) * (((n - k).factorial : ℝ) / d) := by
  have hchoose' := Nat.choose_mul_factorial_mul_factorial hkn
  have hchoose : (n.choose k : ℝ) * (k.factorial : ℝ) *
      ((n - k).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast congrArg (fun a : ℕ => (a : ℝ)) hchoose'
  rw [← hchoose]
  field_simp [cast_factorial_ne_zero, hd]

private theorem even_summand_factorization {m k i j : ℕ} (hk : k ≤ m)
    (hij : i + j = m - k) :
    summand m (1 / 2) 1 (1 / 2) 1 (1 / 4) i j =
      ((2 * m - k).choose k : ℝ) *
        (((2 * (m - k)).factorial : ℝ) /
          ((i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ))) := by
  have hijk : i + j + k = m := by lia
  have hkn : k ≤ 2 * m - k := by lia
  have hsub : 2 * m - k - k = 2 * (m - k) := by lia
  have hden : (i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ) ≠ 0 := by
    positivity
  rw [summand_even_factorial hijk]
  calc
    ((2 * m - k).factorial : ℝ) /
        ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ)) =
        ((2 * m - k).factorial : ℝ) /
          ((k.factorial : ℝ) *
            ((i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ))) := by
      ring
    _ = ((2 * m - k).choose k : ℝ) *
          (((2 * m - k - k).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ))) := by
      rw [factorial_div_eq_choose_mul_factorial_div hkn _ hden]
    _ = ((2 * m - k).choose k : ℝ) *
          (((2 * (m - k)).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ))) := by
      rw [hsub]

private theorem odd_summand_factorization {m k i j : ℕ} (hk : k ≤ m)
    (hij : i + j = m - k) :
    ((m : ℝ) + 1) * summand m (1 / 2) 1 (3 / 2) 1 (1 / 4) i j =
      ((2 * m + 1 - k).choose k : ℝ) *
        (((2 * (m - k) + 1).factorial : ℝ) /
          ((i.factorial : ℝ) ^ 2 * ((2 * j + 1).factorial : ℝ))) := by
  have hijk : i + j + k = m := by lia
  have hkn : k ≤ 2 * m + 1 - k := by lia
  have hsub : 2 * m + 1 - k - k = 2 * (m - k) + 1 := by lia
  have hden : (i.factorial : ℝ) ^ 2 * ((2 * j + 1).factorial : ℝ) ≠ 0 := by
    positivity
  rw [summand_odd_factorial hijk]
  calc
    ((2 * m + 1 - k).factorial : ℝ) /
        ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 *
          ((2 * j + 1).factorial : ℝ)) =
        ((2 * m + 1 - k).factorial : ℝ) /
          ((k.factorial : ℝ) *
            ((i.factorial : ℝ) ^ 2 * ((2 * j + 1).factorial : ℝ))) := by
      ring
    _ = ((2 * m + 1 - k).choose k : ℝ) *
          (((2 * m + 1 - k - k).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * j + 1).factorial : ℝ))) := by
      rw [factorial_div_eq_choose_mul_factorial_div hkn _ hden]
    _ = ((2 * m + 1 - k).choose k : ℝ) *
          (((2 * (m - k) + 1).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * j + 1).factorial : ℝ))) := by
      rw [hsub]

/-- The even Jacobi specialization has central-trinomial coefficients. -/
theorem coeff_polynomial_even_centralTrinomial (m k : ℕ) :
    (polynomial m (1 / 2) 1 (1 / 2) 1 (1 / 4)).coeff k =
      ((2 * m - k).choose k : ℝ) * CentralTrinomial.T (2 * m - 2 * k) := by
  by_cases hk : k ≤ m
  · rw [coeff_polynomial, ite_eq_left hk]
    have hT := centralTrinomial_parity_antidiagonal_factorial (m - k) 0 (by lia)
    have hT' : CentralTrinomial.T (2 * (m - k)) =
        ∑ ij ∈ antidiagonal (m - k), ((2 * (m - k)).factorial : ℝ) /
          ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2).factorial : ℝ)) := by
      simpa using hT
    have hindex : 2 * (m - k) = 2 * m - 2 * k := by lia
    calc
      ∑ ij ∈ antidiagonal (m - k), summand m (1 / 2) 1 (1 / 2) 1 (1 / 4) ij.1 ij.2 =
          ∑ ij ∈ antidiagonal (m - k), ((2 * m - k).choose k : ℝ) *
            (((2 * (m - k)).factorial : ℝ) /
              ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2).factorial : ℝ))) := by
        refine sum_congr rfl ?_
        intro ij hij
        exact even_summand_factorization hk (mem_antidiagonal.mp hij)
      _ = (2 * m - k).choose k *
          ∑ ij ∈ antidiagonal (m - k), ((2 * (m - k)).factorial : ℝ) /
            ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2).factorial : ℝ)) := by
        rw [mul_sum]
      _ = ((2 * m - k).choose k : ℝ) * CentralTrinomial.T (2 * m - 2 * k) := by
        rw [← hT', hindex]
  · have hlt : 2 * m - k < k := by lia
    rw [coeff_polynomial, ite_eq_right hk, Nat.choose_eq_zero_of_lt hlt]
    norm_num

/-- The odd Jacobi specialization has central-trinomial coefficients. -/
theorem coeff_polynomial_odd_centralTrinomial (m k : ℕ) :
    ((m : ℝ) + 1) * (polynomial m (1 / 2) 1 (3 / 2) 1 (1 / 4)).coeff k =
      ((2 * m + 1 - k).choose k : ℝ) * CentralTrinomial.T (2 * m + 1 - 2 * k) := by
  by_cases hk : k ≤ m
  · rw [coeff_polynomial, ite_eq_left hk, mul_sum]
    have hT := centralTrinomial_parity_antidiagonal_factorial (m - k) 1 (by lia)
    have hindex : 2 * (m - k) + 1 = 2 * m + 1 - 2 * k := by lia
    calc
      ∑ ij ∈ antidiagonal (m - k), ((m : ℝ) + 1) *
          summand m (1 / 2) 1 (3 / 2) 1 (1 / 4) ij.1 ij.2 =
          ∑ ij ∈ antidiagonal (m - k), ((2 * m + 1 - k).choose k : ℝ) *
            (((2 * (m - k) + 1).factorial : ℝ) /
              ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2 + 1).factorial : ℝ))) := by
        refine sum_congr rfl ?_
        intro ij hij
        exact odd_summand_factorization hk (mem_antidiagonal.mp hij)
      _ = (2 * m + 1 - k).choose k *
          ∑ ij ∈ antidiagonal (m - k), ((2 * (m - k) + 1).factorial : ℝ) /
            ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2 + 1).factorial : ℝ)) := by
        rw [mul_sum]
      _ = ((2 * m + 1 - k).choose k : ℝ) *
          CentralTrinomial.T (2 * m + 1 - 2 * k) := by
        rw [← hT, hindex]
  · have hlt : 2 * m + 1 - k < k := by lia
    rw [coeff_polynomial, ite_eq_right hk, Nat.choose_eq_zero_of_lt hlt]
    norm_num

end RealRooted.JacobiDeformation
