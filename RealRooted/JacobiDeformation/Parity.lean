import RealRooted.JacobiDeformation.Basic
import RealRooted.Mathlib.Combinatorics.Enumerative.CentralTrinomial

/-!
# Parity specializations of the Jacobi deformation

At `δ = 1 / 2`, `U = 1`, `V = 1 / 4` and `c = 1`, the two half-integer values
`d = 1 / 2` and `d = 3 / 2` turn the Pochhammer factors of the Jacobi
deformation into ordinary factorials.  The resulting coefficient sums factor
through the central trinomial coefficients:

* `coeff_polynomial_even_centralTrinomial`:
  `[X^k] J_{m,1/2}^{1,1/2}(X, 1, 1/4) = C(2m - k, k) T(2m - 2k)`;
* `coeff_polynomial_odd_centralTrinomial`:
  `(m + 1) [X^k] J_{m,1/2}^{1,3/2}(X, 1, 1/4) = C(2m + 1 - k, k) T(2m + 1 - 2k)`,

where `T = Nat.centralTrinomial`.  These are the even and odd rows of OEIS
A132885.
-/

open Finset

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Factorial forms of the parity summands -/

private theorem cast_factorial_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  positivity

/-- The half-integer rising factorial gives the even factorial. -/
theorem risingFactorial_one_half_mul_factorial_mul_four_pow (j : ℕ) :
    risingFactorial (1 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j =
      ((2 * j).factorial : ℝ) := by
  induction j with
  | zero => norm_num [risingFactorial]
  | succ j ih =>
    calc
      risingFactorial (1 / 2 : ℝ) (j + 1) * ((j + 1).factorial : ℝ) *
          4 ^ (j + 1) =
          (risingFactorial (1 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j) *
            ((1 / 2 : ℝ) + j) * ((j : ℝ) + 1) * 4 := by
        rw [risingFactorial_succ, Nat.factorial_succ, pow_succ]
        push_cast
        ring
      _ = ((2 * j).factorial : ℝ) * ((1 / 2 : ℝ) + j) * ((j : ℝ) + 1) * 4 := by
        rw [ih]
      _ = ((2 * (j + 1)).factorial : ℝ) := by
        rw [show 2 * (j + 1) = 2 * j + 2 by ring,
          Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j)]
        push_cast
        ring

/-- The three-halves rising factorial gives the odd factorial. -/
theorem risingFactorial_three_halves_mul_factorial_mul_four_pow (j : ℕ) :
    risingFactorial (3 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j =
      ((2 * j + 1).factorial : ℝ) := by
  induction j with
  | zero => norm_num [risingFactorial]
  | succ j ih =>
    calc
      risingFactorial (3 / 2 : ℝ) (j + 1) * ((j + 1).factorial : ℝ) *
          4 ^ (j + 1) =
          (risingFactorial (3 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j) *
            ((3 / 2 : ℝ) + j) * ((j : ℝ) + 1) * 4 := by
        rw [risingFactorial_succ, Nat.factorial_succ, pow_succ]
        push_cast
        ring
      _ = ((2 * j + 1).factorial : ℝ) * ((3 / 2 : ℝ) + j) * ((j : ℝ) + 1) *
          4 := by
        rw [ih]
      _ = ((2 * (j + 1) + 1).factorial : ℝ) := by
        rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
          Nat.factorial_succ (2 * j + 2), Nat.factorial_succ (2 * j + 1)]
        push_cast
        ring

private theorem risingFactorial_one_eq_factorial (i : ℕ) :
    risingFactorial (1 : ℝ) i = (i.factorial : ℝ) := by
  simp [risingFactorial]

/-- The even parity specialization of the Jacobi summand. -/
theorem summand_even_factorial {m i j k : ℕ} (hijk : i + j + k = m) :
    summand m (1 / 2) 1 (1 / 2) 1 (1 / 4) i j =
      ((2 * m - k).factorial : ℝ) /
        ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ)) := by
  have hsub : m - i - j = k := by lia
  have htop : m + (i + j) = 2 * m - k := by lia
  have hparameter : (m : ℝ) + 1 + (1 / 2 : ℝ) - 1 + 1 / 2 = (m : ℝ) + 1 := by
    ring
  have hbase : (m.factorial : ℝ) * risingFactorial ((m : ℝ) + 1) (i + j) =
      ((m + (i + j)).factorial : ℝ) := by
    simpa [risingFactorial] using factorial_mul_ascPochhammer ℝ m (i + j)
  have hhalf := risingFactorial_one_half_mul_factorial_mul_four_pow j
  have hhalf_ne : risingFactorial (1 / 2 : ℝ) j ≠ 0 :=
    (risingFactorial_pos j (by norm_num)).ne'
  have hfour_ne : (4 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    summand m (1 / 2) 1 (1 / 2) 1 (1 / 4) i j =
        ((m.factorial : ℝ) * risingFactorial ((m : ℝ) + 1) (i + j)) /
          ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 *
            (risingFactorial (1 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j)) := by
      unfold summand
      rw [hsub, hparameter, risingFactorial_one_eq_factorial]
      norm_num [div_pow]
      field_simp [cast_factorial_ne_zero, hhalf_ne, hfour_ne]
    _ = ((2 * m - k).factorial : ℝ) /
          ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 * ((2 * j).factorial : ℝ)) := by
      rw [hbase, hhalf, htop]

/-- The odd parity specialization of the Jacobi summand. -/
theorem summand_odd_factorial {m i j k : ℕ} (hijk : i + j + k = m) :
    ((m : ℝ) + 1) * summand m (1 / 2) 1 (3 / 2) 1 (1 / 4) i j =
      ((2 * m + 1 - k).factorial : ℝ) /
        ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 *
          ((2 * j + 1).factorial : ℝ)) := by
  have hsub : m - i - j = k := by lia
  have htop : m + 1 + (i + j) = 2 * m + 1 - k := by lia
  have hparameter : (m : ℝ) + 1 + (3 / 2 : ℝ) - 1 + 1 / 2 = (m : ℝ) + 2 := by
    ring
  have hbase : ((m + 1).factorial : ℝ) * risingFactorial ((m : ℝ) + 2) (i + j) =
      ((m + 1 + (i + j)).factorial : ℝ) := by
    have harg : (m : ℝ) + 2 = ((m + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [risingFactorial, harg]
    exact factorial_mul_ascPochhammer ℝ (m + 1) (i + j)
  have hthree := risingFactorial_three_halves_mul_factorial_mul_four_pow j
  have hthree_ne : risingFactorial (3 / 2 : ℝ) j ≠ 0 :=
    (risingFactorial_pos j (by norm_num)).ne'
  have hfour_ne : (4 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    ((m : ℝ) + 1) * summand m (1 / 2) 1 (3 / 2) 1 (1 / 4) i j =
        (((m + 1).factorial : ℝ) * risingFactorial ((m : ℝ) + 2) (i + j)) /
          ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 *
            (risingFactorial (3 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j)) := by
      unfold summand
      rw [hsub, hparameter, risingFactorial_one_eq_factorial,
        Nat.factorial_succ]
      norm_num [div_pow]
      field_simp [cast_factorial_ne_zero, hthree_ne, hfour_ne]
    _ = ((2 * m + 1 - k).factorial : ℝ) /
          ((k.factorial : ℝ) * (i.factorial : ℝ) ^ 2 *
            ((2 * j + 1).factorial : ℝ)) := by
      rw [hbase, hthree, htop]

/-! ## Central-trinomial forms of the parity coefficients -/

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
      ((2 * m - k).choose k : ℝ) * (Nat.centralTrinomial (2 * m - 2 * k) : ℝ) := by
  by_cases hk : k ≤ m
  · rw [coeff_polynomial, ite_eq_left hk]
    have hT := Nat.cast_centralTrinomial_two_mul_add_eq_sum_antidiagonal (m - k) 0 (by lia)
    have hT' : (Nat.centralTrinomial (2 * (m - k)) : ℝ) =
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
      _ = ((2 * m - k).choose k : ℝ) * (Nat.centralTrinomial (2 * m - 2 * k) : ℝ) := by
        rw [← hT', hindex]
  · have hlt : 2 * m - k < k := by lia
    rw [coeff_polynomial, ite_eq_right hk, Nat.choose_eq_zero_of_lt hlt]
    norm_num

/-- The odd Jacobi specialization has central-trinomial coefficients. -/
theorem coeff_polynomial_odd_centralTrinomial (m k : ℕ) :
    ((m : ℝ) + 1) * (polynomial m (1 / 2) 1 (3 / 2) 1 (1 / 4)).coeff k =
      ((2 * m + 1 - k).choose k : ℝ) * (Nat.centralTrinomial (2 * m + 1 - 2 * k) : ℝ) := by
  by_cases hk : k ≤ m
  · rw [coeff_polynomial, ite_eq_left hk, mul_sum]
    have hT := Nat.cast_centralTrinomial_two_mul_add_eq_sum_antidiagonal (m - k) 1 (by lia)
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
          (Nat.centralTrinomial (2 * m + 1 - 2 * k) : ℝ) := by
        rw [← hT, hindex]
  · have hlt : 2 * m + 1 - k < k := by lia
    rw [coeff_polynomial, ite_eq_right hk, Nat.choose_eq_zero_of_lt hlt]
    norm_num

end RealRooted.JacobiDeformation
