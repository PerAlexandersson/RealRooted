import RealRooted.JacobiDeformation.Basic

/-!
# Parity specializations of the Jacobi summand

The half-integer Pochhammer factors in the two parity specializations reduce
the actual Jacobi summands to factorial quotients.
-/

namespace RealRooted.JacobiDeformation

private theorem cast_factorial_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  positivity

/-- The half-integer rising factorial gives the even factorial. -/
theorem risingFactorial_one_half_mul_factorial_mul_four_pow (j : ℕ) :
    risingFactorial (1 / 2 : ℝ) j * (j.factorial : ℝ) * 4 ^ j =
      ((2 * j).factorial : ℝ) := by
  induction j with
  | zero => norm_num [risingFactorial]
  | succ j ih =>
    change risingFactorial (1 / 2 : ℝ) (j + 1) * ((j + 1).factorial : ℝ) *
        4 ^ (j + 1) = ((2 * (j + 1)).factorial : ℝ)
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
    change risingFactorial (3 / 2 : ℝ) (j + 1) * ((j + 1).factorial : ℝ) *
        4 ^ (j + 1) = ((2 * (j + 1) + 1).factorial : ℝ)
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
  simpa [risingFactorial] using ascPochhammer_eval_one ℝ i

/-- The even parity specialization of the actual Jacobi summand. -/
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

/-- The odd parity specialization of the actual Jacobi summand. -/
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

end RealRooted.JacobiDeformation
