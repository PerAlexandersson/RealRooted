module

public import RealRooted.ParityFactorization
public import RealRooted.Favard.Affine.Basic
public import RealRooted.SequenceClosure
public import RealRooted.Tactic.RowInterlacing
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness

@[expose] public noncomputable section

open Polynomial
open RealRooted

namespace RealRooted.Tactic.Examples.RowParityFactorization

/-- The monic Chebyshev-type family with first row `X + 2`. -/
def lower : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 2
  | n + 2 => (X + 2) * lower (n + 1) - lower n

/-- The companion Chebyshev-type family with first row `X + 3`. -/
def upper : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 3
  | n + 2 => (X + 2) * upper (n + 1) - upper n

private theorem lower_splits (n : ℕ) : (lower n).Splits := by
  exact (RealRooted.isRealRooted_of_favard_const_coeff
    (P := lower) (α := -2) (β := 1) (hβ := by norm_num) (hP0 := rfl)
    (hP1 := by norm_num [lower, map_ofNat])
    (hstep := fun _ => by norm_num [lower, map_ofNat]) n).2

private theorem upper_splits (n : ℕ) : (upper n).Splits := by
  let α : ℕ → ℝ := fun n => if n = 0 then -3 else -2
  have h := RealRooted.isRealRooted_of_favard_param_coeff
    (P := upper) (α := α) (β := fun _ => 1) (hβ := fun _ => by norm_num) (hP0 := rfl)
    (hP1 := by norm_num [upper, α, map_ofNat])
    (hstep := fun k => by
      simp only [upper]
      unfold α
      rw [ite_eq_right (by lia : k + 1 ≠ 0)]
      norm_num [map_ofNat]) n
  exact h.2

private theorem upper_succ_eq_lower_succ_add_lower (k : ℕ) :
    upper (k + 1) = lower (k + 1) + lower k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 =>
          rw [show upper 1 = X + 3 from rfl, show lower 1 = X + 2 from rfl,
            show lower 0 = 1 from rfl]
          ring
      | 1 =>
          rw [show upper 2 = (X + 2) * upper 1 - upper 0 from rfl]
          rw [show lower 2 = (X + 2) * lower 1 - lower 0 from rfl]
          rw [show upper 1 = X + 3 from rfl, show upper 0 = 1 from rfl]
          rw [show lower 1 = X + 2 from rfl, show lower 0 = 1 from rfl]
          ring
      | j + 2 =>
          rw [show j + 2 + 1 = j + 3 by lia]
          rw [show upper (j + 3) = (X + 2) * upper (j + 2) - upper (j + 1) from rfl]
          rw [ih (j + 1) (by lia), ih j (by lia)]
          rw [show lower (j + 3) = (X + 2) * lower (j + 2) - lower (j + 1) from rfl]
          rw [show lower (j + 2) = (X + 2) * lower (j + 1) - lower j from rfl]
          ring

/-- The downstream recurrence for OEIS A156308. -/
def a156308 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 4 + X
  | 2 => 9 + 6 * X + X ^ 2
  | n + 3 => (3 + X) * a156308 (n + 2) + (-3 - X) * a156308 (n + 1) +
      a156308 n

private theorem a156308_shapes (k : ℕ) :
    a156308 (2 * k) = (upper k) ^ 2 ∧
      a156308 (2 * k + 1) = (X + C 4) * (lower k) ^ 2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 =>
          constructor
          · norm_num [a156308, upper]
          · rw [show a156308 1 = 4 + X from rfl, show lower 0 = 1 from rfl]
            norm_num [map_ofNat]
            ring
      | 1 =>
          constructor
          · rw [show a156308 2 = 9 + 6 * X + X ^ 2 from rfl]
            rw [show upper 1 = X + 3 from rfl]
            ring
          · rw [show a156308 3 =
                (3 + X) * a156308 2 + (-3 - X) * a156308 1 + a156308 0 from rfl]
            rw [show a156308 2 = 9 + 6 * X + X ^ 2 from rfl]
            rw [show a156308 1 = 4 + X from rfl, show a156308 0 = 1 from rfl]
            rw [show lower 1 = X + 2 from rfl]
            norm_num [map_ofNat]
            ring
      | j + 2 =>
          obtain ⟨he1, ho1⟩ := ih (j + 1) (by lia)
          obtain ⟨_, ho0⟩ := ih j (by lia)
          have hC1 := upper_succ_eq_lower_succ_add_lower (j + 1)
          have hC0 := upper_succ_eq_lower_succ_add_lower j
          have hB2 : lower (j + 2) = (X + 2) * lower (j + 1) - lower j := rfl
          constructor
          · rw [show 2 * (j + 2) = 2 * j + 4 by lia]
            rw [show 2 * j + 4 = (2 * j + 1) + 3 by lia, a156308]
            rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by lia]
            rw [show 2 * j + 1 + 1 = 2 * (j + 1) by lia]
            rw [ho1, he1, ho0, hC1, hC0, hB2]
            norm_num [map_ofNat]
            ring
          · have he2 : a156308 (2 * (j + 2)) = (upper (j + 2)) ^ 2 := by
              rw [show 2 * (j + 2) = 2 * j + 4 by lia]
              rw [show 2 * j + 4 = (2 * j + 1) + 3 by lia, a156308]
              rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by lia]
              rw [show 2 * j + 1 + 1 = 2 * (j + 1) by lia]
              rw [ho1, he1, ho0, hC1, hC0, hB2]
              norm_num [map_ofNat]
              ring
            rw [show 2 * (j + 2) + 1 = 2 * (j + 1) + 3 by lia, a156308]
            rw [show 2 * (j + 1) + 2 = 2 * (j + 2) by lia]
            rw [he2, ho1, he1, hC1, hC0, hB2]
            norm_num [map_ofNat]
            ring

private theorem a156308_splits (n : ℕ) : (a156308 n).Splits := by
  apply RealRooted.splits_of_parity_factorization
    (P := a156308) (E := fun k => (upper k) ^ 2) (O := fun k => (lower k) ^ 2)
    (a := 1) (b := 1) (c := X + C 4)
  · exact fun k => by simpa using (a156308_shapes k).1
  · exact fun k => by simpa using (a156308_shapes k).2
  · exact Polynomial.Splits.one
  · exact Polynomial.Splits.one
  · exact Polynomial.Splits.X_add_C 4
  · exact fun k => (upper_splits k).pow 2
  · exact fun k => (lower_splits k).pow 2

/-- Split-row transfer for the three-lag A156308 presentation. -/
@[rr_row_model]
theorem a156308_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 4 + X)
    (htwo : P 2 = 9 + 6 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = ((3 + X)) * P (n + 2) +
        ((-3 + (-1 * X))) * P (n + 1) + (1) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_three_recurrence
    (fun _ p q r => ((3 + X)) * p + ((-3 + (-1 * X))) * q + (1) * r)
    (hzero.trans (show (1 : ℝ[X]) = a156308 0 by rfl))
    (hone.trans (show (4 + X : ℝ[X]) = a156308 1 by rfl))
    (htwo.trans (show (9 + 6 * X + X ^ 2 : ℝ[X]) = a156308 2 by rfl))
    hrec (fun m => by rw [a156308]; ring)
  rw [heq n]
  exact a156308_splits n

example (n : ℕ) : (a156308 n).Splits := by
  exact a156308_splits n

/-- The scaled downstream recurrence for OEIS A334009. -/
def a334009 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 4 + 4 * X
  | 2 => 9 + 24 * X + 16 * X ^ 2
  | n + 3 => (3 + 4 * X) * a334009 (n + 2) + (-3 - 4 * X) *
      a334009 (n + 1) + a334009 n

private theorem a334009_eq_comp (n : ℕ) :
    a334009 n = (a156308 n).comp (C (4 : ℝ) * X) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => simp [a334009, a156308]
      | 1 =>
          norm_num [a334009, a156308, add_comp, X_comp, map_ofNat]
      | 2 =>
          simp only [a334009, a156308, mul_comp, add_comp, X_comp]
          norm_num [map_ofNat]
          ring
      | k + 3 =>
          rw [a334009, a156308]
          rw [ih (k + 2) (by lia), ih (k + 1) (by lia), ih k (by lia)]
          simp only [mul_comp, add_comp, X_comp]
          norm_num [map_ofNat]

private theorem a334009_splits (n : ℕ) : (a334009 n).Splits := by
  rw [a334009_eq_comp]
  exact (a156308_splits n).comp_of_natDegree_le_one (by simp)

/-- Split-row transfer for the scaled three-lag A334009 presentation. -/
@[rr_row_model]
theorem a334009_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 4 + 4 * X)
    (htwo : P 2 = 9 + 24 * X + 16 * X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = ((3 + (4 * X))) * P (n + 2) +
        ((-3 + (-4 * X))) * P (n + 1) + (1) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_three_recurrence
    (fun _ p q r => ((3 + (4 * X))) * p + ((-3 + (-4 * X))) * q + (1) * r)
    (hzero.trans (show (1 : ℝ[X]) = a334009 0 by rfl))
    (hone.trans (show (4 + 4 * X : ℝ[X]) = a334009 1 by rfl))
    (htwo.trans
      (show (9 + 24 * X + 16 * X ^ 2 : ℝ[X]) = a334009 2 by rfl))
    hrec (fun m => by rw [a334009]; ring)
  rw [heq n]
  exact a334009_splits n

private theorem a334009_natDegree (n : ℕ) : (a334009 n).natDegree = n := by
  rr_row_natDegree

example (n : ℕ) : (a334009 n).Splits := by
  exact a334009_splits n

/-- The reversed downstream recurrence for OEIS A082649. -/
def a082649 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 4 + 4 * X
  | 2 => 16 + 24 * X + 9 * X ^ 2
  | n + 3 => (4 + 3 * X) * a082649 (n + 2) + (-4 * X - 3 * X ^ 2) *
      a082649 (n + 1) + X ^ 3 * a082649 n

private theorem a082649_eq_reverse (n : ℕ) :
    a082649 n = (a334009 n).reverse := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          rw [show a082649 0 = 1 from rfl, show a334009 0 = 1 from rfl]
          simp [Polynomial.reverse]
      | 1 =>
          rw [show a082649 1 = 4 + 4 * X from rfl,
            show a334009 1 = 4 + 4 * X from rfl]
          rw [Polynomial.reverse,
            show (4 + 4 * X : ℝ[X]).natDegree = 1 by compute_degree!]
          rw [show (4 + 4 * X : ℝ[X]) =
              C (4 : ℝ) * X ^ 0 + C (4 : ℝ) * X ^ 1 by norm_num [map_ofNat]]
          rw [Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
            Polynomial.reflect_C_mul_X_pow]
          simp only [Polynomial.revAt_le (by lia : (0 : ℕ) ≤ 1),
            Polynomial.revAt_le (by lia : (1 : ℕ) ≤ 1)]
          norm_num [map_ofNat]
          ring
      | 2 =>
          rw [show a082649 2 = 16 + 24 * X + 9 * X ^ 2 from rfl,
            show a334009 2 = 9 + 24 * X + 16 * X ^ 2 from rfl]
          rw [Polynomial.reverse,
            show (9 + 24 * X + 16 * X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
          rw [show (9 + 24 * X + 16 * X ^ 2 : ℝ[X]) =
              C (9 : ℝ) * X ^ 0 + C (24 : ℝ) * X ^ 1 + C (16 : ℝ) * X ^ 2 by
            norm_num [map_ofNat]]
          rw [Polynomial.reflect_add, Polynomial.reflect_add,
            Polynomial.reflect_C_mul_X_pow, Polynomial.reflect_C_mul_X_pow,
            Polynomial.reflect_C_mul_X_pow]
          simp only [Polynomial.revAt_le (by lia : (0 : ℕ) ≤ 2),
            Polynomial.revAt_le (by lia : (1 : ℕ) ≤ 2),
            Polynomial.revAt_le (by lia : (2 : ℕ) ≤ 2)]
          norm_num [map_ofNat]
          ring
      | k + 3 =>
          rw [Polynomial.reverse, a334009_natDegree, a082649, a334009]
          rw [Polynomial.reflect_add, Polynomial.reflect_add]
          have hlin1 : Polynomial.reflect 1 (3 + 4 * X : ℝ[X]) = 4 + 3 * X := by
            rw [show (3 + 4 * X : ℝ[X]) =
                C (3 : ℝ) * X ^ 0 + C (4 : ℝ) * X ^ 1 by norm_num [map_ofNat]]
            rw [Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
              Polynomial.reflect_C_mul_X_pow]
            simp only [Polynomial.revAt_le (by lia : (0 : ℕ) ≤ 1),
              Polynomial.revAt_le (by lia : (1 : ℕ) ≤ 1)]
            norm_num [map_ofNat]
            ring
          have hlin2 : Polynomial.reflect 2 (-3 - 4 * X : ℝ[X]) =
              -4 * X - 3 * X ^ 2 := by
            rw [show (-3 - 4 * X : ℝ[X]) =
                C (-3 : ℝ) * X ^ 0 + C (-4 : ℝ) * X ^ 1 by
              norm_num [map_ofNat, map_neg]
              ring]
            rw [Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
              Polynomial.reflect_C_mul_X_pow]
            simp only [Polynomial.revAt_le (by lia : (0 : ℕ) ≤ 2),
              Polynomial.revAt_le (by lia : (1 : ℕ) ≤ 2)]
            norm_num [map_ofNat, map_neg]
            ring
          have hconst : Polynomial.reflect 3 (1 : ℝ[X]) = X ^ 3 := by simp
          rw [show k + 3 = 1 + (k + 2) by lia]
          rw [Polynomial.reflect_mul (3 + 4 * X : ℝ[X]) (a334009 (k + 2))
            (F := 1) (G := k + 2) (by compute_degree!) (by rw [a334009_natDegree])]
          rw [hlin1, show 1 + (k + 2) = 2 + (k + 1) by lia]
          rw [Polynomial.reflect_mul (-3 - 4 * X : ℝ[X]) (a334009 (k + 1))
            (F := 2) (G := k + 1) (by compute_degree!) (by rw [a334009_natDegree])]
          rw [hlin2, show 2 + (k + 1) = 3 + k by lia]
          have htail : Polynomial.reflect (3 + k) (a334009 k) =
              X ^ 3 * Polynomial.reflect k (a334009 k) := by
            calc
              Polynomial.reflect (3 + k) (a334009 k) =
                  Polynomial.reflect (3 + k) ((1 : ℝ[X]) * a334009 k) := by simp
              _ = Polynomial.reflect 3 (1 : ℝ[X]) *
                  Polynomial.reflect k (a334009 k) := by
                rw [Polynomial.reflect_mul (1 : ℝ[X]) (a334009 k)
                  (F := 3) (G := k) (by simp) (by rw [a334009_natDegree])]
              _ = X ^ 3 * Polynomial.reflect k (a334009 k) := by rw [hconst]
          rw [htail]
          rw [show Polynomial.reflect (k + 2) (a334009 (k + 2)) =
              (a334009 (k + 2)).reverse by rw [Polynomial.reverse, a334009_natDegree]]
          rw [show Polynomial.reflect (k + 1) (a334009 (k + 1)) =
              (a334009 (k + 1)).reverse by rw [Polynomial.reverse, a334009_natDegree]]
          rw [show Polynomial.reflect k (a334009 k) = (a334009 k).reverse by
            rw [Polynomial.reverse, a334009_natDegree]]
          simp_all

private theorem a082649_splits (n : ℕ) : (a082649 n).Splits := by
  rw [a082649_eq_reverse]
  exact Polynomial.Splits.reverse (a334009_splits n)

/-- Split-row transfer for the reversed three-lag A082649 presentation. -/
@[rr_row_model]
theorem a082649_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 4 + 4 * X)
    (htwo : P 2 = 16 + 24 * X + 9 * X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = ((4 + (3 * X))) * P (n + 2) +
        (((-4 * X) + (-3 * (X) ^ (2)))) * P (n + 1) +
        ((X) ^ (3)) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_three_recurrence
    (fun _ p q r => ((4 + (3 * X))) * p +
      (((-4 * X) + (-3 * (X) ^ (2)))) * q + ((X) ^ (3)) * r)
    (hzero.trans (show (1 : ℝ[X]) = a082649 0 by rfl))
    (hone.trans (show (4 + 4 * X : ℝ[X]) = a082649 1 by rfl))
    (htwo.trans
      (show (16 + 24 * X + 9 * X ^ 2 : ℝ[X]) = a082649 2 by rfl))
    hrec (fun m => by rw [a082649]; ring)
  rw [heq n]
  exact a082649_splits n

example (n : ℕ) : (a082649 n).Splits := by
  exact a082649_splits n

/-- The parity-lifted downstream recurrence for OEIS A099605. -/
def a099605 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | 2 => 1 + 5 * X + 4 * X ^ 2
  | 3 => 4 + 16 * X + 20 * X ^ 2 + 8 * X ^ 3
  | n + 4 => (2 + 4 * X ^ 2 + 6 * X) * a099605 (n + 2) +
      (-1 - X ^ 2 - 2 * X) * a099605 n

private def evenQ : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (4 : ℝ) * X + C (1 : ℝ)
  | n + 2 => (C (4 : ℝ) * X + C (2 : ℝ)) * evenQ (n + 1) - evenQ n

private def oddQ : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (4 : ℝ) * X + C (2 : ℝ)
  | n + 2 => (C (4 : ℝ) * X + C (2 : ℝ)) * oddQ (n + 1) - oddQ n

private theorem evenQ_splits (n : ℕ) : (evenQ n).Splits := by
  let α : ℕ → ℝ := fun k => if k = 0 then -1 else -2
  have h := RealRooted.isRealRooted_of_favard_affine_param_coeff
    (P := evenQ) (s := fun _ => 4) (α := α) (β := fun _ => 1)
    (hs := fun _ => by norm_num) (hβ := fun _ => by norm_num) (hP0 := rfl)
    (hP1 := by norm_num [evenQ, α])
    (hstep := fun k => by
      simp only [evenQ]
      unfold α
      rw [ite_eq_right (by lia : k + 1 ≠ 0)]
      norm_num) n
  exact h.2

private theorem oddQ_splits (n : ℕ) : (oddQ n).Splits := by
  exact (RealRooted.isRealRooted_of_favard_affine_const_coeff
    (P := oddQ) (s := 4) (α := -2) (β := 1) (hs := by norm_num) (hβ := by norm_num)
    (hP0 := rfl) (hP1 := by norm_num [oddQ])
    (hstep := fun _ => by norm_num [oddQ]) n).2

private theorem a099605_even_factor (k : ℕ) :
    a099605 (2 * k) = (1 + X) ^ k * evenQ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 => simp [evenQ, a099605]
      | 1 =>
          rw [show 2 * 1 = 2 by norm_num]
          rw [show a099605 2 = 1 + 5 * X + 4 * X ^ 2 from rfl]
          rw [show evenQ 1 = C (4 : ℝ) * X + C (1 : ℝ) from rfl]
          simp only [pow_one]
          apply Polynomial.funext
          intro r
          simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_ofNat]
          ring
      | n + 2 =>
          have h0 := ih n (by lia)
          have h1 := ih (n + 1) (by lia)
          rw [show 2 * (n + 2) = 2 * n + 4 by ring, a099605,
            show 2 * n + 2 = 2 * (n + 1) by ring, h0, h1, evenQ]
          rw [show (1 + X : ℝ[X]) ^ (n + 2) =
              (1 + X) ^ n * (1 + X) ^ 2 by grind]
          rw [show (1 + X : ℝ[X]) ^ (n + 1) =
              (1 + X) ^ n * (1 + X) by grind]
          apply Polynomial.funext
          intro r
          simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_ofNat,
            eval_neg, eval_sub]
          ring

private theorem a099605_odd_factor (k : ℕ) :
    a099605 (2 * k + 1) = C (2 : ℝ) * (1 + X) ^ (k + 1) * oddQ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 =>
          rw [show 2 * 0 + 1 = 1 by norm_num]
          rw [show a099605 1 = 2 + 2 * X from rfl, show oddQ 0 = 1 from rfl]
          simp only [pow_one, mul_one]
          apply Polynomial.funext
          intro r
          simp only [eval_add, eval_mul, eval_X, eval_C, eval_one, eval_ofNat]
          ring
      | 1 =>
          rw [show 2 * 1 + 1 = 3 by norm_num]
          rw [show a099605 3 = 4 + 16 * X + 20 * X ^ 2 + 8 * X ^ 3 from rfl]
          rw [show oddQ 1 = C (4 : ℝ) * X + C (2 : ℝ) from rfl]
          norm_num only [Nat.reduceAdd]
          apply Polynomial.funext
          intro r
          simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_ofNat]
          ring
      | n + 2 =>
          have h0 := ih n (by lia)
          have h1 := ih (n + 1) (by lia)
          rw [show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, a099605,
            show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by ring, h0, h1, oddQ]
          rw [show (1 + X : ℝ[X]) ^ (n + 2 + 1) =
              (1 + X) ^ (n + 1) * (1 + X) ^ 2 by grind]
          rw [show (1 + X : ℝ[X]) ^ (n + 1 + 1) =
              (1 + X) ^ (n + 1) * (1 + X) by grind]
          apply Polynomial.funext
          intro r
          simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_ofNat,
            eval_neg, eval_sub]
          ring

private theorem one_add_X_splits : (1 + X : ℝ[X]).Splits := by
  simpa [sub_eq_add_neg, add_comm] using (RealRooted.isRealRooted_X_sub_C (-1 : ℝ)).2

private theorem a099605_splits (n : ℕ) : (a099605 n).Splits := by
  apply RealRooted.splits_of_parity_factorization
    (P := a099605) (E := evenQ) (O := oddQ) (a := 1 + X) (b := 1 + X)
    (c := C 2)
  · exact a099605_even_factor
  · exact a099605_odd_factor
  · exact one_add_X_splits
  · exact one_add_X_splits
  · exact Polynomial.Splits.C 2
  · exact evenQ_splits
  · exact oddQ_splits

/-- Split-row transfer for the parity-factored order-four A099605 presentation. -/
@[rr_row_model]
theorem a099605_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + 2 * X)
    (htwo : P 2 = 1 + 5 * X + 4 * X ^ 2)
    (hthree : P 3 = 4 + 16 * X + 20 * X ^ 2 + 8 * X ^ 3)
    (hrec : ∀ n : ℕ,
      P (n + 4) = ((2 + (4 * (X) ^ (2)) + (6 * X))) * P (n + 2) +
        ((-1 + (-1 * (X) ^ (2)) + (-2 * X))) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq : ∀ m : ℕ, P m = a099605 m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        rcases m with _ | _ | _ | _ | m
        · exact hzero
        · exact hone
        · exact htwo
        · exact hthree
        · rw [hrec, a099605, ih (m + 2) (by lia), ih m (by lia)]
          ring
  rw [heq n]
  exact a099605_splits n

example (n : ℕ) : (a099605 n).Splits := by
  exact a099605_splits n

/-- The four-lag downstream recurrence for OEIS A049325. -/
def a049325 : ℕ → ℝ[X]
  | 0 => 16 + 12 * X + X ^ 2
  | 1 => 16 + 68 * X + 18 * X ^ 2 + X ^ 3
  | 2 => 224 * X + 156 * X ^ 2 + 24 * X ^ 3 + X ^ 4
  | 3 => 448 * X + 840 * X ^ 2 + 280 * X ^ 3 + 30 * X ^ 4 + X ^ 5
  | n + 4 => X * a049325 (n + 3) + 6 * X * a049325 (n + 2) +
      16 * X * a049325 (n + 1) + 16 * X * a049325 n

private theorem a049325_natDegree (n : ℕ) : (a049325 n).natDegree = n + 2 := by
  rr_row_natDegree

private theorem a049325_leadingCoeff_pos (n : ℕ) :
    0 < (a049325 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

private theorem a049325_nonneg (n : ℕ) : HasNonnegCoeffs (a049325 n) := by
  rr_row_nonneg_coeffs

private theorem a049325_first_order : ∀ n : ℕ,
    C ((n : ℝ) + 4) * a049325 (n + 1) =
      X * (X + C 16) * (a049325 n).derivative +
        (C (4 - 4 * (n : ℝ)) + C 2 * X) * a049325 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases lt_or_ge n 4 with hn | hn
      · interval_cases n <;>
          norm_num [a049325, derivative_add, derivative_mul, derivative_X,
            derivative_pow, derivative_ofNat, map_ofNat] <;> ring
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by lia⟩
        have h0 := ih k (by lia)
        have h1 := ih (k + 1) (by lia)
        have h2 := ih (k + 2) (by lia)
        have h3 := ih (k + 3) (by lia)
        have hrec : a049325 (k + 4) =
            X * a049325 (k + 3) + 6 * X * a049325 (k + 2) +
              16 * X * a049325 (k + 1) + 16 * X * a049325 k := by
          rw [a049325]
        rw [show a049325 (k + 4 + 1) =
            X * a049325 (k + 4) + 6 * X * a049325 (k + 3) +
              16 * X * a049325 (k + 2) + 16 * X * a049325 (k + 1) by
            rw [show k + 4 + 1 = k + 1 + 4 by lia, a049325]]
        rw [hrec]
        rw [show k + 3 + 1 = k + 4 by lia, hrec] at h3
        simp only [derivative_add, derivative_mul, derivative_X, one_mul,
          derivative_ofNat, zero_mul, zero_add]
        norm_num [map_ofNat] at h0 h1 h2 h3 ⊢
        linear_combination X * h3 + 6 * X * h2 + 16 * X * h1 + 16 * X * h0

private def shifted049325 (n : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ (n + 2)) * (a049325 n).comp (C (-16) - X)

private theorem shifted049325_first_order (n : ℕ) :
    C ((n : ℝ) + 4) * shifted049325 (n + 1) =
      X * (X + C 16) * (shifted049325 n).derivative +
        (C (4 * (n : ℝ) + 28) + C 2 * X) * shifted049325 n := by
  have h := congrArg
    (fun p : ℝ[X] => C ((-1 : ℝ) ^ (n + 3)) * p.comp (C (-16) - X))
    (a049325_first_order n)
  unfold shifted049325
  simp only [mul_comp, add_comp, C_comp, X_comp, derivative_mul,
    derivative_C, zero_mul, zero_add, derivative_comp, sub_eq_add_neg] at h ⊢
  rcases Nat.even_or_odd n with hn | hn
  · norm_num [pow_add, hn.neg_one_pow, map_ofNat] at h ⊢
    grind
  · norm_num [pow_add, hn.neg_one_pow, map_ofNat] at h ⊢
    grind

private theorem shifted049325_nonneg : ∀ n : ℕ, HasNonnegCoeffs (shifted049325 n)
  | 0 => by
      have hbase : shifted049325 0 = 80 + 20 * X + X ^ 2 := by
        unfold shifted049325
        norm_num [a049325, map_ofNat, add_comp, mul_comp, pow_comp]
        ring
      rw [hbase]
      exact ((hasNonnegCoeffs_C (by norm_num)).add
        ((hasNonnegCoeffs_C (by norm_num)).mul hasNonnegCoeffs_X)).add
          (hasNonnegCoeffs_X.pow 2)
  | n + 1 => by
      have ih := shifted049325_nonneg n
      let R := X * (X + C 16) * (shifted049325 n).derivative +
        (C (4 * (n : ℝ) + 28) + C 2 * X) * shifted049325 n
      have hR : HasNonnegCoeffs R := by
        dsimp [R]
        have hlinear : HasNonnegCoeffs (X + C (16 : ℝ)) :=
          hasNonnegCoeffs_X.add (hasNonnegCoeffs_C (by norm_num))
        have hder : HasNonnegCoeffs
            (X * (X + C 16) * (shifted049325 n).derivative) :=
          (hasNonnegCoeffs_X.mul hlinear).mul ih.derivative
        have hcoeff : HasNonnegCoeffs (C (4 * (n : ℝ) + 28) + C 2 * X) :=
          (hasNonnegCoeffs_C (by positivity)).add
            ((hasNonnegCoeffs_C (by norm_num)).mul hasNonnegCoeffs_X)
        exact hder.add (hcoeff.mul ih)
      have hden : (n : ℝ) + 4 ≠ 0 := by positivity
      have heq : shifted049325 (n + 1) = C (1 / ((n : ℝ) + 4)) * R := by
        calc
          shifted049325 (n + 1) = C (1 / ((n : ℝ) + 4)) *
              (C ((n : ℝ) + 4) * shifted049325 (n + 1)) := by
            rw [← mul_assoc, ← map_mul]
            simp_all
          _ = C (1 / ((n : ℝ) + 4)) * R := by rw [shifted049325_first_order]
      rw [heq]
      exact hasNonnegCoeffs_C_mul (by positivity) hR

private theorem shifted049325_ne_zero (n : ℕ) : shifted049325 n ≠ 0 := by
  have hudeg : (C (-16 : ℝ) - X).natDegree = 1 := by compute_degree!
  have hcompdeg : ((a049325 n).comp (C (-16) - X)).natDegree = n + 2 := by
    rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
    · rw [a049325_natDegree]
      simp only [hudeg, mul_one]
    · have hu : (C (-16 : ℝ) - X).leadingCoeff = -1 := by
        rw [leadingCoeff, hudeg]
        simp
      rw [hu]
      exact mul_ne_zero (a049325_leadingCoeff_pos n).ne' (by norm_num)
  intro hzero
  have hdeg := hcompdeg
  unfold shifted049325 at hzero
  simp_all

private theorem a049325_roots_ge_neg_sixteen (n : ℕ) {r : ℝ}
    (hr : (a049325 n).IsRoot r) : -16 ≤ r := by
  let s : ℝ := -16 - r
  have hroot : (shifted049325 n).IsRoot s := by
    unfold shifted049325
    simp only [IsRoot, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
    have : -16 - s = r := by grind
    simp_all
  have hmem : s ∈ (shifted049325 n).roots :=
    (mem_roots (shifted049325_ne_zero n)).mpr hroot
  have hsle : s ≤ 0 := roots_nonpos_of_hasNonnegCoeffs (shifted049325_nonneg n) s hmem
  grind

private theorem a049325_strictInterl_step (n : ℕ) (hs : (a049325 n).Splits) :
    StrictInterl (a049325 n) (a049325 (n + 1)) := by
  let u : ℝ[X] := C (4 - 4 * (n : ℝ)) + C 2 * X
  let v : ℝ[X] := X * (X + C 16)
  let F : ℝ[X] := C ((n : ℝ) + 4) * a049325 (n + 1)
  have hrec : F = u * a049325 n + v * (a049325 n).derivative := by
    dsimp [F, u, v]
    simpa only [add_comm] using a049325_first_order n
  have hfpos : HasPosLeadingCoeff (a049325 n) := a049325_leadingCoeff_pos n
  have hFpos : HasPosLeadingCoeff F := by
    dsimp [F]
    exact hasPosLeadingCoeff_C_mul (by positivity) (a049325_leadingCoeff_pos (n + 1))
  have hv : ∀ r, (a049325 n).IsRoot r → v.eval r ≤ 0 := by
    intro r hr
    have hrlo := a049325_roots_ge_neg_sixteen n hr
    have hpne : a049325 n ≠ 0 :=
      leadingCoeff_ne_zero.mp (a049325_leadingCoeff_pos n).ne'
    have hrhi := roots_nonpos_of_hasNonnegCoeffs (a049325_nonneg n) r
      ((mem_roots hpne).mpr hr)
    dsimp [v]
    simp only [eval_mul, eval_add, eval_X, eval_C]
    nlinarith
  have hFdeg : F.natDegree = n + 3 := by
    dsimp [F]
    rw [natDegree_C_mul (by positivity), a049325_natDegree]
  have hcore : StrictInterl (a049325 n) F := by
    have h := MaWang.strictInterl_derivative_of_nonpos_of_recurrence_of_splits
      (f := a049325 n) (F := F) (u := u) (v := v) hs hrec hFpos
      (by rw [a049325_natDegree, hFdeg]; lia)
      (by rw [a049325_natDegree, hFdeg]) hfpos hv
    simpa only [hrec] using h
  have hscaled := StrictInterl.C_mul_right hcore
    (by positivity : 1 / ((n : ℝ) + 4) ≠ 0)
  have hden : (n : ℝ) + 4 ≠ 0 := by positivity
  convert hscaled using 1
  rw [← mul_assoc, ← map_mul]
  simp_all

private theorem a049325_splits : ∀ n : ℕ, (a049325 n).Splits
  | 0 => by
      rw [show a049325 0 = 16 + 12 * X + X ^ 2 from rfl]
      apply splits_of_natDegree_eq_two_of_discrim_nonneg (by compute_degree!)
      norm_num [discrim, coeff_add, coeff_X, coeff_X_pow]
  | n + 1 => (a049325_strictInterl_step n (a049325_splits n)).2.1.2

/-- Split-row transfer for the order-four A049325 presentation. -/
@[rr_row_model]
theorem a049325_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 16 + 12 * X + X ^ 2)
    (hone : P 1 = 16 + 68 * X + 18 * X ^ 2 + X ^ 3)
    (htwo : P 2 = 224 * X + 156 * X ^ 2 + 24 * X ^ 3 + X ^ 4)
    (hthree : P 3 =
      448 * X + 840 * X ^ 2 + 280 * X ^ 3 + 30 * X ^ 4 + X ^ 5)
    (hrec : ∀ n : ℕ,
      P (n + 4) = X * P (n + 3) + 6 * X * P (n + 2) +
        16 * X * P (n + 1) + 16 * X * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq : ∀ m : ℕ, P m = a049325 m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        rcases m with _ | _ | _ | _ | m
        · exact hzero
        · exact hone
        · exact htwo
        · exact hthree
        · rw [hrec, a049325, ih (m + 3) (by lia), ih (m + 2) (by lia),
            ih (m + 1) (by lia), ih m (by lia)]
  rw [heq n]
  exact a049325_splits n

/-- Consecutive-row transfer for the order-four A049325 presentation. -/
@[rr_row_model]
theorem a049325_interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 16 + 12 * X + X ^ 2)
    (hone : P 1 = 16 + 68 * X + 18 * X ^ 2 + X ^ 3)
    (htwo : P 2 = 224 * X + 156 * X ^ 2 + 24 * X ^ 3 + X ^ 4)
    (hthree : P 3 =
      448 * X + 840 * X ^ 2 + 280 * X ^ 3 + 30 * X ^ 4 + X ^ 5)
    (hrec : ∀ n : ℕ,
      P (n + 4) = X * P (n + 3) + 6 * X * P (n + 2) +
        16 * X * P (n + 1) + 16 * X * P n)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m : ℕ, P m = a049325 m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        rcases m with _ | _ | _ | _ | m
        · exact hzero
        · exact hone
        · exact htwo
        · exact hthree
        · rw [hrec, a049325, ih (m + 3) (by lia), ih (m + 2) (by lia),
            ih (m + 1) (by lia), ih m (by lia)]
  rw [heq n, heq (n + 1)]
  exact (a049325_strictInterl_step n (a049325_splits n)).toInterlaces (by
    rw [a049325_natDegree, a049325_natDegree])

example (n : ℕ) : (a049325 n).Splits := by
  exact a049325_splits n

example (n : ℕ) : Interlaces (a049325 n) (a049325 (n + 1)) := by
  exact (a049325_strictInterl_step n (a049325_splits n)).toInterlaces (by
    rw [a049325_natDegree, a049325_natDegree])

end RealRooted.Tactic.Examples.RowParityFactorization
