module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Topology.Order.IntermediateValue
public import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# OEIS A124848

This module defines the row polynomials of OEIS A124848 by their coefficient
formula. For rows of index at least three, a derivative computation factors
them as a power of `1 + X` times a cubic. Sign changes at three explicit
points locate all three cubic roots in `(-1, 0)`.

The intended repository destination is
`RealRooted/Applications/OEIS/A124848.lean`.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.Applications.OEIS.A124848

/-- The entry `T(n, k) = (k + 1)(k + 2)(k + 3) C(n, k) / 6` of OEIS
A124848. -/
def coefficient (n k : ℕ) : ℝ :=
  (((k + 1) * (k + 2) * (k + 3) * n.choose k : ℕ) : ℝ) / 6

/-- The row polynomial `∑_k T(n, k) X ^ k` of OEIS A124848. -/
def polynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (coefficient n k) * X ^ k

/-- The cubic factor remaining after removing the persistent power of
`1 + X` from a row of index at least three. -/
def cubic (n : ℝ) : ℝ[X] :=
  C (n * (n - 1) * (n - 2)) * X ^ 3 +
    C (9 * n * (n - 1)) * X ^ 2 * (1 + X) +
      C (18 * n) * X * (1 + X) ^ 2 + C 6 * (1 + X) ^ 3

private theorem one_add_X_pow (n : ℕ) :
    (1 + X : ℝ[X]) ^ n =
      ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℕ) : ℝ) * X ^ k := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

private theorem derivative_three_eq_polynomial (n : ℕ) :
    derivative (derivative (derivative (X ^ 3 * (1 + X : ℝ[X]) ^ n))) =
      C 6 * polynomial n := by
  rw [one_add_X_pow, polynomial, Finset.mul_sum, Finset.mul_sum]
  simp only [derivative_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmul :
      (X : ℝ[X]) ^ 3 * (C ((n.choose k : ℕ) : ℝ) * X ^ k) =
        C ((n.choose k : ℕ) : ℝ) * X ^ (k + 3) := by
    ring
  rw [hmul]
  simp only [derivative_C_mul, derivative_X_pow, coefficient]
  simp only [← mul_assoc, ← C_mul, show k + 3 - 1 - 1 - 1 = k by lia]
  congr 2
  push_cast
  ring

private theorem derivative_one_add_X_pow (k : ℕ) :
    derivative ((1 + X : ℝ[X]) ^ (k + 1)) =
      ((k : ℝ[X]) + 1) * (1 + X) ^ k := by
  rw [derivative_pow]
  simp

private theorem derivative_three_eq_cubic (m : ℕ) :
    derivative (derivative (derivative (X ^ 3 * (1 + X : ℝ[X]) ^ (m + 3)))) =
      (1 + X) ^ m * cubic ((m + 3 : ℕ) : ℝ) := by
  have h3 := derivative_one_add_X_pow (m + 2)
  have h2 := derivative_one_add_X_pow (m + 1)
  have h1 := derivative_one_add_X_pow m
  simp only [show m + 2 + 1 = m + 3 by lia,
    show m + 1 + 1 = m + 2 by lia] at h3 h2
  simp only [derivative_mul, h3, h2, h1, derivative_X_pow, derivative_add,
    derivative_natCast, derivative_one, derivative_C, derivative_zero]
  simp only [cubic, pow_succ (1 + X : ℝ[X]), map_mul, map_sub,
    map_natCast, map_ofNat, map_one]
  push_cast
  ring

private theorem eval_cubic (n x : ℝ) :
    (cubic n).eval x =
      n * (n - 1) * (n - 2) * x ^ 3 +
        9 * n * (n - 1) * x ^ 2 * (1 + x) +
          18 * n * x * (1 + x) ^ 2 + 6 * (1 + x) ^ 3 := by
  simp [cubic]

private theorem exists_root_Ioo {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (h : p.eval a * p.eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ p.eval c = 0 := by
  have ha0 : p.eval a ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at h
    exact (lt_irrefl 0 h)
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · have hb : 0 < p.eval b := by nlinarith
    obtain ⟨c, hc, hc'⟩ :=
      intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨ha, hb⟩
    exact ⟨c, hc.1, hc.2, hc'⟩
  · have hb : p.eval b < 0 := by nlinarith
    obtain ⟨c, hc, hc'⟩ :=
      intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨hb, ha⟩
    exact ⟨c, hc.1, hc.2, hc'⟩

/-- Rows of index at least three factor as a power of `1 + X` times a cubic. -/
theorem polynomial_add_three (m : ℕ) :
    polynomial (m + 3) =
      C (1 / 6) * (1 + X) ^ m * cubic ((m + 3 : ℕ) : ℝ) := by
  have h :=
    (derivative_three_eq_polynomial (m + 3)).symm.trans
      (derivative_three_eq_cubic m)
  calc
    polynomial (m + 3) = C (1 / 6) * (C 6 * polynomial (m + 3)) := by
      rw [← mul_assoc, ← C_mul]
      norm_num
    _ = _ := by rw [h, mul_assoc]

/-- The cubic cofactor of row `m + 3` has three ordered roots in `(-1, 0)`. -/
theorem exists_three_roots_cubic (m : ℕ) :
    ∃ a b c : ℝ, -1 < a ∧ a < b ∧ b < c ∧ c < 0 ∧
      (cubic ((m + 3 : ℕ) : ℝ)).eval a = 0 ∧
        (cubic ((m + 3 : ℕ) : ℝ)).eval b = 0 ∧
          (cubic ((m + 3 : ℕ) : ℝ)).eval c = 0 := by
  set n : ℝ := ((m + 3 : ℕ) : ℝ) with hn
  have hn3 : (3 : ℝ) ≤ n := by
    rw [hn]
    push_cast
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have e1 : (cubic n).eval (-1) < 0 := by
    have h : 0 < n * (n - 1) * (n - 2) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    rw [eval_cubic]
    norm_num
    linarith
  have e2 : 0 < (cubic n).eval (-4 / (n + 3)) := by
    rw [eval_cubic]
    have h :
        n * (n - 1) * (n - 2) * (-4 / (n + 3)) ^ 3 +
            9 * n * (n - 1) * (-4 / (n + 3)) ^ 2 *
              (1 + -4 / (n + 3)) +
            18 * n * (-4 / (n + 3)) * (1 + -4 / (n + 3)) ^ 2 +
            6 * (1 + -4 / (n + 3)) ^ 3 =
          (n - 1) * (14 * n ^ 2 + 44 * n + 6) / (n + 3) ^ 3 := by
      field_simp
      ring
    rw [h]
    apply div_pos
    · nlinarith
    · positivity
  have e3 : (cubic n).eval (-1 / n) < 0 := by
    rw [eval_cubic]
    have h :
        n * (n - 1) * (n - 2) * (-1 / n) ^ 3 +
            9 * n * (n - 1) * (-1 / n) ^ 2 * (1 + -1 / n) +
            18 * n * (-1 / n) * (1 + -1 / n) ^ 2 +
            6 * (1 + -1 / n) ^ 3 =
          -((n - 1) * (4 * n ^ 2 + n - 6) / n ^ 3) := by
      field_simp
      ring
    rw [h, neg_lt_zero]
    apply div_pos
    · nlinarith
    · positivity
  have e4 : 0 < (cubic n).eval 0 := by
    rw [eval_cubic]
    norm_num
  have l1 : -1 < -4 / (n + 3) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have l2 : -4 / (n + 3) < -1 / n := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    linarith
  have l3 : -1 / n < 0 := by
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
  obtain ⟨a, ha1, ha2, ha⟩ :=
    exists_root_Ioo l1 (mul_neg_of_neg_of_pos e1 e2)
  obtain ⟨b, hb1, hb2, hb⟩ :=
    exists_root_Ioo l2 (mul_neg_of_pos_of_neg e2 e3)
  obtain ⟨c, hc1, hc2, hc⟩ :=
    exists_root_Ioo l3 (mul_neg_of_neg_of_pos e3 e4)
  exact ⟨a, b, c, ha1, by linarith, by linarith, hc2, ha, hb, hc⟩

/-- Every row polynomial of OEIS A124848 splits over the reals. -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  have h0 : polynomial 0 = 1 := by
    norm_num [polynomial, coefficient]
  have h1 : polynomial 1 = 1 + C 4 * X := by
    norm_num [polynomial, coefficient, Finset.sum_range_succ]
  have h2 : polynomial 2 = 1 + C 8 * X + C 10 * X ^ 2 := by
    norm_num [polynomial, coefficient, Finset.sum_range_succ, Nat.choose]
  match n with
  | 0 =>
      rw [h0]
      exact splits_of_finset_roots_of_natDegree_le_card
        (s := ∅) (by simp) (by simp)
  | 1 =>
      rw [h1]
      refine splits_of_finset_roots_of_natDegree_le_card
        (s := {-1 / 4}) (by norm_num [Polynomial.IsRoot]) ?_
      simp only [Finset.card_singleton]
      compute_degree
  | 2 =>
      rw [h2]
      set p : ℝ[X] := 1 + C 8 * X + C 10 * X ^ 2 with hp
      have hev : ∀ x, p.eval x = 1 + 8 * x + 10 * x ^ 2 := by
        intro x
        simp [hp]
      obtain ⟨a, ha1, ha2, ha⟩ :=
        exists_root_Ioo (p := p) (a := -1) (b := -1 / 2)
          (by norm_num) (by rw [hev, hev]; norm_num)
      obtain ⟨b, hb1, hb2, hb⟩ :=
        exists_root_Ioo (p := p) (a := -1 / 2) (b := 0)
          (by norm_num) (by rw [hev, hev]; norm_num)
      refine splits_of_finset_roots_of_natDegree_le_card
        (p := p) (s := {a, b}) ?_ ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro x (rfl | rfl)
        · exact ha
        · exact hb
      · rw [Finset.card_pair (by linarith), hp]
        compute_degree
  | m + 3 =>
      rw [polynomial_add_three]
      obtain ⟨a, b, c, h1, hab, hbc, hc, ha, hb, hc'⟩ :=
        exists_three_roots_cubic m
      have hX : (1 + X : ℝ[X]).Splits := by
        refine splits_of_finset_roots_of_natDegree_le_card
          (s := {-1}) (by simp [Polynomial.IsRoot]) ?_
        simp only [Finset.card_singleton]
        compute_degree
      have hQ : (cubic ((m + 3 : ℕ) : ℝ)).Splits := by
        refine splits_of_finset_roots_of_natDegree_le_card
          (s := {a, b, c}) ?_ ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro x (rfl | rfl | rfl)
          · exact ha
          · exact hb
          · exact hc'
        · rw [Finset.card_insert_of_notMem
              (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                constructor <;> intro h <;> linarith),
            Finset.card_pair (by linarith)]
          unfold cubic
          compute_degree
      exact ((hX.pow m).C_mul _).mul hQ

/-- Every real root of an A124848 row belongs to `[-1, 0)`. -/
theorem roots_mem_Ico_polynomial (n : ℕ) {r : ℝ}
    (hr : (polynomial n).IsRoot r) : r ∈ Set.Ico (-1) 0 := by
  change -1 ≤ r ∧ r < 0
  match n with
  | 0 => norm_num [polynomial, coefficient, Polynomial.IsRoot] at hr
  | 1 =>
      norm_num [polynomial, coefficient, Finset.sum_range_succ,
        Polynomial.IsRoot] at hr
      constructor <;> nlinarith
  | 2 =>
      norm_num [polynomial, coefficient, Finset.sum_range_succ, Nat.choose,
        Polynomial.IsRoot] at hr
      constructor <;> nlinarith
  | m + 3 =>
      rw [polynomial_add_three] at hr
      simp only [Polynomial.IsRoot, eval_mul, eval_C, eval_pow, eval_add,
        eval_one, eval_X, eval_cubic] at hr
      set q : ℝ := ((m + 3 : ℕ) : ℝ) with hq
      have hq3 : (3 : ℝ) ≤ q := by
        rw [hq]
        push_cast
        linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
      have hpos : 0 < q * (q - 1) * (q - 2) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      constructor
      · by_contra h
        push Not at h
        have h1 : 1 + r < 0 := by linarith
        have hm : (1 + r) ^ m ≠ 0 := pow_ne_zero _ h1.ne
        have hcubic :
            q * (q - 1) * (q - 2) * r ^ 3 +
                9 * q * (q - 1) * r ^ 2 * (1 + r) +
                18 * q * r * (1 + r) ^ 2 + 6 * (1 + r) ^ 3 < 0 := by
          have t1 : r ^ 3 < 0 := Odd.pow_neg (by decide) (by linarith)
          have t2 : r ^ 2 * (1 + r) < 0 :=
            mul_neg_of_pos_of_neg (by nlinarith) h1
          have t3 : r * (1 + r) ^ 2 < 0 :=
            mul_neg_of_neg_of_pos (by linarith) (by nlinarith)
          have t4 : (1 + r) ^ 3 < 0 := Odd.pow_neg (by decide) h1
          have u2 : 0 < 9 * q * (q - 1) := by nlinarith
          nlinarith [mul_neg_of_pos_of_neg hpos t1,
            mul_neg_of_pos_of_neg u2 t2]
        have hne :
            (1 : ℝ) / 6 * (1 + r) ^ m *
                (q * (q - 1) * (q - 2) * r ^ 3 +
                  9 * q * (q - 1) * r ^ 2 * (1 + r) +
                  18 * q * r * (1 + r) ^ 2 + 6 * (1 + r) ^ 3) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hm) hcubic.ne
        exact hne hr
      · by_contra h
        push Not at h
        have hm : 0 < (1 + r) ^ m := by positivity
        have hcubic :
            0 < q * (q - 1) * (q - 2) * r ^ 3 +
                9 * q * (q - 1) * r ^ 2 * (1 + r) +
                18 * q * r * (1 + r) ^ 2 + 6 * (1 + r) ^ 3 := by
          have u2 : 0 < 9 * q * (q - 1) := by nlinarith
          have h3 : 0 < (1 + r) ^ 3 := by positivity
          have a1 : 0 ≤ q * (q - 1) * (q - 2) * r ^ 3 :=
            mul_nonneg hpos.le (by positivity)
          have a2 : 0 ≤ 9 * q * (q - 1) * r ^ 2 * (1 + r) := by
            have h2 : 0 ≤ r ^ 2 * (1 + r) := by positivity
            nlinarith
          have a3 : 0 ≤ 18 * q * r * (1 + r) ^ 2 := by
            have h2 : 0 ≤ r * (1 + r) ^ 2 := by positivity
            nlinarith
          linarith
        have hpositive :
            0 < (1 : ℝ) / 6 * (1 + r) ^ m *
                (q * (q - 1) * (q - 2) * r ^ 3 +
                  9 * q * (q - 1) * r ^ 2 * (1 + r) +
                  18 * q * r * (1 + r) ^ 2 + 6 * (1 + r) ^ 3) := by
          positivity
        linarith

end RealRooted.Applications.OEIS.A124848
