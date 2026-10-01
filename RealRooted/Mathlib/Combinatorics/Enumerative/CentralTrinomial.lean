import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Central trinomial coefficients

The central trinomial coefficient `Nat.centralTrinomial n` is the middle
coefficient of `(1 + X + X ^ 2) ^ n` (OEIS A002426).  We define it by the
finite binomial sum `∑ i, (n choose 2i) (2i choose i)`, which chooses the
`2i` positions of the non-constant factors and then which `i` of them are
`X ^ 2`.

## Main results

* `Nat.cast_centralTrinomial_eq_sum_factorial`: the guarded factorial form
  `∑ i, n! / (i! ^ 2 (n - 2i)!)`.
* `Nat.cast_centralTrinomial_two_mul_add_eq_sum_antidiagonal`: the same
  factorial form written over a single antidiagonal, for either parity.
* `Nat.centralTrinomial_succ_succ`: the holonomic recurrence
  `(n + 2) T(n + 2) = (2n + 3) T(n + 1) + 3 (n + 1) T(n)`, proved by an
  explicit finite telescoping certificate.
* `Nat.eq_centralTrinomial_of_recurrence`: in characteristic zero, the initial
  values `1, 1` and this recurrence determine the sequence.
-/

open Finset

namespace Nat

/-- The central trinomial coefficient, the middle coefficient of
`(1 + X + X ^ 2) ^ n`, as a finite binomial sum. -/
def centralTrinomial (n : ℕ) : ℕ :=
  ∑ i ∈ range (n + 1), n.choose (2 * i) * (2 * i).choose i

@[simp]
theorem centralTrinomial_zero : centralTrinomial 0 = 1 := by
  simp [centralTrinomial]

@[simp]
theorem centralTrinomial_one : centralTrinomial 1 = 1 := by
  simp [centralTrinomial, sum_range_succ]

theorem centralTrinomial_two : centralTrinomial 2 = 3 := by
  decide

namespace CentralTrinomial

/-- The factorial-form summand, with its support condition made explicit. -/
private noncomputable def F (n k : ℕ) : ℝ :=
  if 2 * k ≤ n then
    (n.factorial : ℝ) / ((k.factorial : ℝ) ^ 2 * ((n - 2 * k).factorial : ℝ))
  else 0

/-- The finite telescoping certificate. -/
private noncomputable def G (n k : ℕ) : ℝ :=
  if 2 * k ≤ n + 2 then
    -4 * ((n : ℝ) + 1) * (k : ℝ) ^ 2 * (n.factorial : ℝ) /
      ((k.factorial : ℝ) ^ 2 * ((n + 2 - 2 * k).factorial : ℝ))
  else 0

/-! ### Factorial form -/

private theorem choose_mul_choose_eq_F (n i : ℕ) :
    (n.choose (2 * i) : ℝ) * ((2 * i).choose i : ℝ) = F n i := by
  unfold F
  by_cases h : 2 * i ≤ n
  · rw [ite_eq_left h, eq_div_iff (by positivity)]
    have h2 : ((2 * i).choose i : ℝ) * (i.factorial : ℝ) ^ 2 =
        ((2 * i).factorial : ℝ) := by
      have h2' := Nat.choose_mul_factorial_mul_factorial (show i ≤ 2 * i by lia)
      rw [show 2 * i - i = i from by lia] at h2'
      have h2'' : (((2 * i).choose i * i.factorial * i.factorial : ℕ) : ℝ) =
          (((2 * i).factorial : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h2'
      push_cast at h2''
      rw [← h2'']
      ring
    have h1 : (n.choose (2 * i) : ℝ) * ((2 * i).factorial : ℝ) *
        ((n - 2 * i).factorial : ℝ) = (n.factorial : ℝ) := by
      have h1' := Nat.choose_mul_factorial_mul_factorial h
      have h1'' :
          ((n.choose (2 * i) * (2 * i).factorial * (n - 2 * i).factorial : ℕ) : ℝ) =
            ((n.factorial : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h1'
      push_cast at h1''
      rw [← h1'']
    rw [← h1, ← h2]
    ring
  · rw [ite_eq_right h, Nat.choose_eq_zero_of_lt (by lia)]
    push_cast
    ring

private theorem F_eq_zero_of_lt {n k : ℕ} (h : n < 2 * k) : F n k = 0 :=
  ite_eq_right (by lia)

/-! ### Pointwise telescoping identity -/

private theorem key_main {k m : ℕ} :
    ((2 * k + m : ℕ) + 2 : ℝ) * F (2 * k + m + 2) k
        - (2 * ((2 * k + m : ℕ) : ℝ) + 3) * F (2 * k + m + 1) k
        - 3 * (((2 * k + m : ℕ) : ℝ) + 1) * F (2 * k + m) k
      = G (2 * k + m) (k + 1) - G (2 * k + m) k := by
  unfold F G
  rw [ite_eq_left (show 2 * k ≤ 2 * k + m + 2 by lia),
    ite_eq_left (show 2 * k ≤ 2 * k + m + 1 by lia),
    ite_eq_left (show 2 * k ≤ 2 * k + m by lia),
    ite_eq_left (show 2 * (k + 1) ≤ 2 * k + m + 2 by lia),
    ite_eq_left (show 2 * k ≤ 2 * k + m + 2 by lia),
    show 2 * k + m + 2 - 2 * k = m + 2 from by lia,
    show 2 * k + m + 1 - 2 * k = m + 1 from by lia,
    show 2 * k + m - 2 * k = m from by lia,
    show 2 * k + m + 2 - 2 * (k + 1) = m from by lia]
  have e1 : (((2 * k + m + 1).factorial : ℕ) : ℝ) =
      (2 * (k : ℝ) + m + 1) * (((2 * k + m).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e2 : (((2 * k + m + 2).factorial : ℕ) : ℝ) =
      (2 * (k : ℝ) + m + 2) * (2 * (k : ℝ) + m + 1) *
        (((2 * k + m).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ (2 * k + m + 1), Nat.factorial_succ (2 * k + m)]
    push_cast
    ring
  have e3 : (((m + 1).factorial : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e4 : (((m + 2).factorial : ℕ) : ℝ) =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * ((m.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
    push_cast
    ring
  have e5 : (((k + 1).factorial : ℕ) : ℝ) =
      ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [e1, e2, e3, e4, e5]
  push_cast
  field_simp
  ring

private theorem key_edge_one {j : ℕ} :
    ((2 * j + 1 : ℕ) + 2 : ℝ) * F (2 * j + 1 + 2) (j + 1)
        - (2 * ((2 * j + 1 : ℕ) : ℝ) + 3) * F (2 * j + 1 + 1) (j + 1)
        - 3 * (((2 * j + 1 : ℕ) : ℝ) + 1) * F (2 * j + 1) (j + 1)
      = G (2 * j + 1) (j + 1 + 1) - G (2 * j + 1) (j + 1) := by
  unfold F G
  rw [ite_eq_left (show 2 * (j + 1) ≤ 2 * j + 1 + 2 by lia),
    ite_eq_left (show 2 * (j + 1) ≤ 2 * j + 1 + 1 by lia),
    ite_eq_right (show ¬ 2 * (j + 1) ≤ 2 * j + 1 by lia),
    ite_eq_right (show ¬ 2 * (j + 1 + 1) ≤ 2 * j + 1 + 2 by lia),
    ite_eq_left (show 2 * (j + 1) ≤ 2 * j + 1 + 2 by lia),
    show 2 * j + 1 + 2 - 2 * (j + 1) = 1 from by lia,
    show 2 * j + 1 + 1 - 2 * (j + 1) = 0 from by lia]
  have e1 : (((2 * j + 1 + 1).factorial : ℕ) : ℝ) =
      (2 * (j : ℝ) + 2) * (((2 * j + 1).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e2 : (((2 * j + 1 + 2).factorial : ℕ) : ℝ) =
      (2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 2) *
        (((2 * j + 1).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ (2 * j + 1 + 1), Nat.factorial_succ (2 * j + 1)]
    push_cast
    ring
  rw [e1, e2]
  push_cast [Nat.factorial]
  field_simp
  ring

private theorem key_edge_two {j : ℕ} :
    ((2 * j : ℕ) + 2 : ℝ) * F (2 * j + 2) (j + 1)
        - (2 * ((2 * j : ℕ) : ℝ) + 3) * F (2 * j + 1) (j + 1)
        - 3 * (((2 * j : ℕ) : ℝ) + 1) * F (2 * j) (j + 1)
      = G (2 * j) (j + 1 + 1) - G (2 * j) (j + 1) := by
  unfold F G
  rw [ite_eq_left (show 2 * (j + 1) ≤ 2 * j + 2 by lia),
    ite_eq_right (show ¬ 2 * (j + 1) ≤ 2 * j + 1 by lia),
    ite_eq_right (show ¬ 2 * (j + 1) ≤ 2 * j by lia),
    ite_eq_right (show ¬ 2 * (j + 1 + 1) ≤ 2 * j + 2 by lia),
    ite_eq_left (show 2 * (j + 1) ≤ 2 * j + 2 by lia),
    show 2 * j + 2 - 2 * (j + 1) = 0 from by lia]
  have e2 : (((2 * j + 2).factorial : ℕ) : ℝ) =
      (2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 1) *
        (((2 * j).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j)]
    push_cast
    ring
  rw [e2]
  push_cast [Nat.factorial]
  field_simp
  ring

private theorem key (n k : ℕ) :
    ((n : ℝ) + 2) * F (n + 2) k - (2 * (n : ℝ) + 3) * F (n + 1) k
        - 3 * ((n : ℝ) + 1) * F n k
      = G n (k + 1) - G n k := by
  by_cases h1 : 2 * k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * k + m := ⟨n - 2 * k, by lia⟩
    have hmain := @key_main k m
    push_cast at hmain ⊢
    linarith [hmain]
  · by_cases h2 : 2 * k ≤ n + 2
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
      by_cases h3 : 2 * (j + 1) ≤ n + 1
      · obtain rfl : n = 2 * j + 1 := by lia
        have hedge := @key_edge_one j
        push_cast at hedge ⊢
        linarith [hedge]
      · obtain rfl : n = 2 * j := by lia
        have hedge := @key_edge_two j
        push_cast at hedge ⊢
        linarith [hedge]
    · unfold F G
      rw [ite_eq_right (show ¬ 2 * k ≤ n + 2 by lia),
        ite_eq_right (show ¬ 2 * k ≤ n + 1 by lia),
        ite_eq_right (show ¬ 2 * k ≤ n by lia),
        ite_eq_right (show ¬ 2 * (k + 1) ≤ n + 2 by lia),
        ite_eq_right (show ¬ 2 * k ≤ n + 2 by lia)]
      ring

end CentralTrinomial

open CentralTrinomial

private theorem cast_centralTrinomial_eq_sum_F (n : ℕ) :
    (centralTrinomial n : ℝ) = ∑ i ∈ range (n + 1), F n i := by
  rw [centralTrinomial, Nat.cast_sum]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Nat.cast_mul]
  exact choose_mul_choose_eq_F n i

/-- The guarded factorial form of the central trinomial coefficient. -/
theorem cast_centralTrinomial_eq_sum_factorial (n : ℕ) :
    (centralTrinomial n : ℝ) = ∑ i ∈ range (n + 1),
      if 2 * i ≤ n then
        (n.factorial : ℝ) /
          ((i.factorial : ℝ) ^ 2 * ((n - 2 * i).factorial : ℝ))
      else 0 :=
  cast_centralTrinomial_eq_sum_F n

private theorem cast_centralTrinomial_eq_sum_F_range {n M : ℕ} (h : n + 1 ≤ M) :
    (centralTrinomial n : ℝ) = ∑ i ∈ range M, F n i := by
  rw [cast_centralTrinomial_eq_sum_F]
  have hsub : range (n + 1) ⊆ range M :=
    range_subset.2 (fun x hx => mem_range.2 (by lia))
  refine sum_subset hsub (fun x _ hx => ?_)
  exact F_eq_zero_of_lt (by simp only [mem_range, not_lt] at hx; lia)

private theorem G_zero (n : ℕ) : G n 0 = 0 := by
  unfold G
  rw [ite_eq_left (by lia)]
  norm_num

private theorem G_top (n : ℕ) : G n (n + 3) = 0 := ite_eq_right (by lia)

private theorem cast_centralTrinomial_succ_succ (n : ℕ) :
    ((n : ℝ) + 2) * centralTrinomial (n + 2) =
      (2 * (n : ℝ) + 3) * centralTrinomial (n + 1) +
        3 * ((n : ℝ) + 1) * centralTrinomial n := by
  have hsum : ∑ k ∈ range (n + 3), (G n (k + 1) - G n k) = 0 := by
    rw [sum_range_sub (fun k => G n k) (n + 3), G_top, G_zero, sub_zero]
  have h2 : (centralTrinomial (n + 2) : ℝ) = ∑ k ∈ range (n + 3), F (n + 2) k :=
    cast_centralTrinomial_eq_sum_F_range (le_refl (n + 3))
  have h1 : (centralTrinomial (n + 1) : ℝ) = ∑ k ∈ range (n + 3), F (n + 1) k :=
    cast_centralTrinomial_eq_sum_F_range (by lia)
  have h0 : (centralTrinomial n : ℝ) = ∑ k ∈ range (n + 3), F n k :=
    cast_centralTrinomial_eq_sum_F_range (by lia)
  have expand : ((n : ℝ) + 2) * centralTrinomial (n + 2) -
      (2 * (n : ℝ) + 3) * centralTrinomial (n + 1) -
        3 * ((n : ℝ) + 1) * centralTrinomial n =
        ∑ k ∈ range (n + 3), (G n (k + 1) - G n k) := by
    rw [h0, h1, h2, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib,
      ← sum_sub_distrib]
    exact sum_congr rfl (fun k _ => key n k)
  rw [hsum] at expand
  linarith [expand]

/-- The holonomic recurrence of the central trinomial coefficients. -/
theorem centralTrinomial_succ_succ (n : ℕ) :
    (n + 2) * centralTrinomial (n + 2) =
      (2 * n + 3) * centralTrinomial (n + 1) + 3 * (n + 1) * centralTrinomial n := by
  exact_mod_cast cast_centralTrinomial_succ_succ n

/-- In characteristic zero, a sequence with the initial values `1, 1` and the
central trinomial recurrence is the sequence of central trinomial
coefficients. -/
theorem eq_centralTrinomial_of_recurrence {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (hrec : ∀ n : ℕ, ((n : K) + 2) * a (n + 2) =
      (2 * (n : K) + 3) * a (n + 1) + 3 * ((n : K) + 1) * a n) (n : ℕ) :
    a n = centralTrinomial n := by
  have main : ∀ n : ℕ, a n = centralTrinomial n ∧
      a (n + 1) = centralTrinomial (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [h0], by simp [h1]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hne : ((n : K) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (n + 1))
      have hcast : ((n : K) + 2) * (centralTrinomial (n + 2) : K) =
          (2 * (n : K) + 3) * centralTrinomial (n + 1) +
            3 * ((n : K) + 1) * centralTrinomial n := by
        exact_mod_cast centralTrinomial_succ_succ n
      have hrec' := hrec n
      rw [ih.1, ih.2, ← hcast] at hrec'
      exact mul_left_cancel₀ hne hrec'
  exact (main n).1

/-- The factorial form of the central trinomial coefficient on a single
antidiagonal, for either parity of the index. -/
theorem cast_centralTrinomial_two_mul_add_eq_sum_antidiagonal (q e : ℕ) (he : e ≤ 1) :
    (centralTrinomial (2 * q + e) : ℝ) =
      ∑ ij ∈ antidiagonal q,
        ((2 * q + e).factorial : ℝ) /
          ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2 + e).factorial : ℝ)) := by
  rw [cast_centralTrinomial_eq_sum_factorial]
  have hsub : range (q + 1) ⊆ range (2 * q + e + 1) :=
    range_subset_range.mpr (by lia)
  calc
    ∑ i ∈ range (2 * q + e + 1),
        (if 2 * i ≤ 2 * q + e then
          ((2 * q + e).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * q + e - 2 * i).factorial : ℝ))
        else 0) =
        ∑ i ∈ range (q + 1),
          (if 2 * i ≤ 2 * q + e then
            ((2 * q + e).factorial : ℝ) /
              ((i.factorial : ℝ) ^ 2 * ((2 * q + e - 2 * i).factorial : ℝ))
          else 0) := by
      symm
      refine sum_subset hsub ?_
      intro i _ hi
      rw [ite_eq_right ?_]
      simp only [mem_range, not_lt] at hi
      lia
    _ = ∑ i ∈ range (q + 1),
          ((2 * q + e).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * (q - i) + e).factorial : ℝ)) := by
      refine sum_congr rfl ?_
      intro i hi
      have hiq : i ≤ q := by
        simpa only [mem_range, Nat.lt_succ_iff] using hi
      have hsupport : 2 * i ≤ 2 * q + e := by lia
      have hindex : 2 * q + e - 2 * i = 2 * (q - i) + e := by lia
      rw [ite_eq_left hsupport, hindex]
    _ = ∑ ij ∈ antidiagonal q,
          ((2 * q + e).factorial : ℝ) /
            ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2 + e).factorial : ℝ)) := by
      symm
      simpa only [Nat.succ_eq_add_one] using
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => ((2 * q + e).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * j + e).factorial : ℝ))) q)

end Nat
