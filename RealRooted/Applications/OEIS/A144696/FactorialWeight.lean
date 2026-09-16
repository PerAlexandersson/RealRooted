import RealRooted.Analysis.FactorialTail
import RealRooted.Applications.OEIS.A144696.Basic

/-!
# A factorial-weight estimate for A144696 Bernstein images

This file evaluates the A144696 Bernstein images at one and rewrites the
successive-row comparison as a finite signed factorial sum. A strict
binomial-factorial ratio and the reciprocal-factorial tail estimate then make
that comparison positive.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted

/-- The binomial-factorial weight in the A144696 evaluation difference. -/
def a144696FactorialWeight (d k l : ℕ) : ℝ :=
  (Nat.choose (d - k - 1) l : ℝ) * (Nat.factorial (d + 1 - l) : ℝ)

/-- Evaluation at one of an A144696 Bernstein image. -/
theorem eval_one_a144696BernsteinImage (d k : ℕ) :
    (a144696BernsteinImage d k).eval 1 =
      ∑ i ∈ Finset.range (d - k + 1),
        (Nat.choose (d - k) i : ℝ) *
          (Nat.factorial (k + i + 2) : ℝ) / 2 := by
  rw [a144696BernsteinImage_eq_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [eval_one_a144696Polynomial]
  ring

/-- Reverse-index form of twice an A144696 Bernstein-image evaluation. -/
theorem two_mul_eval_one_a144696BernsteinImage
    {d k : ℕ} (hk : k ≤ d) :
    2 * (a144696BernsteinImage d k).eval 1 =
      ∑ l ∈ Finset.range (d - k + 1),
        (Nat.choose (d - k) l : ℝ) *
          (Nat.factorial (d - l + 2) : ℝ) := by
  rw [eval_one_a144696BernsteinImage, Finset.mul_sum]
  have hcancel :
      ∑ i ∈ Finset.range (d - k + 1),
          2 * ((Nat.choose (d - k) i : ℝ) *
            (Nat.factorial (k + i + 2) : ℝ) / 2) =
        ∑ i ∈ Finset.range (d - k + 1),
          (Nat.choose (d - k) i : ℝ) *
            (Nat.factorial (k + i + 2) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcancel]
  have hreflect := Finset.sum_range_reflect
    (fun i => (Nat.choose (d - k) i : ℝ) *
      (Nat.factorial (k + i + 2) : ℝ)) (d - k + 1)
  rw [← hreflect]
  apply Finset.sum_congr rfl
  intro l hl
  have hlm : l ≤ d - k := by
    have := Finset.mem_range.mp hl
    lia
  have hidx : d - k + 1 - 1 - l = d - k - l := by lia
  have hkm : k + (d - k - l) + 2 = d - l + 2 := by lia
  rw [hidx, Nat.choose_symm hlm, hkm]

/-- Exact factorial-weight form of the successive-row evaluation difference. -/
theorem a144696_eval_difference_eq_sum
    {d k : ℕ} (hk : k < d) :
    2 * ((a144696BernsteinImage d (k + 1)).eval 1 -
        (d + 1 : ℝ) * (a144696BernsteinImage (d - 1) k).eval 1) =
      ∑ l ∈ Finset.range (d - k),
        (1 - (l : ℝ)) * a144696FactorialWeight d k l := by
  have hg := two_mul_eval_one_a144696BernsteinImage
    (d := d) (k := k + 1) (by lia)
  have hh := two_mul_eval_one_a144696BernsteinImage
    (d := d - 1) (k := k) (by lia)
  have hm1 : d - (k + 1) = d - k - 1 := by lia
  have hm2 : d - 1 - k = d - k - 1 := by lia
  have hrange : d - k - 1 + 1 = d - k := by lia
  rw [hm1, hrange] at hg
  rw [hm2, hrange] at hh
  calc
    2 * ((a144696BernsteinImage d (k + 1)).eval 1 -
        (d + 1 : ℝ) * (a144696BernsteinImage (d - 1) k).eval 1) =
      2 * (a144696BernsteinImage d (k + 1)).eval 1 -
        (d + 1 : ℝ) *
          (2 * (a144696BernsteinImage (d - 1) k).eval 1) := by ring
    _ = (∑ l ∈ Finset.range (d - k),
          (Nat.choose (d - k - 1) l : ℝ) *
            (Nat.factorial (d - l + 2) : ℝ)) -
        (d + 1 : ℝ) *
          (∑ l ∈ Finset.range (d - k),
            (Nat.choose (d - k - 1) l : ℝ) *
              (Nat.factorial (d - 1 - l + 2) : ℝ)) := by rw [hg, hh]
    _ = ∑ l ∈ Finset.range (d - k),
        ((Nat.choose (d - k - 1) l : ℝ) *
            (Nat.factorial (d - l + 2) : ℝ) -
          (d + 1 : ℝ) *
            ((Nat.choose (d - k - 1) l : ℝ) *
              (Nat.factorial (d - 1 - l + 2) : ℝ))) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlrange : l < d - k := Finset.mem_range.mp hl
      have hfacidx : d - l + 2 = (d + 1 - l) + 1 := by lia
      have hfacidx' : d - 1 - l + 2 = d + 1 - l := by lia
      rw [hfacidx, hfacidx', Nat.factorial_succ]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        a144696FactorialWeight]
      rw [Nat.cast_sub (by lia : l ≤ d + 1)]
      push_cast
      ring

/-- Every positive nonzero A144696 factorial weight is strictly smaller than
the head weight divided by `l!`. -/
theorem a144696FactorialWeight_ratio_lt
    {d k l : ℕ} (hl : 0 < l) (hln : l ≤ d - k - 1) :
    a144696FactorialWeight d k l / a144696FactorialWeight d k 0 <
      1 / (Nat.factorial l : ℝ) := by
  have hratio := factorialWeight_ratio_lt
    (n := d - k - 1) (m := d + 1) (l := l) (by lia) hl hln
  simpa [a144696FactorialWeight] using hratio

private theorem sum_one_sub_mul_eq_head_sub_tail
    (m : ℕ) (W : ℕ → ℝ) :
    ∑ l ∈ Finset.range (m + 1), (1 - (l : ℝ)) * W l =
      W 0 - ∑ l ∈ Finset.Icc 2 m, ((l : ℝ) - 1) * W l := by
  by_cases hm : 2 ≤ m
  swap
  · have hmle : m ≤ 1 := by lia
    interval_cases m <;> simp [Finset.sum_range_succ]
  rw [Nat.range_succ_eq_Icc_zero]
  have hzero : insert 0 (Finset.Icc 1 m) = Finset.Icc 0 m := by
    simpa using Finset.insert_Icc_succ_left_eq_Icc (by lia : 0 ≤ m)
  have hone : insert 1 (Finset.Icc 2 m) = Finset.Icc 1 m := by
    simpa using Finset.insert_Icc_succ_left_eq_Icc (by lia : 1 ≤ m)
  rw [← hzero, Finset.sum_insert (by simp), ← hone,
    Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, sub_zero, one_mul, Nat.cast_one, sub_self, zero_mul,
    zero_add]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  apply congrArg (W 0 + ·)
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- The negative factorial-weight tail is strictly smaller than its positive
head term. -/
theorem a144696_factorialTail_lt_head (d k : ℕ) :
    ∑ l ∈ Finset.Icc 2 (d - k - 1),
        ((l : ℝ) - 1) * a144696FactorialWeight d k l <
      a144696FactorialWeight d k 0 := by
  let m := d - k - 1
  have hhead : 0 < a144696FactorialWeight d k 0 := by
    have hfac : 0 < (Nat.factorial (d + 1) : ℝ) := by positivity
    simpa [a144696FactorialWeight] using hfac
  by_cases hm : 2 ≤ m
  · have hterm : ∀ l ∈ Finset.Icc 2 m,
        (((l : ℝ) - 1) * a144696FactorialWeight d k l) /
            a144696FactorialWeight d k 0 <
          ((l : ℝ) - 1) / (Nat.factorial l : ℝ) := by
      intro l hlmem
      have hlbounds := Finset.mem_Icc.mp hlmem
      have hratio := a144696FactorialWeight_ratio_lt
        (d := d) (k := k) (l := l) (by lia) (by simpa [m] using hlbounds.2)
      have hlR : (1 : ℝ) < (l : ℝ) := by
        exact_mod_cast (show 1 < l by lia)
      have hpos : 0 < (l : ℝ) - 1 := by linarith
      calc
        (((l : ℝ) - 1) * a144696FactorialWeight d k l) /
            a144696FactorialWeight d k 0 =
          ((l : ℝ) - 1) *
            (a144696FactorialWeight d k l /
              a144696FactorialWeight d k 0) := by ring
        _ < ((l : ℝ) - 1) * (1 / (Nat.factorial l : ℝ)) :=
          mul_lt_mul_of_pos_left hratio hpos
        _ = ((l : ℝ) - 1) / (Nat.factorial l : ℝ) := by ring
    have hnonempty : (Finset.Icc 2 m).Nonempty := ⟨2, by simp [hm]⟩
    have hsums := Finset.sum_lt_sum_of_nonempty hnonempty hterm
    have htail := sum_Icc_factorialTail_lt_one m
    have hdiv :
        (∑ l ∈ Finset.Icc 2 m,
            ((l : ℝ) - 1) * a144696FactorialWeight d k l) /
            a144696FactorialWeight d k 0 < 1 := by
      rw [Finset.sum_div]
      exact hsums.trans htail
    simpa [m] using (div_lt_one hhead).mp hdiv
  · have hempty : Finset.Icc 2 m = ∅ := by
      ext l
      simp
      lia
    rw [show d - k - 1 = m by rfl, hempty]
    simpa using hhead

/-- The signed factorial-weight sum for the A144696 comparison is positive. -/
theorem a144696_weighted_sum_pos
    {d k : ℕ} (hk : k < d) :
    0 < ∑ l ∈ Finset.range (d - k),
      (1 - (l : ℝ)) * a144696FactorialWeight d k l := by
  let m := d - k - 1
  have hrange : d - k = m + 1 := by
    dsimp [m]
    lia
  rw [hrange, sum_one_sub_mul_eq_head_sub_tail]
  have htail := a144696_factorialTail_lt_head d k
  change
    ∑ l ∈ Finset.Icc 2 m,
        ((l : ℝ) - 1) * a144696FactorialWeight d k l <
      a144696FactorialWeight d k 0 at htail
  linarith

/-- Strict endpoint comparison for adjacent A144696 Bernstein-image rows. -/
theorem a144696_eval_gap_pos
    {d k : ℕ} (hk : k < d) :
    (d + 1 : ℝ) * (a144696BernsteinImage (d - 1) k).eval 1 <
      (a144696BernsteinImage d (k + 1)).eval 1 := by
  have hsum := a144696_weighted_sum_pos (d := d) (k := k) hk
  have heq := a144696_eval_difference_eq_sum (d := d) (k := k) hk
  nlinarith

end RealRooted
