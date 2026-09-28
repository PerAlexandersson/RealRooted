import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# Real rising and falling factorials

This file fixes the real Pochhammer notation used throughout the Jacobi
deformation: `risingFactorial a n = a (a + 1) ⋯ (a + n - 1)` and
`fallingFactorial a n = a (a - 1) ⋯ (a - n + 1)`, defined as evaluations of
Mathlib's `ascPochhammer` and `descPochhammer`.  Besides the elementary
splitting, reflection, and natural-argument identities, it proves three
terminating hypergeometric summations:

* the Chu--Vandermonde convolution for rising and for falling factorials;
* its alternating terminating form `chu_vandermonde_terminating`; and
* the Pfaff--Saalschütz identity in denominator-free form,
  `risingFactorial_pfaffSaalschutz`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.4.24 and
  16.4.3.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The real rising factorial `(a)_n`, using Mathlib's `ascPochhammer`. -/
def risingFactorial (a : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval a

/-- The real falling factorial, using Mathlib's `descPochhammer`. -/
def fallingFactorial (a : ℝ) (n : ℕ) : ℝ :=
  (descPochhammer ℝ n).eval a

@[simp]
theorem risingFactorial_zero (a : ℝ) : risingFactorial a 0 = 1 := by
  simp [risingFactorial]

@[simp]
theorem risingFactorial_one (a : ℝ) : risingFactorial a 1 = a := by
  simp [risingFactorial]

@[simp]
theorem fallingFactorial_zero (a : ℝ) : fallingFactorial a 0 = 1 := by
  simp [fallingFactorial]

theorem risingFactorial_succ (a : ℝ) (n : ℕ) :
    risingFactorial a (n + 1) = risingFactorial a n * (a + n) := by
  simpa [risingFactorial] using ascPochhammer_succ_eval n a

theorem fallingFactorial_succ (a : ℝ) (n : ℕ) :
    fallingFactorial a (n + 1) = fallingFactorial a n * (a - n) := by
  simpa [fallingFactorial] using descPochhammer_succ_eval n a

theorem risingFactorial_eq_prod (a : ℝ) (n : ℕ) :
    risingFactorial a n = ∏ l ∈ range n, (a + (l : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [risingFactorial_succ, ih, prod_range_succ]

theorem fallingFactorial_eq_prod (a : ℝ) (n : ℕ) :
    fallingFactorial a n = ∏ l ∈ range n, (a - (l : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [fallingFactorial_succ, ih, prod_range_succ]

theorem risingFactorial_pos {a : ℝ} (n : ℕ) (ha : 0 < a) :
    0 < risingFactorial a n := by
  simpa [risingFactorial] using ascPochhammer_pos n a ha

/-- Splitting a rising factorial at a natural-number offset. -/
theorem risingFactorial_add (a : ℝ) (m n : ℕ) :
    risingFactorial a (m + n) = risingFactorial a m * risingFactorial (a + m) n := by
  have h := congrArg (fun p : ℝ[X] => p.eval a) (ascPochhammer_mul ℝ m n)
  simpa [risingFactorial] using h.symm

/-- A rising factorial is a falling factorial read from the other end. -/
theorem risingFactorial_eq_fallingFactorial (a : ℝ) (n : ℕ) :
    risingFactorial a n = fallingFactorial (a + n - 1) n := by
  rw [fallingFactorial, descPochhammer_eval_eq_ascPochhammer, risingFactorial]
  congr 1
  ring

theorem neg_one_pow_mul_risingFactorial (a : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n * risingFactorial a n = fallingFactorial (-a) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [risingFactorial_succ, fallingFactorial_succ, pow_succ, ← ih]
    ring

/-- Reflection: `(-a)^(n rising) = (-1)^n a^(n falling)`. -/
theorem risingFactorial_neg (a : ℝ) (n : ℕ) :
    risingFactorial (-a) n = (-1) ^ n * fallingFactorial a n := by
  rw [← neg_neg a, ← neg_one_pow_mul_risingFactorial, neg_neg, ← mul_assoc, ← mul_pow]
  norm_num

/-- Reversing a rising factorial. -/
theorem risingFactorial_one_sub (a : ℝ) (n : ℕ) :
    risingFactorial (1 - a - n) n = (-1) ^ n * risingFactorial a n := by
  rw [risingFactorial_eq_fallingFactorial, risingFactorial_eq_fallingFactorial,
    show 1 - a - (n : ℝ) + n - 1 = -a by ring, ← neg_one_pow_mul_risingFactorial,
    ← risingFactorial_eq_fallingFactorial]

theorem fallingFactorial_natCast (k n : ℕ) :
    fallingFactorial (k : ℝ) n = (k.descFactorial n : ℝ) := by
  simpa [fallingFactorial] using descPochhammer_eval_eq_descFactorial ℝ k n

theorem fallingFactorial_natCast_eq_zero_of_lt {k n : ℕ} (hkn : k < n) :
    fallingFactorial (k : ℝ) n = 0 := by
  rw [fallingFactorial_natCast, Nat.descFactorial_eq_zero_iff_lt.mpr hkn]
  simp

/-- A falling factorial at a natural number, in terms of a binomial coefficient. -/
theorem choose_mul_factorial_eq_fallingFactorial (j k : ℕ) :
    (j.choose k : ℝ) * (k.factorial : ℝ) = fallingFactorial (j : ℝ) k := by
  rw [fallingFactorial_natCast, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- Rising factorials at a negative integer. -/
theorem risingFactorial_neg_natCast (m n : ℕ) :
    risingFactorial (-(m : ℝ)) n = (-1 : ℝ) ^ n * (m.descFactorial n : ℝ) := by
  rw [risingFactorial_neg, fallingFactorial_natCast]

/-- Shifting the base of a rising factorial by one. -/
theorem mul_risingFactorial_add_one (a : ℝ) (n : ℕ) :
    a * risingFactorial (a + 1) n =
      (a + n) * risingFactorial a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [risingFactorial_succ, risingFactorial_succ]
      push_cast
      linear_combination (a + (n : ℝ) + 1) * ih

/-- The tail of a rising factorial is the matching descending Pochhammer
evaluation. -/
theorem risingFactorial_sub_mul_descPochhammer (δ : ℝ) {m j : ℕ} (hjm : j ≤ m) :
    risingFactorial δ (m - j) *
        (descPochhammer ℝ j).eval ((m : ℝ) + δ - 1) =
      risingFactorial δ m := by
  rw [descPochhammer_eval_eq_ascPochhammer]
  have harg : (m : ℝ) + δ - 1 - (j : ℝ) + 1 = δ + ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hjm]
    ring
  rw [harg]
  simpa [risingFactorial, Nat.sub_add_cancel hjm] using
    (risingFactorial_add δ (m - j) j).symm

/-! ## Chu--Vandermonde -/

/-- Chu–Vandermonde convolution for risingFactorial factorials. -/
theorem risingFactorial_add_eq_sum_range (x y : ℝ) (n : ℕ) :
    risingFactorial (x + y) n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (risingFactorial x k * risingFactorial y (n - k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [risingFactorial_succ, ih]
    have step1 :
        (∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (risingFactorial x k * risingFactorial y (n - k))) *
            (x + y + (n : ℝ)) =
          (∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (risingFactorial x (k + 1) * risingFactorial y (n - k))) +
          ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (risingFactorial x k * risingFactorial y (n + 1 - k)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      have hnk : n + 1 - k = (n - k) + 1 := by lia
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
        push_cast [Nat.cast_sub hk]; ring
      rw [hnk, risingFactorial_succ, risingFactorial_succ, hcast]
      ring
    rw [step1]
    have hA' :
        ∑ k ∈ Finset.range (n + 1),
          (n.choose (k + 1) : ℝ) * (risingFactorial x (k + 1) * risingFactorial y (n - k)) =
        ∑ k ∈ Finset.range n,
          (n.choose (k + 1) : ℝ) * (risingFactorial x (k + 1) * risingFactorial y (n - k)) := by
      rw [Finset.sum_range_succ]
      simp
    have hB :
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * (risingFactorial x k * risingFactorial y (n + 1 - k)) =
        (∑ k ∈ Finset.range n,
          (n.choose (k + 1) : ℝ) * (risingFactorial x (k + 1) * risingFactorial y (n - k)))
          + risingFactorial y (n + 1) := by
      rw [Finset.sum_range_succ']
      simp
    rw [hB, ← hA', Finset.sum_range_succ'
      (fun k => ((n + 1).choose k : ℝ) * (risingFactorial x k * risingFactorial y (n + 1 -
          k))) (n + 1)]
    simp only [Nat.choose_succ_succ, Nat.succ_sub_succ, Nat.cast_add, add_mul,
      Finset.sum_add_distrib, Nat.choose_zero_right, Nat.cast_one, one_mul, risingFactorial_zero,
      Nat.succ_eq_add_one, Nat.sub_zero]
    ring

/-- Vandermonde's identity for fallingFactorial factorials:
`∑_{i=0}^{j} C(j,i) * fallingFactorial u i * fallingFactorial v (j-i) = fallingFactorial (u+v) j`.
-/
theorem sum_range_choose_mul_fallingFactorial_mul_fallingFactorial (u v : ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * fallingFactorial u i * fallingFactorial v (j - i)
      = fallingFactorial (u + v) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ez : ∑ i ∈ Finset.range (j + 1), (j.choose (i + 1) : ℝ) * fallingFactorial u (i + 1)
          * fallingFactorial v (j - i)
        = ∑ i ∈ Finset.range j, (j.choose (i + 1) : ℝ) * fallingFactorial u (i + 1)
          * fallingFactorial v (j - i) := by
      rw [Finset.sum_range_succ]
      simp
    have e1 : ∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ) * fallingFactorial u i
          * fallingFactorial v (j + 1 - i)
        = (∑ i ∈ Finset.range (j + 1),
            ((j + 1).choose (i + 1) : ℝ) * fallingFactorial u (i + 1)
            * fallingFactorial v (j - i)) + fallingFactorial v (j + 1) := by
      rw [Finset.sum_range_succ' (fun i => ((j + 1).choose i : ℝ) * fallingFactorial u i
        * fallingFactorial v (j + 1 - i)) (j + 1)]
      simp
    have e2 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u i *
        fallingFactorial v (j + 1 - i)
        = (∑ i ∈ Finset.range (j + 1), (j.choose (i + 1) : ℝ) * fallingFactorial u (i + 1)
            * fallingFactorial v (j - i)) + fallingFactorial v (j + 1) := by
      rw [ez, Finset.sum_range_succ' (fun i => (j.choose i : ℝ) * fallingFactorial u i
        * fallingFactorial v (j + 1 - i)) j]
      simp
    have e3 : ∑ i ∈ Finset.range (j + 1),
        ((j + 1).choose (i + 1) : ℝ) * fallingFactorial u (i + 1)
          * fallingFactorial v (j - i)
        = (∑ i ∈ Finset.range (j + 1), (j.choose (i + 1) : ℝ) * fallingFactorial u (i + 1)
            * fallingFactorial v (j - i))
          + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u (i + 1)
            * fallingFactorial v (j - i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hc : ((j + 1).choose (i + 1) : ℝ) = (j.choose i : ℝ) + (j.choose (i + 1) : ℝ) := by
        push_cast [Nat.choose_succ_succ j i]
        ring
      rw [hc]
      ring
    have key : ∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ) * fallingFactorial u i
          * fallingFactorial v (j + 1 - i)
        = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u i *
            fallingFactorial v (j + 1 - i))
          + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u (i + 1)
            * fallingFactorial v (j - i) := by
      rw [e1, e3, e2]
      ring
    rw [key]
    have hA : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u i *
        fallingFactorial v (j + 1 - i)
        = ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * fallingFactorial u i * fallingFactorial v (j - i)) *
            (v - ((j : ℝ) - (i : ℝ))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mem_range] at hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp hi
      have h1 : j + 1 - i = (j - i) + 1 := by lia
      have h2 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
        push_cast [Nat.cast_sub hij]; ring
      rw [h1, fallingFactorial_succ, h2]
      ring
    have hB : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u (i + 1) *
        fallingFactorial v (j - i)
        = ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * fallingFactorial u i * fallingFactorial v (j - i)) * (u -
              (i : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [fallingFactorial_succ]
      ring
    have hsum : ∑ i ∈ Finset.range (j + 1),
        (((j.choose i : ℝ) * fallingFactorial u i * fallingFactorial v (j - i)) *
            (v - ((j : ℝ) - (i : ℝ)))
          + ((j.choose i : ℝ) * fallingFactorial u i * fallingFactorial v (j - i)) *
            (u - (i : ℝ)))
        = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * fallingFactorial u i *
            fallingFactorial v (j - i))
            * (u + v - (j : ℝ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hA, hB, ← Finset.sum_add_distrib, hsum, ih, fallingFactorial_succ]

/-- The general terminating Chu–Vandermonde sum, with denominators cleared:
`∑_{i=0}^{j} (-1)^i C(j,i) risingFactorial a i * risingFactorial (b+i) (j-i) =
risingFactorial (b - a) j`. -/
theorem sum_range_neg_one_pow_mul_choose_mul_risingFactorial (a b : ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ) * risingFactorial a i
        * risingFactorial (b + (i : ℝ)) (j - i)
      = risingFactorial (b - a) j := by
  have h := sum_range_choose_mul_fallingFactorial_mul_fallingFactorial (-a) (b + (j : ℝ) - 1) j
  have hb : (-a) + (b + (j : ℝ) - 1) = (b - a) + (j : ℝ) - 1 := by ring
  rw [hb, ← risingFactorial_eq_fallingFactorial] at h
  rw [← h]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mem_range] at hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp hi
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
    push_cast [Nat.cast_sub hij]; ring
  have h1 : risingFactorial (b + (i : ℝ)) (j - i) =
      fallingFactorial (b + (j : ℝ) - 1) (j - i) := by
    rw [risingFactorial_eq_fallingFactorial, hcast]
    ring_nf
  rw [h1, ← neg_one_pow_mul_risingFactorial]
  ring

private theorem div_mul_cancel_aux (X d e : ℝ) (hd : d ≠ 0) : X / d * (d * e) = X * e := by
  field_simp

/-- **Terminating Chu–Vandermonde identity.**  For all natural numbers `j, k`
and every real `s > 0`,
`∑_{i=0}^{j} (-1)^i C(j,i) * risingFactorial (j+s-1) i /
risingFactorial (s+k) i = fallingFactorial k j / risingFactorial (s+k) j`.
No relation between `j` and `k` is assumed: when `j > k` the right-hand side vanishes. -/
theorem chu_vandermonde_terminating (j k : ℕ) (s : ℝ) (hs : 0 < s) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ)
        * risingFactorial ((j : ℝ) + s - 1) i / risingFactorial (s + (k : ℝ)) i
      = fallingFactorial (k : ℝ) j / risingFactorial (s + (k : ℝ)) j := by
  have hb : (0 : ℝ) < s + (k : ℝ) := by positivity
  rw [eq_div_iff (ne_of_gt (risingFactorial_pos j hb)), Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      ((-1 : ℝ) ^ i * (j.choose i : ℝ) * risingFactorial ((j : ℝ) + s - 1) i /
          risingFactorial (s + (k : ℝ)) i)
          * risingFactorial (s + (k : ℝ)) j
        = (-1 : ℝ) ^ i * (j.choose i : ℝ) * risingFactorial ((j : ℝ) + s - 1) i
          * risingFactorial ((s + (k : ℝ)) + (i : ℝ)) (j - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp hi
    have hsplit : risingFactorial (s + (k : ℝ)) j
        = risingFactorial (s + (k : ℝ)) i *
          risingFactorial ((s + (k : ℝ)) + (i : ℝ)) (j - i) := by
      rw [← risingFactorial_add]
      congr 1
      lia
    rw [hsplit, div_mul_cancel_aux _ _ _ (ne_of_gt (risingFactorial_pos i hb))]
  rw [Finset.sum_congr rfl hterm, sum_range_neg_one_pow_mul_choose_mul_risingFactorial]
  have hba : s + (k : ℝ) - ((j : ℝ) + s - 1) = (k : ℝ) - (j : ℝ) + 1 := by ring
  rw [hba, risingFactorial_eq_fallingFactorial]
  congr 1
  ring

/-- The `j > k` case of the identity: the alternating sum cancels to zero. -/
theorem chu_vandermonde_terminating_eq_zero (j k : ℕ) (s : ℝ) (hs : 0 < s) (hjk : k < j) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ)
        * risingFactorial ((j : ℝ) + s - 1) i / risingFactorial (s + (k : ℝ)) i = 0 := by
  rw [chu_vandermonde_terminating j k s hs, fallingFactorial_natCast_eq_zero_of_lt hjk, zero_div]

/-! ## Pfaff--Saalschütz -/

/-- The generic term of the double sum in the proof of Pfaff--Saalschütz. -/
private def pfaffSaalschutzTerm (a b d : ℝ) (n k i : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((n - k).choose i : ℝ) *
    (risingFactorial a (k + i) * risingFactorial b k * risingFactorial d (n - k) *
        risingFactorial (b + d) (n - k - i))

private theorem pfaffSaalschutz_stepA (n : ℕ) (a b c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (risingFactorial a k * risingFactorial b k * risingFactorial (c + (k : ℝ)) (n - k) *
            risingFactorial (c - a - b) (n - k))
      = ∑ k ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1 - k), pfaffSaalschutzTerm a b (c - a - b) n k i := by
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hc : c + (k : ℝ) = (a + (k : ℝ)) + (b + (c - a - b)) := by ring
  have hr : n - k + 1 = n + 1 - k := by lia
  rw [hc, risingFactorial_add_eq_sum_range, hr]
  calc (n.choose k : ℝ) * (risingFactorial a k * risingFactorial b k *
          (∑ i ∈ Finset.range (n + 1 - k), ((n - k).choose i : ℝ) *
            (risingFactorial (a + (k : ℝ)) i * risingFactorial (b + (c - a - b)) (n - k - i))) *
          risingFactorial (c - a - b) (n - k))
      = ((n.choose k : ℝ) * risingFactorial a k * risingFactorial b k * risingFactorial (c - a -
          b) (n - k)) *
          (∑ i ∈ Finset.range (n + 1 - k), ((n - k).choose i : ℝ) *
            (risingFactorial (a + (k : ℝ)) i * risingFactorial (b + (c - a - b)) (n - k -
                i))) := by ring
    _ = ∑ i ∈ Finset.range (n + 1 - k), pfaffSaalschutzTerm a b (c - a - b) n k i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [pfaffSaalschutzTerm, risingFactorial_add a k i]
        ring

private theorem pfaffSaalschutz_stepC (n j : ℕ) (hj : j ≤ n) (a b d : ℝ) :
    ∑ k ∈ Finset.range (j + 1), pfaffSaalschutzTerm a b d n k (j - k)
      = (n.choose j : ℝ) * (risingFactorial a j * risingFactorial d (n - j) * risingFactorial (b +
          d) n) := by
  have key : ∀ k ∈ Finset.range (j + 1), pfaffSaalschutzTerm a b d n k (j - k)
      = ((n.choose j : ℝ) * (risingFactorial a j * risingFactorial d (n - j) *
          risingFactorial (b + d) (n - j)))
        * ((j.choose k : ℝ) *
          (risingFactorial b k *
            risingFactorial (d + ((n - j : ℕ) : ℝ)) (j - k))) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have h1 : k + (j - k) = j := by lia
    have h2 : n - k - (j - k) = n - j := by lia
    have h3 : (n.choose k : ℝ) * (((n - k).choose (j - k) : ℕ) : ℝ)
        = (n.choose j : ℝ) * (j.choose k : ℝ) := by
      have hnat : n.choose j * j.choose k = n.choose k * (n - k).choose (j - k) :=
        Nat.choose_mul hk
      exact_mod_cast hnat.symm
    have h4 : risingFactorial d (n - k) = risingFactorial d (n - j) * risingFactorial (d + ((n -
        j : ℕ) : ℝ)) (j - k) := by
      have hsplit : (n - j) + (j - k) = n - k := by lia
      rw [← hsplit, risingFactorial_add]
    simp only [pfaffSaalschutzTerm, h1, h2, h4]
    linear_combination (risingFactorial a j * risingFactorial b k * risingFactorial d (n - j) *
      risingFactorial (d + ((n - j : ℕ) : ℝ)) (j - k) * risingFactorial (b + d) (n - j)) * h3
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← risingFactorial_add_eq_sum_range]
  have h5 :
      risingFactorial (b + d) (n - j) * risingFactorial (b + (d + ((n - j : ℕ) : ℝ))) j =
        risingFactorial (b + d) n := by
    have hx : b + (d + ((n - j : ℕ) : ℝ)) = (b + d) + ((n - j : ℕ) : ℝ) := by ring
    rw [hx, ← risingFactorial_add, Nat.sub_add_cancel hj]
  linear_combination ((n.choose j : ℝ) * risingFactorial a j * risingFactorial d (n - j)) * h5

/-- The Pfaff–Saalschütz theorem in polynomial (denominator-free) form. -/
theorem risingFactorial_pfaffSaalschutz (n : ℕ) (a b c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (risingFactorial a k * risingFactorial b k * risingFactorial (c + (k : ℝ)) (n - k) *
            risingFactorial (c - a - b) (n - k))
      = risingFactorial (c - a) n * risingFactorial (c - b) n := by
  rw [pfaffSaalschutz_stepA n a b c,
    ← Finset.sum_range_diag_flip (n + 1) (fun k i => pfaffSaalschutzTerm a b (c - a - b) n k i),
    Finset.sum_congr rfl (fun j hj => pfaffSaalschutz_stepC n j
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj) a b (c - a - b))]
  have hfac : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (risingFactorial a j * risingFactorial (c - a - b) (n - j) * risingFactorial (b + (c - a -
            b)) n)
      = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (risingFactorial a j * risingFactorial (c - a - b) (n - j))) * risingFactorial (b + (c -
              a - b)) n := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfac, ← risingFactorial_add_eq_sum_range]
  have h1 : a + (c - a - b) = c - b := by ring
  have h2 : b + (c - a - b) = c - a := by ring
  rw [h1, h2, mul_comm]

end RealRooted.JacobiDeformation
