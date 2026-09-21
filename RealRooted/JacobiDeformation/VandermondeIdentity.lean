import RealRooted.JacobiDeformation.Basic

/-!
# Finite Chu--Vandermonde identity

This is the finite algebraic identity used by the normalized Jacobi moment
calculation. It intentionally has no local resource-option changes.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

namespace FiniteVandermonde

open Finset

/-- `rising x i = ∏_{l=0}^{i-1} (x + l)`; the empty product is `1`. -/
noncomputable def rising (x : ℝ) (i : ℕ) : ℝ := ∏ l ∈ Finset.range i, (x + (l : ℝ))

/-- `falling x i = ∏_{l=0}^{i-1} (x - l)`; the empty product is `1`. -/
noncomputable def falling (x : ℝ) (i : ℕ) : ℝ := ∏ l ∈ Finset.range i, (x - (l : ℝ))

@[simp] lemma rising_zero (x : ℝ) : rising x 0 = 1 := by simp [rising]

@[simp] lemma falling_zero (x : ℝ) : falling x 0 = 1 := by simp [falling]

lemma rising_succ (x : ℝ) (i : ℕ) : rising x (i + 1) = rising x i * (x + (i : ℝ)) := by
  simp [rising, Finset.prod_range_succ]

lemma falling_succ (x : ℝ) (i : ℕ) : falling x (i + 1) = falling x i * (x - (i : ℝ)) := by
  simp [falling, Finset.prod_range_succ]

lemma rising_add (x : ℝ) (m n : ℕ) : rising x (m + n) = rising x m * rising (x + (m : ℝ)) n := by
  unfold rising
  rw [Finset.prod_range_add]
  refine congrArg _ (Finset.prod_congr rfl ?_)
  intro i _
  push_cast
  ring

/-- A rising factorial is a falling factorial read from the other end. -/
lemma rising_eq_falling (x : ℝ) (m : ℕ) : rising x m = falling (x + (m : ℝ) - 1) m := by
  unfold rising falling
  rw [← Finset.prod_range_reflect (fun l => x + (m : ℝ) - 1 - (l : ℝ)) m]
  refine Finset.prod_congr rfl ?_
  intro i hi
  rw [Finset.mem_range] at hi
  have hcast : ((m - 1 - i : ℕ) : ℝ) = (m : ℝ) - 1 - (i : ℝ) := by
    have h1 : 1 ≤ m := Nat.one_le_of_lt hi
    have h2 : i ≤ m - 1 := by lia
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  rw [hcast]
  ring

/-- `(-1)^i * rising x i = falling (-x) i`. -/
lemma neg_one_pow_mul_rising (x : ℝ) (i : ℕ) :
    (-1 : ℝ) ^ i * rising x i = falling (-x) i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [rising_succ, falling_succ, pow_succ, ← ih]
    ring

/-- Vandermonde's identity for falling factorials:
`∑_{i=0}^{j} C(j,i) * falling u i * falling v (j-i) = falling (u+v) j`. -/
lemma falling_vandermonde (u v : ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u i * falling v (j - i)
      = falling (u + v) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ez : ∑ i ∈ Finset.range (j + 1), (j.choose (i + 1) : ℝ) * falling u (i + 1)
          * falling v (j - i)
        = ∑ i ∈ Finset.range j, (j.choose (i + 1) : ℝ) * falling u (i + 1)
          * falling v (j - i) := by
      rw [Finset.sum_range_succ]
      simp
    have e1 : ∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ) * falling u i
          * falling v (j + 1 - i)
        = (∑ i ∈ Finset.range (j + 1), ((j + 1).choose (i + 1) : ℝ) * falling u (i + 1)
            * falling v (j - i)) + falling v (j + 1) := by
      rw [Finset.sum_range_succ' (fun i => ((j + 1).choose i : ℝ) * falling u i
        * falling v (j + 1 - i)) (j + 1)]
      simp
    have e2 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u i * falling v (j + 1 - i)
        = (∑ i ∈ Finset.range (j + 1), (j.choose (i + 1) : ℝ) * falling u (i + 1)
            * falling v (j - i)) + falling v (j + 1) := by
      rw [ez, Finset.sum_range_succ' (fun i => (j.choose i : ℝ) * falling u i
        * falling v (j + 1 - i)) j]
      simp
    have e3 : ∑ i ∈ Finset.range (j + 1), ((j + 1).choose (i + 1) : ℝ) * falling u (i + 1)
          * falling v (j - i)
        = (∑ i ∈ Finset.range (j + 1), (j.choose (i + 1) : ℝ) * falling u (i + 1)
            * falling v (j - i))
          + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u (i + 1)
            * falling v (j - i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hc : ((j + 1).choose (i + 1) : ℝ) = (j.choose i : ℝ) + (j.choose (i + 1) : ℝ) := by
        push_cast [Nat.choose_succ_succ j i]
        ring
      rw [hc]
      ring
    have key : ∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ) * falling u i
          * falling v (j + 1 - i)
        = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u i * falling v (j + 1 - i))
          + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u (i + 1)
            * falling v (j - i) := by
      rw [e1, e3, e2]
      ring
    rw [key]
    have hA : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u i * falling v (j + 1 - i)
        = ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * falling u i * falling v (j - i)) * (v - ((j : ℝ) - (i : ℝ))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mem_range] at hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp hi
      have h1 : j + 1 - i = (j - i) + 1 := by lia
      have h2 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
        push_cast [Nat.cast_sub hij]; ring
      rw [h1, falling_succ, h2]
      ring
    have hB : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u (i + 1) * falling v (j - i)
        = ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * falling u i * falling v (j - i)) * (u - (i : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [falling_succ]
      ring
    have hsum : ∑ i ∈ Finset.range (j + 1),
        (((j.choose i : ℝ) * falling u i * falling v (j - i)) * (v - ((j : ℝ) - (i : ℝ)))
          + ((j.choose i : ℝ) * falling u i * falling v (j - i)) * (u - (i : ℝ)))
        = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * falling u i * falling v (j - i))
            * (u + v - (j : ℝ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hA, hB, ← Finset.sum_add_distrib, hsum, ih, falling_succ]

/-- Positivity of the rising factorials appearing in the denominators. -/
lemma rising_pos {y : ℝ} (hy : 0 < y) (i : ℕ) : 0 < rising y i := by
  unfold rising
  refine Finset.prod_pos ?_
  intro l _
  positivity

/-- The general terminating Chu–Vandermonde sum, with denominators cleared:
`∑_{i=0}^{j} (-1)^i C(j,i) rising a i * rising (b+i) (j-i) = rising (b - a) j`. -/
lemma cleared_identity (a b : ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ) * rising a i
        * rising (b + (i : ℝ)) (j - i)
      = rising (b - a) j := by
  have h := falling_vandermonde (-a) (b + (j : ℝ) - 1) j
  have hb : (-a) + (b + (j : ℝ) - 1) = (b - a) + (j : ℝ) - 1 := by ring
  rw [hb, ← rising_eq_falling] at h
  rw [← h]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mem_range] at hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp hi
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
    push_cast [Nat.cast_sub hij]; ring
  have h1 : rising (b + (i : ℝ)) (j - i) = falling (b + (j : ℝ) - 1) (j - i) := by
    rw [rising_eq_falling, hcast]
    ring_nf
  rw [h1, ← neg_one_pow_mul_rising]
  ring

private lemma div_mul_cancel_aux (X d e : ℝ) (hd : d ≠ 0) : X / d * (d * e) = X * e := by
  field_simp

/-- **Terminating Chu–Vandermonde identity.**  For all natural numbers `j, k` and every real
`s > 0`,
`∑_{i=0}^{j} (-1)^i C(j,i) * rising (j+s-1) i / rising (s+k) i = falling k j / rising (s+k) j`.
No relation between `j` and `k` is assumed: when `j > k` the right-hand side vanishes. -/
theorem chu_vandermonde_terminating (j k : ℕ) (s : ℝ) (hs : 0 < s) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ)
        * rising ((j : ℝ) + s - 1) i / rising (s + (k : ℝ)) i
      = falling (k : ℝ) j / rising (s + (k : ℝ)) j := by
  have hb : (0 : ℝ) < s + (k : ℝ) := by positivity
  rw [eq_div_iff (ne_of_gt (rising_pos hb j)), Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      ((-1 : ℝ) ^ i * (j.choose i : ℝ) * rising ((j : ℝ) + s - 1) i / rising (s + (k : ℝ)) i)
          * rising (s + (k : ℝ)) j
        = (-1 : ℝ) ^ i * (j.choose i : ℝ) * rising ((j : ℝ) + s - 1) i
          * rising ((s + (k : ℝ)) + (i : ℝ)) (j - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp hi
    have hsplit : rising (s + (k : ℝ)) j
        = rising (s + (k : ℝ)) i * rising ((s + (k : ℝ)) + (i : ℝ)) (j - i) := by
      rw [← rising_add]
      congr 1
      lia
    rw [hsplit, div_mul_cancel_aux _ _ _ (ne_of_gt (rising_pos hb i))]
  rw [Finset.sum_congr rfl hterm, cleared_identity]
  have hba : s + (k : ℝ) - ((j : ℝ) + s - 1) = (k : ℝ) - (j : ℝ) + 1 := by ring
  rw [hba, rising_eq_falling]
  congr 1
  ring

/-- For natural `k < j` the falling factorial `falling k j` vanishes. -/
lemma falling_nat_eq_zero (k j : ℕ) (h : k < j) : falling (k : ℝ) j = 0 := by
  unfold falling
  refine Finset.prod_eq_zero (Finset.mem_range.mpr h) ?_
  simp

/-- The `j > k` case of the identity: the alternating sum cancels to zero. -/
theorem chu_vandermonde_terminating_eq_zero (j k : ℕ) (s : ℝ) (hs : 0 < s) (hjk : k < j) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ)
        * rising ((j : ℝ) + s - 1) i / rising (s + (k : ℝ)) i = 0 := by
  rw [chu_vandermonde_terminating j k s hs, falling_nat_eq_zero k j hjk, zero_div]

end FiniteVandermonde

end RealRooted.JacobiDeformation
