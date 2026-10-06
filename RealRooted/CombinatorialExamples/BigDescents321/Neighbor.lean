import RealRooted.CombinatorialExamples.BigDescents321.Certificate
import RealRooted.CombinatorialExamples.BigDescents321.Coordinates

/-!
# The neighbouring-coefficient inequality

For `r ≥ 6` and `J ≥ 2` the Gegenbauer coordinates of `Q_(J+2r)` satisfy

`(J + 1) q_(J+2r, J) - J q_(J+2r, J-2) > 0`.

With `R = r + 1` and `X = J - 2`, the four kernel sums on the left are rewritten as sums over
the weights `W_(R,k)(X)` by the ratios `L₁, L₂, L₃`. The difference becomes
`2^(1-2R) ∑_(k ≤ R) W_(R,k)(X) P(R, X, k)`, which the universal certificate in
`Certificate.lean` shows to be positive. The inequality is false for `r = 5`.

## Main statements

* `kernelCoord_eq_kernelSum`: `q_(J+2r, J) = (2J + 3)(c_r(J) - c_(r-1)(J)/2)` for `r ≥ 3`.
* `kernelCoord_neighbor_pos`: the inequality above.
-/

open Finset

namespace RealRooted.BigDescents321

/-- `W_(r,k)(J) / W_(r+1,k)(J)`. -/
theorem kernelWeight_rank_succ {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k J = kernelWeight (r + 1) k J *
      ((r + 1 - k) * (J + k + r + 2) / ((r + k - 1) * (2 * J + r + k + 2)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + k - 2 = (k + s + k - 2) + 1 by lia, show k + s - k = s by lia,
    show k + s + 1 - k = s + 1 by lia,
    show 2 * J + (k + s + 1) + k + 1 = (2 * J + (k + s) + k + 1) + 1 by ring,
    show J + k + (k + s + 1) + 1 = (J + k + (k + s) + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s) + k + 1 = A
  generalize hE : J + k + (k + s) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 1 := by rw [← hA]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 1 := by rw [← hE]; push_cast; ring
  have hn1 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  rw [hu', hA', hE']
  field_simp
  ring

/-- `q_(J+2r, J) = (2J + 3)(c_r(J) - c_(r-1)(J)/2)` for `r ≥ 3`, with `c_r = kernelSum r`. -/
theorem kernelCoord_eq_kernelSum {m : ℕ} (hm : 2 ≤ m) (J : ℕ) :
    kernelCoord (m + 1 : ℕ) J = (2 * J + 3) * (kernelSum (m + 1) J - kernelSum m J / 2) := by
  rw [kernelCoord_eq, corrCoordZ_of_three_le (by lia),
    show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℕ) by push_cast; ring,
    kernelMoment_eq_neg_kernelSum (by lia), kernelMoment_eq_neg_kernelSum hm]
  ring

/-- Extend a weighted sum to a larger range, where the weight ratio vanishes. -/
private theorem sum_kernelWeight_extend {n d m J' J : ℕ} (hm : m = n + d) (ρ G : ℕ → ℚ)
    (hW : ∀ k ≤ n, kernelWeight n k J' = kernelWeight m k J * ρ k)
    (hz : ∀ i < d, ρ (n + 1 + i) = 0) :
    ∑ k ∈ range (n + 1), kernelWeight n k J' * G k =
      ∑ k ∈ range (m + 1), kernelWeight m k J * ρ k * G k := by
  subst hm
  rw [show n + d + 1 = n + 1 + d by lia,
    sum_range_add (fun k ↦ kernelWeight (n + d) k J * ρ k * G k) (n + 1) d,
    sum_eq_zero (s := range d) fun i hi ↦ by simp [hz i (mem_range.mp hi)], add_zero]
  exact sum_congr rfl fun k hk ↦ by rw [hW k (by have := mem_range.mp hk; lia)]

/-- The four kernel sums, rewritten over the weights `W_(t+2,k)(X)`. -/
private theorem kernelSum_neighbor_eq {t : ℕ} (ht : 5 ≤ t) (X : ℕ) :
    ((X + 2 : ℕ) + 1 : ℚ) * kernelCoord (t + 1 : ℕ) (X + 2) -
        (X + 2 : ℕ) * kernelCoord (t + 1 + 1 : ℕ) X =
      2 * (1 / 4) ^ (t + 2) * ∑ k ∈ range (t + 2 + 1),
        kernelWeight (t + 2) k X * bernP ((t : ℚ) + 2) X k := by
  have hX0 : (0 : ℚ) ≤ X := X.cast_nonneg
  have ht' : (5 : ℚ) ≤ t := by exact_mod_cast ht
  -- `L₁`: `W_(t+1,k)(X+2) = W_(t+2,k)(X) L₁`.
  have ha := sum_kernelWeight_extend (n := t + 1) (d := 1) (m := t + 2) (J' := X + 2) (J := X)
    rfl (fun k ↦ bernL1 ((t : ℚ) + 2) X k) (fun k ↦ kernelF (t + 1) (X + 2) k)
    (fun k hk ↦ by
      have hk' : (k : ℚ) ≤ t + 1 := by exact_mod_cast hk
      rw [kernelWeight_two (by lia) hk]
      congr 1
      unfold bernL1
      push_cast
      have : (t : ℚ) + 1 + k - 1 ≠ 0 := by intro h; linarith
      have : (X : ℚ) + k + (t + 1) + 3 ≠ 0 := by intro h; linarith
      have : (t : ℚ) + 2 + k - 2 ≠ 0 := by intro h; linarith
      field_simp
      ring)
    (fun i hi ↦ by
      obtain rfl : i = 0 := by lia
      simp only [bernL1]
      push_cast
      ring)
  -- `L₂`: `W_(t,k)(X+2) = W_(t+1,k)(X) (W_(t+1,k)(X) / W_(t+2,k)(X)) = W_(t+2,k)(X) L₂`.
  have hb := sum_kernelWeight_extend (n := t) (d := 2) (m := t + 2) (J' := X + 2) (J := X)
    rfl (fun k ↦ bernL2 ((t : ℚ) + 2) X k) (fun k ↦ kernelF t (X + 2) k)
    (fun k hk ↦ by
      have hk' : (k : ℚ) ≤ t := by exact_mod_cast hk
      rw [kernelWeight_two (by lia) hk, kernelWeight_rank_succ (by lia) (by lia), mul_assoc]
      congr 1
      unfold bernL2
      push_cast
      have : (t : ℚ) + k - 1 ≠ 0 := by intro h; linarith
      have : (t : ℚ) + 1 + k - 1 ≠ 0 := by intro h; linarith
      have : (X : ℚ) + k + t + 3 ≠ 0 := by intro h; linarith
      have : 2 * (X : ℚ) + (t + 1) + k + 2 ≠ 0 := by intro h; linarith
      have : (t : ℚ) + 2 + k - 2 ≠ 0 := by intro h; linarith
      have : (t : ℚ) + 2 + k - 3 ≠ 0 := by intro h; linarith
      field_simp
      ring)
    (fun i hi ↦ by
      simp only [bernL2]
      rcases (show i = 0 ∨ i = 1 by lia) with rfl | rfl <;> push_cast <;> ring)
  -- `L₃`: `W_(t+1,k)(X) = W_(t+2,k)(X) L₃`.
  have hd := sum_kernelWeight_extend (n := t + 1) (d := 1) (m := t + 2) (J' := X) (J := X)
    rfl (fun k ↦ bernL3 ((t : ℚ) + 2) X k) (fun k ↦ kernelF (t + 1) X k)
    (fun k hk ↦ by
      have hk' : (k : ℚ) ≤ t + 1 := by exact_mod_cast hk
      rw [kernelWeight_rank_succ (by lia) hk]
      congr 1
      unfold bernL3
      push_cast
      ring_nf)
    (fun i hi ↦ by
      obtain rfl : i = 0 := by lia
      simp only [bernL3]
      push_cast
      ring)
  have hP : ∑ k ∈ range (t + 2 + 1), kernelWeight (t + 2) k X * bernP ((t : ℚ) + 2) X k =
      4 * ((X + 3) * (2 * X + 7)) * ∑ k ∈ range (t + 2 + 1),
          kernelWeight (t + 2) k X * bernL1 ((t : ℚ) + 2) X k * kernelF (t + 1) (X + 2) k -
        8 * ((X + 3) * (2 * X + 7)) * ∑ k ∈ range (t + 2 + 1),
          kernelWeight (t + 2) k X * bernL2 ((t : ℚ) + 2) X k * kernelF t (X + 2) k -
        (X + 2) * (2 * X + 3) * ∑ k ∈ range (t + 2 + 1),
          kernelWeight (t + 2) k X * kernelF (t + 2) X k +
        2 * ((X + 2) * (2 * X + 3)) * ∑ k ∈ range (t + 2 + 1),
          kernelWeight (t + 2) k X * bernL3 ((t : ℚ) + 2) X k * kernelF (t + 1) X k := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [bernP, kernelF, certF]
    push_cast
    ring
  rw [kernelCoord_eq_kernelSum (by lia), kernelCoord_eq_kernelSum (by lia), hP, ← ha, ← hb,
    ← hd]
  simp only [kernelSum]
  push_cast
  ring

/-- `∑_(k ≤ R) W_(R,k)(X) P(R, X, k) > 0` for `R = t + 2 ≥ 7`: the sum telescopes to
`∑_(k ≤ R) W_(R,k)(X) H̃(R, X, k) / (2 L d(R, X, k))`, whose terms are nonnegative and whose
`k = 0` term is positive. -/
theorem sum_kernelWeight_mul_bernP_pos {t : ℕ} (ht : 5 ≤ t) (X : ℕ) :
    0 < ∑ k ∈ range (t + 2 + 1), kernelWeight (t + 2) k X * bernP ((t : ℚ) + 2) X k := by
  have hR : (7 : ℚ) ≤ t + 2 := by
    have : (5 : ℚ) ≤ t := by exact_mod_cast ht
    linarith
  have hX0 : (0 : ℚ) ≤ X := X.cast_nonneg
  have hsplit : ∀ k ∈ range (t + 2 + 1), kernelWeight (t + 2) k X * bernP ((t : ℚ) + 2) X k =
      kernelWeight (t + 2) k X *
          (bernH ((t : ℚ) + 2) X k / (2 * CertData.lden * bernD ((t : ℚ) + 2) X k)) +
        (kernelWeight (t + 2) k X * certBq ((t : ℚ) + 2 - 1) X k *
            bernG ((t : ℚ) + 2) X (k + 1) -
          kernelWeight (t + 2) k X * bernG ((t : ℚ) + 2) X k) := fun k _ ↦ by
    rw [bernP_eq hR hX0 k.cast_nonneg]
    ring
  have hstep : ∀ k ∈ range (t + 2), kernelWeight (t + 2) k X * certBq ((t : ℚ) + 2 - 1) X k *
        bernG ((t : ℚ) + 2) X (k + 1) - kernelWeight (t + 2) k X * bernG ((t : ℚ) + 2) X k =
      kernelWeight (t + 2) (k + 1) X * bernG ((t : ℚ) + 2) X (k + 1 : ℕ) -
        kernelWeight (t + 2) k X * bernG ((t : ℚ) + 2) X k := fun k hk ↦ by
    have hW := kernelWeight_succ_right (r := t + 1) (k := k) (J := X) (by lia)
      (by have := mem_range.mp hk; lia)
    rw [show t + 1 + 1 = t + 2 from rfl] at hW
    rw [hW]
    push_cast
    unfold certBq
    ring
  have hlast : certBq ((t : ℚ) + 2 - 1) X ((t + 2 : ℕ) : ℚ) = 0 := by
    unfold certBq
    push_cast
    ring
  have htel : ∑ k ∈ range (t + 2 + 1), (kernelWeight (t + 2) k X *
        certBq ((t : ℚ) + 2 - 1) X k * bernG ((t : ℚ) + 2) X (k + 1) -
      kernelWeight (t + 2) k X * bernG ((t : ℚ) + 2) X k) = 0 := by
    rw [sum_range_succ, hlast, mul_zero, zero_mul, zero_sub, sum_congr rfl hstep,
      sum_range_sub (fun k ↦ kernelWeight (t + 2) k X * bernG ((t : ℚ) + 2) X k)]
    simp [bernG]
  rw [sum_congr rfl hsplit, sum_add_distrib, htel, add_zero]
  have hden : ∀ k : ℕ, 0 < 2 * (CertData.lden : ℚ) * bernD ((t : ℚ) + 2) X k := fun k ↦
    mul_pos (mul_pos two_pos lden_pos) (bernD_pos hR hX0 k.cast_nonneg)
  refine sum_pos' (fun k hk ↦ ?_) ⟨0, by simp, ?_⟩
  · have hk : (k : ℚ) ≤ t + 2 := by
      have : k ≤ t + 2 := by have := mem_range.mp hk; lia
      exact_mod_cast this
    exact mul_nonneg (kernelWeight_pos _ _ _).le
      (div_nonneg (bernH_nonneg hR hX0 k.cast_nonneg hk) (hden k).le)
  · have h0 := hden 0
    rw [Nat.cast_zero] at h0 ⊢
    exact mul_pos (kernelWeight_pos _ _ _) (div_pos (bernH_pos_zero hR hX0) h0)

/-- The neighbouring-coefficient inequality `(J + 1) q_(J+2r, J) - J q_(J+2r, J-2) > 0` for
`r ≥ 6` and `J ≥ 2` (issue #1143, §9 and §11). -/
theorem kernelCoord_neighbor_pos {r J : ℕ} (hr : 6 ≤ r) (hJ : 2 ≤ J) :
    0 < (J + 1 : ℚ) * kernelCoord r J - J * kernelCoord (r + 1 : ℕ) (J - 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by lia⟩
  obtain ⟨X, rfl⟩ : ∃ X, J = X + 2 := ⟨J - 2, by lia⟩
  have h := kernelSum_neighbor_eq (t := t) (by lia) X
  rw [Nat.add_sub_cancel]
  push_cast at h ⊢
  rw [h]
  exact mul_pos (by positivity) (sum_kernelWeight_mul_bernP_pos (by lia) X)

end RealRooted.BigDescents321
