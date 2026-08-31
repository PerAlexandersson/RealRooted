import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Thresholded polynomial-root counts

The root multiset filtered above a moving negative threshold, together with the
parity information supplied by polynomial evaluations at that threshold.
-/

namespace RealRooted.RootCounting

open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The roots above `-s`. -/
noncomputable def rootsAbove (p : K[X]) (s : K) : Multiset K :=
  p.roots.filter (fun ξ => -s < ξ)

/-- Moving the threshold to the left can only add roots to the filtered multiset. -/
theorem rootsAbove_le (p : K[X]) {s s' : K} (h : s ≤ s') :
    rootsAbove p s ≤ rootsAbove p s' := by
  classical
  rw [rootsAbove, rootsAbove]
  refine Multiset.le_iff_count.mpr (fun ξ => ?_)
  by_cases h₁ : -s < ξ
  · have h₂ : -s' < ξ := by linarith
    rw [Multiset.count_filter, Multiset.count_filter, if_pos h₁, if_pos h₂]
  · rw [Multiset.count_filter, if_neg h₁]
    exact Nat.zero_le _

/-- The cardinality of `rootsAbove` is monotone in its threshold. -/
theorem card_rootsAbove_mono (p : K[X]) {s s' : K} (h : s ≤ s') :
    Multiset.card (rootsAbove p s) ≤ Multiset.card (rootsAbove p s') :=
  Multiset.card_le_card (rootsAbove_le p h)

/-- The sign of a product records the parity of its factors above `-s`. -/
theorem prod_sign {m : Multiset K} {s : K} (h : ∀ ξ ∈ m, ξ ≠ -s) :
    0 < (-1 : K) ^ (Multiset.card (m.filter (fun ξ => -s < ξ)))
      * (m.map (fun ξ => -s - ξ)).prod := by
  classical
  induction m using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have hta : ∀ ξ ∈ t, ξ ≠ -s := fun ξ hξ => h ξ (Multiset.mem_cons_of_mem hξ)
      have hane : a ≠ -s := h a (Multiset.mem_cons_self a t)
      have hIH := ih hta
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
      rcases lt_or_gt_of_ne hane with hlt | hgt
      · have hnot : ¬ (-s < a) := by linarith
        rw [if_neg hnot]
        simp only [zero_add]
        have hfac : (0 : K) < -s - a := by linarith
        nlinarith [hIH, hfac]
      · rw [if_pos hgt]
        rw [Multiset.card_add, Multiset.card_singleton]
        have hfac : (-s - a) < 0 := by linarith
        have hpow : (-1 : K) ^ (1 + Multiset.card (t.filter (fun ξ => -s < ξ)))
            = -((-1 : K) ^ (Multiset.card (t.filter (fun ξ => -s < ξ)))) := by
          rw [pow_add, pow_one]
          ring
        rw [hpow]
        nlinarith [hIH, hfac]

/-- The sign of `p (-s)` is the parity of the roots above `-s`. -/
theorem sign_eval_neg {p : K[X]} (hcard : Multiset.card p.roots = p.natDegree)
    (hlc : 0 < p.leadingCoeff) {s : K} (hns : ∀ ξ ∈ p.roots, ξ ≠ -s) :
    0 < (-1 : K) ^ (Multiset.card (rootsAbove p s)) * p.eval (-s) := by
  classical
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have heval : p.eval (-s)
      = p.leadingCoeff * ((p.roots.map (fun ξ => -s - ξ)).prod) := by
    conv_lhs => rw [← hfac]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun ξ _ => ?_))
    simp
  rw [heval, rootsAbove]
  have hsign := prod_sign (m := p.roots) (s := s) hns
  nlinarith [hsign, hlc]

/-- A positive dominant coefficient fixes the sign of the polynomial at `-s`. -/
theorem sign_of_dominant {p : K[X]} {s : K} (hs : 0 < s) {j N : ℕ}
    (hdeg : p.natDegree < N) (hj : j < N) (hpj : 0 < p.coeff j)
    (hdom : ∑ k ∈ (Finset.range N).erase j, |p.coeff k| * s ^ k
      < |p.coeff j| * s ^ j) :
    0 < (-1 : K) ^ j * p.eval (-s) := by
  classical
  have hsum : p.eval (-s) = ∑ k ∈ Finset.range N, p.coeff k * (-s) ^ k := by
    rw [Polynomial.eval_eq_sum_range' hdeg]
  have hjmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
  have hsplit : ∑ k ∈ Finset.range N, p.coeff k * (-s) ^ k
      = p.coeff j * (-s) ^ j
        + ∑ k ∈ (Finset.range N).erase j, p.coeff k * (-s) ^ k :=
    (Finset.add_sum_erase _ _ hjmem).symm
  have habs : |∑ k ∈ (Finset.range N).erase j, p.coeff k * (-s) ^ k|
      ≤ ∑ k ∈ (Finset.range N).erase j, |p.coeff k| * s ^ k := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_of_pos hs]
  have hjval : (-1 : K) ^ j * (p.coeff j * (-s) ^ j) = p.coeff j * s ^ j := by
    calc
      (-1 : K) ^ j * (p.coeff j * (-s) ^ j)
          = p.coeff j * ((-1 : K) ^ j * (-s) ^ j) := by ring
      _ = p.coeff j * ((-1 : K) * (-s)) ^ j := by rw [mul_pow]
      _ = p.coeff j * s ^ j := by rw [show ((-1 : K) * (-s)) = s by ring]
  have hpow : |(-1 : K) ^ j| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have hkey : |(-1 : K) ^ j * ∑ k ∈ (Finset.range N).erase j, p.coeff k * (-s) ^ k|
      < p.coeff j * s ^ j := by
    rw [abs_mul, hpow, one_mul]
    refine lt_of_le_of_lt habs ?_
    rwa [abs_of_pos hpj] at hdom
  rw [hsum, hsplit, mul_add, hjval]
  have hb := abs_lt.mp hkey
  linarith [hb.1]

/-- Coefficient dominance determines the parity of the thresholded root count. -/
theorem parity_of_dominant {p : K[X]} {s : K} (hs : 0 < s)
    (hcard : Multiset.card p.roots = p.natDegree) (hlc : 0 < p.leadingCoeff)
    (hns : ∀ ξ ∈ p.roots, ξ ≠ -s) {j N : ℕ}
    (hdeg : p.natDegree < N) (hj : j < N) (hpj : 0 < p.coeff j)
    (hdom : ∑ k ∈ (Finset.range N).erase j, |p.coeff k| * s ^ k
      < |p.coeff j| * s ^ j) :
    (-1 : K) ^ (Multiset.card (rootsAbove p s)) = (-1 : K) ^ j := by
  have h₁ := sign_eval_neg hcard hlc hns
  have h₂ := sign_of_dominant hs hdeg hj hpj hdom
  rcases neg_one_pow_eq_or K (Multiset.card (rootsAbove p s)) with hA | hA <;>
    rcases neg_one_pow_eq_or K j with hB | hB
  · rw [hA, hB]
  · rw [hA] at h₁
    rw [hB] at h₂
    exfalso
    nlinarith [h₁, h₂]
  · rw [hA] at h₁
    rw [hB] at h₂
    exfalso
    nlinarith [h₁, h₂]
  · rw [hA, hB]

/-- Different count parities force a strict increase of the root count. -/
theorem card_lt_of_parity_ne {p : K[X]} {s s' : K} (hss : s ≤ s')
    (hpar : (-1 : K) ^ (Multiset.card (rootsAbove p s))
      ≠ (-1 : K) ^ (Multiset.card (rootsAbove p s'))) :
    Multiset.card (rootsAbove p s) < Multiset.card (rootsAbove p s') := by
  rcases lt_or_eq_of_le (card_rootsAbove_mono p hss) with h | h
  · exact h
  · exact absurd (by rw [h]) hpar

/-- Consecutive powers of `-1` are distinct. -/
theorem neg_one_pow_ne_succ (i : ℕ) : (-1 : K) ^ i ≠ (-1 : K) ^ (i + 1) := by
  rw [pow_succ]
  rcases neg_one_pow_eq_or K i with h | h <;> rw [h] <;> norm_num

/-- A consecutive parity chain forces its thresholded root count above its index. -/
theorem card_ge_index {p : K[X]} (s : ℕ → K) (hmono : ∀ i, s i ≤ s (i + 1))
    (hpar : ∀ i, (-1 : K) ^ (Multiset.card (rootsAbove p (s i))) = (-1 : K) ^ i)
    (j : ℕ) : j ≤ Multiset.card (rootsAbove p (s j)) := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      have hne : (-1 : K) ^ (Multiset.card (rootsAbove p (s j)))
          ≠ (-1 : K) ^ (Multiset.card (rootsAbove p (s (j + 1)))) := by
        rw [hpar j, hpar (j + 1)]
        exact neg_one_pow_ne_succ j
      have hlt := card_lt_of_parity_ne (hmono j) hne
      lia

end RealRooted.RootCounting
