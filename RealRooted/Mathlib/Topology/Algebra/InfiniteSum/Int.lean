import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Nonnegative integer tails

Upstream-shaped bounds that compare a nonnegative sum over `ℤ`, vanishing at
the central pair, with a natural-indexed majorant on its two tails.
-/

open Finset
open scoped BigOperators Topology

noncomputable section

namespace Finset

/-- A nonnegative natural-indexed finite sum is bounded by a uniform bound on
all initial segments. -/
theorem sum_le_of_nonneg_of_le_sum_range {ρ : ℕ → ℝ} (hρ : ∀ k, 0 ≤ ρ k) {c : ℝ}
    (hfin : ∀ N, ∑ k ∈ range N, ρ k ≤ c) (s : Finset ℕ) :
    ∑ k ∈ s, ρ k ≤ c := by
  refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hρ k))
    (hfin (s.sup id + 1))
  intro k hk
  rw [mem_range]
  exact Nat.lt_succ_of_le (le_sup (f := id) hk)

end Finset

namespace Real

/-- A nonnegative integer-indexed series vanishing at `0` and `-1` is bounded
by two copies of a nonnegative natural-indexed majorant for its positive and
negative tails. -/
theorem tsum_int_le_two_mul_tsum_nat {ρ : ℕ → ℝ} (hρ : ∀ k, 0 ≤ ρ k)
    (hsum : Summable ρ) {G : ℤ → ℝ} (hGsum : Summable G)
    (hGz : G 0 = 0) (hGm : G (-1) = 0)
    (hGpos : ∀ n : ℤ, 1 ≤ n → G n ≤ ρ (n - 1).toNat)
    (hGneg : ∀ n : ℤ, n ≤ -2 → G n ≤ ρ (-n - 2).toNat) :
    ∑' n : ℤ, G n ≤ 2 * ∑' k : ℕ, ρ k := by
  classical
  refine hGsum.tsum_le_of_sum_le (fun s => ?_)
  set s1 : Finset ℤ := s.filter (fun n => 1 ≤ n) with hs1
  set s2 : Finset ℤ := s.filter (fun n => n ≤ -2) with hs2
  have hmem1 : ∀ n, n ∈ s1 ↔ n ∈ s ∧ 1 ≤ n := by
    intro n
    rw [hs1, mem_filter]
  have hmem2 : ∀ n, n ∈ s2 ↔ n ∈ s ∧ n ≤ -2 := by
    intro n
    rw [hs2, mem_filter]
  have hdisj : Disjoint s1 s2 := by
    refine disjoint_left.mpr fun n hn1 hn2 => ?_
    rw [hmem1] at hn1
    rw [hmem2] at hn2
    lia
  have hsub : s1 ∪ s2 ⊆ s := by
    intro n hn
    rcases mem_union.mp hn with h | h
    · exact ((hmem1 n).mp h).1
    · exact ((hmem2 n).mp h).1
  have hzero : ∀ n ∈ s, n ∉ s1 ∪ s2 → G n = 0 := by
    intro n hn hnot
    have h1 : ¬ (1 ≤ n) := fun h =>
      hnot (mem_union.mpr (Or.inl ((hmem1 n).mpr ⟨hn, h⟩)))
    have h2 : ¬ (n ≤ -2) := fun h =>
      hnot (mem_union.mpr (Or.inr ((hmem2 n).mpr ⟨hn, h⟩)))
    have hle : n ≤ 0 := by lia
    have hge : -1 ≤ n := by lia
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact hGz
    · have hn : n = -1 := by lia
      rw [hn]
      exact hGm
  have heq : ∑ n ∈ s1 ∪ s2, G n = ∑ n ∈ s, G n := sum_subset hsub hzero
  have hb1 : ∑ n ∈ s1, G n ≤ ∑' k : ℕ, ρ k := by
    have hinj : Set.InjOn (fun n : ℤ => (n - 1).toNat) s1 := by
      intro a ha b hb hab
      have ha1 : 1 ≤ a := (hmem1 a).mp ha |>.2
      have hb1 : 1 ≤ b := (hmem1 b).mp hb |>.2
      have ha0 : 0 ≤ a - 1 := by lia
      have hb0 : 0 ≤ b - 1 := by lia
      have hab' : ((a - 1).toNat : ℤ) = ((b - 1).toNat : ℤ) := by
        exact_mod_cast hab
      rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] at hab'
      lia
    calc
      ∑ n ∈ s1, G n ≤ ∑ n ∈ s1, ρ ((n - 1).toNat) :=
        sum_le_sum fun n hn => hGpos n ((hmem1 n).mp hn).2
      _ = ∑ k ∈ s1.image (fun n : ℤ => (n - 1).toNat), ρ k :=
        (sum_image fun a ha b hb h => hinj ha hb h).symm
      _ ≤ ∑' k : ℕ, ρ k := hsum.sum_le_tsum _ fun k _ => hρ k
  have hb2 : ∑ n ∈ s2, G n ≤ ∑' k : ℕ, ρ k := by
    have hinj : Set.InjOn (fun n : ℤ => (-n - 2).toNat) s2 := by
      intro a ha b hb hab
      have ha2 : a ≤ -2 := (hmem2 a).mp ha |>.2
      have hb2 : b ≤ -2 := (hmem2 b).mp hb |>.2
      have ha0 : 0 ≤ -a - 2 := by lia
      have hb0 : 0 ≤ -b - 2 := by lia
      have hab' : ((-a - 2).toNat : ℤ) = ((-b - 2).toNat : ℤ) := by
        exact_mod_cast hab
      rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] at hab'
      lia
    calc
      ∑ n ∈ s2, G n ≤ ∑ n ∈ s2, ρ (-n - 2).toNat :=
        sum_le_sum fun n hn => hGneg n ((hmem2 n).mp hn).2
      _ = ∑ k ∈ s2.image (fun n : ℤ => (-n - 2).toNat), ρ k :=
        (sum_image fun a ha b hb h => hinj ha hb h).symm
      _ ≤ ∑' k : ℕ, ρ k := hsum.sum_le_tsum _ fun k _ => hρ k
  rw [← heq, sum_union hdisj]
  linarith

/-- The finite-range version of `tsum_int_le_two_mul_tsum_nat`, which avoids
requiring the natural-indexed majorant itself to be summable. -/
theorem tsum_int_le_two_mul_of_sum_range_le {ρ : ℕ → ℝ} (hρ : ∀ k, 0 ≤ ρ k)
    {c : ℝ} (hfin : ∀ N, ∑ k ∈ Finset.range N, ρ k ≤ c) {G : ℤ → ℝ}
    (hGsum : Summable G) (hGz : G 0 = 0) (hGm : G (-1) = 0)
    (hGpos : ∀ n : ℤ, 1 ≤ n → G n ≤ ρ (n - 1).toNat)
    (hGneg : ∀ n : ℤ, n ≤ -2 → G n ≤ ρ (-n - 2).toNat) :
    ∑' n : ℤ, G n ≤ 2 * c := by
  classical
  refine hGsum.tsum_le_of_sum_le fun s => ?_
  set s1 : Finset ℤ := s.filter (fun n => 1 ≤ n) with hs1
  set s2 : Finset ℤ := s.filter (fun n => n ≤ -2) with hs2
  have hmem1 : ∀ n, n ∈ s1 ↔ n ∈ s ∧ 1 ≤ n := by
    intro n
    rw [hs1, Finset.mem_filter]
  have hmem2 : ∀ n, n ∈ s2 ↔ n ∈ s ∧ n ≤ -2 := by
    intro n
    rw [hs2, Finset.mem_filter]
  have hdisj : Disjoint s1 s2 := by
    refine Finset.disjoint_left.mpr fun n hn1 hn2 => ?_
    rw [hmem1] at hn1
    rw [hmem2] at hn2
    lia
  have hsub : s1 ∪ s2 ⊆ s := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · exact ((hmem1 n).mp h).1
    · exact ((hmem2 n).mp h).1
  have hzero : ∀ n ∈ s, n ∉ s1 ∪ s2 → G n = 0 := by
    intro n hn hnot
    have h1 : ¬ (1 ≤ n) := fun h =>
      hnot (Finset.mem_union.mpr (Or.inl ((hmem1 n).mpr ⟨hn, h⟩)))
    have h2 : ¬ (n ≤ -2) := fun h =>
      hnot (Finset.mem_union.mpr (Or.inr ((hmem2 n).mpr ⟨hn, h⟩)))
    have hle : n ≤ 0 := by lia
    have hge : -1 ≤ n := by lia
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact hGz
    · have hn : n = -1 := by lia
      rw [hn]
      exact hGm
  have heq : ∑ n ∈ s1 ∪ s2, G n = ∑ n ∈ s, G n := Finset.sum_subset hsub hzero
  have hb1 : ∑ n ∈ s1, G n ≤ c := by
    have hinj : Set.InjOn (fun n : ℤ => (n - 1).toNat) s1 := by
      intro a ha b hb hab
      have ha1 : 1 ≤ a := (hmem1 a).mp ha |>.2
      have hb1 : 1 ≤ b := (hmem1 b).mp hb |>.2
      have ha0 : 0 ≤ a - 1 := by lia
      have hb0 : 0 ≤ b - 1 := by lia
      have hab' : ((a - 1).toNat : ℤ) = ((b - 1).toNat : ℤ) := by
        exact_mod_cast hab
      rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] at hab'
      lia
    calc
      ∑ n ∈ s1, G n ≤ ∑ n ∈ s1, ρ ((n - 1).toNat) :=
        Finset.sum_le_sum fun n hn => hGpos n ((hmem1 n).mp hn).2
      _ = ∑ k ∈ s1.image (fun n : ℤ => (n - 1).toNat), ρ k :=
        (Finset.sum_image fun a ha b hb h => hinj ha hb h).symm
      _ ≤ c := Finset.sum_le_of_nonneg_of_le_sum_range hρ hfin _
  have hb2 : ∑ n ∈ s2, G n ≤ c := by
    have hinj : Set.InjOn (fun n : ℤ => (-n - 2).toNat) s2 := by
      intro a ha b hb hab
      have ha2 : a ≤ -2 := (hmem2 a).mp ha |>.2
      have hb2 : b ≤ -2 := (hmem2 b).mp hb |>.2
      have ha0 : 0 ≤ -a - 2 := by lia
      have hb0 : 0 ≤ -b - 2 := by lia
      have hab' : ((-a - 2).toNat : ℤ) = ((-b - 2).toNat : ℤ) := by
        exact_mod_cast hab
      rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] at hab'
      lia
    calc
      ∑ n ∈ s2, G n ≤ ∑ n ∈ s2, ρ (-n - 2).toNat :=
        Finset.sum_le_sum fun n hn => hGneg n ((hmem2 n).mp hn).2
      _ = ∑ k ∈ s2.image (fun n : ℤ => (-n - 2).toNat), ρ k :=
        (Finset.sum_image fun a ha b hb h => hinj ha hb h).symm
      _ ≤ c := Finset.sum_le_of_nonneg_of_le_sum_range hρ hfin _
  rw [← heq, Finset.sum_union hdisj]
  linarith

end Real
