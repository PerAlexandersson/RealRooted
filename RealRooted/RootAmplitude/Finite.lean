import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite root-amplitude algebra

Algebraic formulas which reduce monotonicity of a finite root-amplitude product
to a comparison of distance products.
-/

namespace RealRooted.RootAmplitude

open Finset

noncomputable section

variable (g : ℕ → ℝ)

/-- The normalized amplitude at the `k`-th member of a finite positive sequence. -/
def amp (n k : ℕ) : ℝ :=
  ∏ j ∈ (range n).erase k, |1 - g k / g j|

/-- The product of distances from the `k`-th member to the others. -/
def gapProd (n k : ℕ) : ℝ :=
  ∏ j ∈ (range n).erase k, |g k - g j|

/-- Clearing denominators turns the amplitude product into the distance product. -/
theorem amp_mul_prod (n k : ℕ) (hpositive : ∀ i, 0 < g i) :
    amp g n k * ∏ j ∈ (range n).erase k, g j = gapProd g n k := by
  rw [amp, gapProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j _
  have hj : 0 < g j := hpositive j
  have hrewrite : |1 - g k / g j| * g j = |(1 - g k / g j) * g j| := by
    rw [abs_mul, abs_of_pos hj]
  have hdivision : (1 - g k / g j) * g j = g j - g k := by field_simp
  rw [hrewrite, hdivision]
  exact abs_sub_comm _ _

/-- The product over `range n` with one factor removed. -/
theorem prod_erase (n k : ℕ) (hindex : k < n) :
    (∏ j ∈ (range n).erase k, g j) * g k = ∏ j ∈ range n, g j := by
  rw [mul_comm]
  exact Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hindex)

/-- The amplitude in closed form, up to multiplication by the root product. -/
theorem amp_eq (n k : ℕ) (hindex : k < n) (hpositive : ∀ i, 0 < g i) :
    amp g n k * ∏ j ∈ range n, g j = g k * gapProd g n k := by
  rw [← prod_erase g n k hindex, ← mul_assoc, amp_mul_prod g n k hpositive, mul_comm]

/-- Amplitude monotonicity is equivalent to a comparison of distance products. -/
theorem amp_le_amp_iff (n k : ℕ) (hindex : k < n) (hnext : k + 1 < n)
    (hpositive : ∀ i, 0 < g i) :
    amp g n k ≤ amp g n (k + 1)
      ↔ g k * gapProd g n k ≤ g (k + 1) * gapProd g n (k + 1) := by
  have hproduct : 0 < ∏ j ∈ range n, g j :=
    Finset.prod_pos (fun j _ => hpositive j)
  constructor
  · intro h
    rw [← amp_eq g n k hindex hpositive, ← amp_eq g n (k + 1) hnext hpositive]
    exact mul_le_mul_of_nonneg_right h (le_of_lt hproduct)
  · intro h
    rw [← amp_eq g n k hindex hpositive, ← amp_eq g n (k + 1) hnext hpositive] at h
    exact le_of_mul_le_mul_right h hproduct

/-- Removing an in-range index splits a finite range into its lower and upper
parts. -/
theorem erase_range_eq (n k : ℕ) (hindex : k < n) :
    (range n).erase k = range k ∪ Ico (k + 1) n := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  lia

/-- Under strict monotonicity, the distance product splits into lower and upper
positive factors. -/
theorem gapProd_split (hstrict : StrictMono g) (n k : ℕ) (hindex : k < n) :
    gapProd g n k
      = (∏ j ∈ range k, (g k - g j)) * ∏ j ∈ Ico (k + 1) n, (g j - g k) := by
  have hdisjoint : Disjoint (range k) (Ico (k + 1) n) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    lia
  rw [gapProd, erase_range_eq n k hindex, Finset.prod_union hdisjoint]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro j hj
    have hlt : g j < g k := hstrict (Finset.mem_range.mp hj)
    exact abs_of_pos (by linarith)
  · refine Finset.prod_congr rfl ?_
    intro j hj
    have hlt : g k < g j := hstrict (Finset.mem_Ico.mp hj).1
    rw [abs_sub_comm]
    exact abs_of_pos (by linarith)

/-- Splits off the shared nearest-neighbor factor on the low side. -/
theorem prod_range_succ_split (k : ℕ) :
    ∏ j ∈ range (k + 1), (g (k + 1) - g j)
      = (g (k + 1) - g k) * ∏ j ∈ range k, (g (k + 1) - g j) := by
  rw [Finset.prod_range_succ]
  ring

/-- Splits off the shared nearest-neighbor factor on the high side. -/
theorem prod_Ico_split (n k : ℕ) (hnext : k + 1 < n) :
    ∏ j ∈ Ico (k + 1) n, (g j - g k)
      = (g (k + 1) - g k) * ∏ j ∈ Ico (k + 2) n, (g j - g k) := by
  rw [show Ico (k + 1) n = insert (k + 1) (Ico (k + 2) n) from ?_,
    Finset.prod_insert (by simp)]
  ext j
  simp only [Finset.mem_Ico, Finset.mem_insert]
  lia

/-- A core comparison of normalized distances implies amplitude monotonicity. -/
theorem amp_le_amp_of_core (hpositive : ∀ i, 0 < g i) (hstrict : StrictMono g)
    (n k : ℕ) (hnext : k + 1 < n)
    (hcore : ∏ j ∈ Ico (k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
      ≤ (1 + (g (k + 1) - g k) / g k)
          * ∏ j ∈ range k, (1 + (g (k + 1) - g k) / (g k - g j))) :
    amp g n k ≤ amp g n (k + 1) := by
  have hindex : k < n := by lia
  set D : ℝ := g (k + 1) - g k with hDdef
  have hD_positive : 0 < D := sub_pos.mpr (hstrict (Nat.lt_succ_self k))
  set Pbelow : ℝ := ∏ j ∈ range k, (g k - g j) with hPbelow
  set Pabove : ℝ := ∏ j ∈ Ico (k + 2) n, (g j - g (k + 1)) with hPabove
  set Rbelow : ℝ := ∏ j ∈ range k, (1 + D / (g k - g j)) with hRbelow
  set Rabove : ℝ := ∏ j ∈ Ico (k + 2) n, (1 + D / (g j - g (k + 1))) with hRabove
  have hbelow_positive : ∀ j ∈ range k, 0 < g k - g j := by
    intro j hj
    exact sub_pos.mpr (hstrict (Finset.mem_range.mp hj))
  have habove_positive : ∀ j ∈ Ico (k + 2) n, 0 < g j - g (k + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact sub_pos.mpr (hstrict (by lia : k + 1 < j))
  have hPbelow_positive : 0 < Pbelow := Finset.prod_pos hbelow_positive
  have hPabove_positive : 0 < Pabove := Finset.prod_pos habove_positive
  have hlow : ∏ j ∈ range k, (g (k + 1) - g j) = Pbelow * Rbelow := by
    rw [hPbelow, hRbelow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hnonzero := hbelow_positive j hj
    field_simp
    rw [hDdef]
    ring
  have hhigh : ∏ j ∈ Ico (k + 2) n, (g j - g k) = Pabove * Rabove := by
    rw [hPabove, hRabove, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hnonzero := habove_positive j hj
    field_simp
    rw [hDdef]
    ring
  have hcurrent : g (k + 1) = g k * (1 + D / g k) := by
    have hnonzero := hpositive k
    field_simp
    rw [hDdef]
    ring
  rw [amp_le_amp_iff g n k hindex hnext hpositive,
    gapProd_split g hstrict n k hindex, gapProd_split g hstrict n (k + 1) hnext,
    prod_Ico_split g n k hnext,
    show Ico (k + 1 + 1) n = Ico (k + 2) n from rfl,
    prod_range_succ_split g k, hlow, hhigh]
  nth_rewrite 2 [hcurrent]
  have hnonnegative : 0 ≤ g k * Pbelow * D * Pabove := by
    have hpositive_k := hpositive k
    positivity
  have hmul := mul_le_mul_of_nonneg_left hcore hnonnegative
  calc
    g k * (Pbelow * (D * (Pabove * Rabove))) = g k * Pbelow * D * Pabove * Rabove := by
      ring
    _ ≤ g k * Pbelow * D * Pabove * ((1 + D / g k) * Rbelow) := hmul
    _ = g k * (1 + D / g k) * (D * (Pbelow * Rbelow) * Pabove) := by ring

end

end RealRooted.RootAmplitude
