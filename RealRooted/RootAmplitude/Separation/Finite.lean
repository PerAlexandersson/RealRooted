import RealRooted.RootAmplitude.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite multiplicative separation

This file isolates the ordered-field algebra behind root-amplitude estimates.
A finite positive sequence is multiplicatively separated when each term is at
least a fixed factor times its predecessor.  Iterating that condition compares
the two halves of the amplitude product with a universal geometric staircase.

The analytic lower bound for the staircase is deliberately kept in
`RootAmplitude.Separation.Euler`.
-/

namespace RealRooted.RootAmplitude

open Finset

noncomputable section

/-- Multiplicative separation by `q` on the first `n` entries of a sequence. -/
def IsMultiplicativelySeparatedOn {K : Type*} [Mul K] [LE K]
    (q : K) (g : ℕ → K) (n : ℕ) : Prop :=
  ∀ i, i + 1 < n → q * g i ≤ g (i + 1)

namespace IsMultiplicativelySeparatedOn

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {q : K} {g : ℕ → K} {n : ℕ}

/-- Finite multiplicative separation iterates to any pair of in-range indices. -/
theorem pow_mul_le (hsep : IsMultiplicativelySeparatedOn q g n) (hq : 0 ≤ q)
    {i m : ℕ} (him : i + m < n) :
    q ^ m * g i ≤ g (i + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmul : q * (q ^ m * g i) ≤ q * g (i + m) :=
        mul_le_mul_of_nonneg_left (ih (by lia)) hq
      calc
        q ^ (m + 1) * g i = q * (q ^ m * g i) := by
          rw [pow_succ]
          ring
        _ ≤ q * g (i + m) := hmul
        _ ≤ g (i + m + 1) := hsep (i + m) (by lia)
        _ = g (i + (m + 1)) := by congr 1

/-- A later-to-earlier ratio dominates the corresponding power of the
separation factor. -/
theorem pow_le_ratio (hsep : IsMultiplicativelySeparatedOn q g n)
    (hq : 0 ≤ q) (hpos : ∀ i, i < n → 0 < g i)
    {i k : ℕ} (hik : i ≤ k) (hk : k < n) :
    q ^ (k - i) ≤ g k / g i := by
  have hi : i < n := lt_of_le_of_lt hik hk
  have hindex : i + (k - i) = k := by lia
  have hiter := hsep.pow_mul_le hq (i := i) (m := k - i) (by simpa [hindex] using hk)
  rw [hindex] at hiter
  rw [le_div_iff₀ (hpos i hi)]
  exact hiter

/-- A separation factor strictly larger than one makes the finite sequence
strictly increasing. -/
theorem strictMonoOnRange (hsep : IsMultiplicativelySeparatedOn q g n)
    (hq : 1 < q) (hpos : ∀ i, i < n → 0 < g i) :
    ∀ i j, i < j → j < n → g i < g j := by
  intro i j hij hj
  have hq0 : 0 ≤ q := le_trans zero_le_one hq.le
  have hpow : q ^ (j - i) ≤ g j / g i :=
    hsep.pow_le_ratio hq0 hpos hij.le hj
  have hdiff : 0 < j - i := Nat.sub_pos_of_lt hij
  have hqpow : 1 < q ^ (j - i) := one_lt_pow₀ hq hdiff.ne'
  have hratio : 1 < g j / g i := lt_of_lt_of_le hqpow hpow
  exact (one_lt_div (hpos i (lt_trans hij hj))).mp hratio

end IsMultiplicativelySeparatedOn

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The universal upper-half staircase associated with a separation factor. -/
def staircaseProd (q : K) (N : ℕ) : K :=
  ∏ j ∈ range N, (1 - (q ^ (j + 1))⁻¹)

/-- The factors below a distinguished entry dominate the lower geometric
staircase. -/
theorem staircaseProd_below {q : K} (hq : 1 ≤ q) {g : ℕ → K} {n k : ℕ}
    (hpos : ∀ i, i < n → 0 < g i)
    (hsep : IsMultiplicativelySeparatedOn q g n) (hk : k < n) :
    ∏ j ∈ range k, (q ^ (j + 1) - 1)
      ≤ ∏ i ∈ range k, (g k / g i - 1) := by
  have hreflect :
      ∏ j ∈ range k, (q ^ ((k - 1 - j) + 1) - 1)
        = ∏ j ∈ range k, (q ^ (j + 1) - 1) :=
    Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) k
  rw [← hreflect]
  refine Finset.prod_le_prod ?_ ?_
  · intro i hi
    have hnonneg : (1 : K) ≤ q ^ ((k - 1 - i) + 1) := one_le_pow₀ hq
    linarith
  · intro i hi
    have hik : i < k := mem_range.mp hi
    have hidx : (k - 1 - i) + 1 = k - i := by lia
    rw [hidx]
    have hratio := hsep.pow_le_ratio (le_trans zero_le_one hq) hpos hik.le hk
    linarith

/-- The factors above a distinguished entry dominate the upper geometric
staircase. -/
theorem staircaseProd_above {q : K} (hq : 1 ≤ q) {g : ℕ → K} {n k N : ℕ}
    (hpos : ∀ i, i < n → 0 < g i)
    (hsep : IsMultiplicativelySeparatedOn q g n)
    (hkN : k + N < n) :
    staircaseProd q N
      ≤ ∏ j ∈ range N, (1 - g k / g (k + 1 + j)) := by
  unfold staircaseProd
  refine Finset.prod_le_prod ?_ ?_
  · intro j _
    have hqpow : (1 : K) ≤ q ^ (j + 1) := one_le_pow₀ hq
    have hqpowPos : (0 : K) < q ^ (j + 1) :=
      lt_of_lt_of_le zero_lt_one hqpow
    have hinv : (q ^ (j + 1))⁻¹ ≤ 1 := by
      exact (inv_le_one₀ hqpowPos).mpr hqpow
    linarith
  · intro j hj
    have hjN : j < N := mem_range.mp hj
    have hk : k < n := by lia
    have hfuture : k + 1 + j < n := by lia
    have hratio := hsep.pow_le_ratio (le_trans zero_le_one hq) hpos
      (show k ≤ k + 1 + j by lia) hfuture
    have hidx : (k + 1 + j) - k = j + 1 := by lia
    rw [hidx] at hratio
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hqpow : 0 < q ^ (j + 1) := pow_pos hqpos _
    have hmul : q ^ (j + 1) * g k ≤ g (k + 1 + j) := by
      rw [le_div_iff₀ (hpos k hk)] at hratio
      exact hratio
    have hquot : g k / g (k + 1 + j) ≤ (q ^ (j + 1))⁻¹ := by
      rw [div_le_iff₀ (hpos _ hfuture), inv_mul_eq_div, le_div_iff₀ hqpow]
      simpa [mul_comm] using hmul
    linarith

/-- The powers in the lower staircase multiply to the triangular power. -/
theorem prod_pow_succ {L : Type*} [CommMonoid L] (q : L) (k : ℕ) :
    ∏ j ∈ range k, q ^ (j + 1) = q ^ (k * (k + 1) / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih, ← pow_add]
      congr 1
      lia

/-- The lower staircase is a triangular power times the upper staircase. -/
theorem prod_sub_one_eq_staircaseProd {L : Type*} [Field L]
    {q : L} (hq : q ≠ 0) (k : ℕ) :
    ∏ j ∈ range k, (q ^ (j + 1) - 1)
      = q ^ (k * (k + 1) / 2) * staircaseProd q k := by
  have hfactor : ∀ j ∈ range k,
      q ^ (j + 1) - 1 = q ^ (j + 1) * (1 - (q ^ (j + 1))⁻¹) := by
    intro j _
    field_simp [pow_ne_zero _ hq]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib,
    prod_pow_succ, staircaseProd]

/-- The amplitude product splits into its lower and upper factors along a
positive strictly increasing finite sequence. -/
theorem amp_eq_lower_mul_upper (g : ℕ → ℝ) (n k : ℕ) (hk : k < n)
    (hpos : ∀ i, i < n → 0 < g i)
    (hstrict : ∀ i j, i < j → j < n → g i < g j) :
    amp g n k
      = (∏ i ∈ range k, (g k / g i - 1))
        * ∏ j ∈ range (n - k - 1), (1 - g k / g (k + 1 + j)) := by
  classical
  have hdisjoint : Disjoint (range k) (Ico (k + 1) n) := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy h'y
    rw [mem_range] at hy
    rw [Finset.mem_Ico] at h'y
    lia
  rw [amp, erase_range_eq n k hk, Finset.prod_union hdisjoint]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro i hi
    rw [mem_range] at hi
    have hgi : 0 < g i := hpos i (by lia)
    have hlt : g i < g k := hstrict i k hi hk
    rw [abs_of_neg]
    · ring
    · rw [sub_neg]
      exact (one_lt_div hgi).mpr hlt
  · have hreindex : Ico (k + 1) n
        = (range (n - k - 1)).image (fun j => k + 1 + j) := by
      ext y
      simp only [Finset.mem_Ico, Finset.mem_image, mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨y - (k + 1), by lia, by lia⟩
      · rintro ⟨j, hj, rfl⟩
        lia
    rw [hreindex, Finset.prod_image (fun a _ b _ h => by lia)]
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [mem_range] at hj
    have hgk : 0 < g k := hpos k hk
    have hfuture : k + 1 + j < n := by lia
    have hlt : g k < g (k + 1 + j) :=
      hstrict k (k + 1 + j) (by lia) hfuture
    have hgj : 0 < g (k + 1 + j) := hpos _ hfuture
    rw [abs_of_pos]
    rw [sub_pos]
    exact (div_lt_one hgj).mpr hlt

end

end RealRooted.RootAmplitude
