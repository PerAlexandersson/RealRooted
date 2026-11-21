module

public import RealRooted.ExponentialRows.PartialProducts
public import RealRooted.Mathlib.Algebra.Polynomial.NewtonPartialProducts
import Mathlib.Tactic

/-!
# Exponential rows for a real-rooted product

We formalize the partial-product recurrence for
`B(z) = c z² ∏ k < d, (z + ρ k)`, ordered by nondecreasing nonnegative `ρ`.
No set-partition model is used. The scalar rows and the partial products are defined
simultaneously; their exponential-generating-function characterization is not needed.

This is an original result from the unpublished discussion in RealRooted issue #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2415, Theorem C.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.ExponentialRows

/-- The two zero nodes followed by the nonnegative roots of the product factor. -/
noncomputable def productNodes (ρ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < 2 then 0 else ρ (k - 2)

/-- The monic product `z² ∏ k < d, (z + ρ k)`. -/
noncomputable def blockProduct (ρ : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∏ k ∈ range (d + 2), (X + C (productNodes ρ k))

/-- The exponential row defined by the Newton partial-product insertion recurrence.
The auxiliary coordinates are `V^(d+1), …, V¹`; the final coordinate is `F`. -/
noncomputable def productRow (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  partialProductRow (fun k => productNodes ρ (d + 1 - k))
    (fun k => c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - k))
    (d + 1) n

/-- Nonnegative parameters give nonnegative Newton nodes. -/
theorem productNodes_nonneg {ρ : ℕ → ℝ} (hρ : ∀ k, 0 ≤ ρ k) (k : ℕ) :
    0 ≤ productNodes ρ k := by
  unfold productNodes
  split_ifs
  · exact le_rfl
  · exact hρ _

/-- Ordered nonnegative parameters give ordered Newton nodes, including the two zero nodes. -/
theorem productNodes_monotone {ρ : ℕ → ℝ} (hρ : ∀ k, 0 ≤ ρ k)
    (hmono : Monotone ρ) : Monotone (productNodes ρ) := by
  intro i j hij
  unfold productNodes
  split_ifs with hi hj hj
  · exact le_rfl
  · exact hρ _
  · lia
  · exact hmono (Nat.sub_le_sub_right hij 2)

/-- The block polynomial is the expected double-zero product. -/
theorem blockProduct_eq (ρ : ℕ → ℝ) (d : ℕ) :
    blockProduct ρ d = X ^ 2 * ∏ k ∈ range d, (X + C (ρ k)) := by
  unfold blockProduct
  rw [show d + 2 = 2 + d by lia, prod_range_add]
  have hshift : (∏ k ∈ range d, (X + C (productNodes ρ (2 + k)))) =
      ∏ k ∈ range d, (X + C (ρ k)) := by
    apply prod_congr rfl
    intro k _
    simp [productNodes, show ¬ (2 + k < 2) by lia]
  rw [hshift]
  norm_num [prod_range_succ, productNodes, pow_two]

private lemma productRow_weights_nonneg {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d k : ℕ) :
    0 ≤ c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - k) :=
  mul_nonneg hc (newtonDerivativeCoeff_nonneg (productNodes_monotone hρ hmono) _ _)

private lemma productRow_weights_succ_le {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d k : ℕ) (hk : k + 1 < d + 1) :
    c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - (k + 1)) ≤
      productNodes ρ (d + 1 - k) *
        (c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - k)) := by
  have h := newtonDerivativeCoeff_le_mul_succ (productNodes_monotone hρ hmono)
    (productNodes_nonneg hρ) (n := d + 2) (j := d - k) (by lia)
  have hidx : d - k + 1 = d + 1 - k := by lia
  have hidx' : d + 1 - (k + 1) = d - k := by lia
  rw [hidx] at h
  rw [hidx']
  nlinarith [mul_le_mul_of_nonneg_left h hc]

/-- Every exponential row of a nonnegative real-rooted product is nonzero and real-rooted.
Zero root parameters and zero scale are included. -/
theorem productRow_isRealRooted {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    productRow c ρ d n ≠ 0 ∧ (productRow c ρ d n).Splits := by
  exact ⟨partialProductRow_ne_zero _ _ _ _,
    partialProductRow_splits (fun k => productNodes_nonneg hρ _) (m := d + 1)
      (fun k _ => productRow_weights_nonneg hc hρ hmono d k)
      (fun k hk => productRow_weights_succ_le hc hρ hmono d k hk) n⟩

/-- The exponential product rows interlace consecutively, with the earlier row on the left. -/
theorem productRow_strictInterl_succ {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    StrictInterl (productRow c ρ d n) (productRow c ρ d (n + 1)) := by
  exact partialProductRow_strictInterl_succ (fun k => productNodes_nonneg hρ _)
    (fun k _ => productRow_weights_nonneg hc hρ hmono d k)
    (fun k hk => productRow_weights_succ_le hc hρ hmono d k hk) n

/-- With at least one factor after `z²`, rows at distance two interlace. -/
theorem productRow_strictInterl_add_two {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    StrictInterl (productRow c ρ (d + 1) n) (productRow c ρ (d + 1) (n + 2)) := by
  apply partialProductRow_strictInterl_add_two
    (fun k => productNodes_nonneg hρ _)
    (fun k _ => productRow_weights_nonneg hc hρ hmono (d + 1) k)
    (fun k hk => productRow_weights_succ_le hc hρ hmono (d + 1) k hk)
  simp [productNodes]

/-- The positive-root case of Theorem C has only simple zeros. -/
theorem productRow_hasSimpleRoots {c : ℝ} (hc : 0 < c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    HasSimpleRoots (productRow c ρ d n) := by
  have hρ' : ∀ k, 0 ≤ ρ k := fun k => (hρ k).le
  apply partialProductRow_hasSimpleRoots (fun k => productNodes_nonneg hρ' _)
    (fun k _ => productRow_weights_nonneg hc.le hρ' hmono d k)
    (fun k hk => productRow_weights_succ_le hc.le hρ' hmono d k hk)
  simp only [Nat.add_sub_cancel_left]
  rw [newtonDerivativeCoeff_one (by simp [productNodes]) (by simp [productNodes])]
  apply mul_pos hc
  apply mul_pos zero_lt_two
  apply prod_pos
  intro k hk
  have hk' := (mem_Ico.mp hk).1
  simpa [productNodes, show ¬ k < 2 by lia] using hρ (k - 2)

/-- The distance-two conclusion of Theorem C, including the degree-two block product. -/
theorem productRow_strictInterl_add_two_all {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    StrictInterl (productRow c ρ d n) (productRow c ρ d (n + 2)) := by
  cases d with
  | zero =>
    apply partialProductRow_one_strictInterl_add_two (fun k => productNodes_nonneg hρ _)
    exact productRow_weights_nonneg hc hρ hmono 0 0
  | succ d => exact productRow_strictInterl_add_two hc hρ hmono d n

/-- Theorem C: the recurrence-defined rows have simple real zeros and both requested
interlacings. The displayed shifts put the earlier row on the left of `StrictInterl`. -/
theorem productRow_roots {c : ℝ} (hc : 0 < c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    IsSimpleRealRooted (productRow c ρ d n) ∧
      StrictInterl (productRow c ρ d n) (productRow c ρ d (n + 1)) ∧
      StrictInterl (productRow c ρ d n) (productRow c ρ d (n + 2)) := by
  have hρ' : ∀ k, 0 ≤ ρ k := fun k => (hρ k).le
  have hreal := productRow_isRealRooted hc.le hρ' hmono d n
  exact ⟨⟨hreal.1, hreal.2, productRow_hasSimpleRoots hc hρ hmono d n⟩,
    productRow_strictInterl_succ hc.le hρ' hmono d n,
    productRow_strictInterl_add_two_all hc.le hρ' hmono d n⟩

end RealRooted.ExponentialRows
