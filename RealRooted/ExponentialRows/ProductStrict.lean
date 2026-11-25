module

public import RealRooted.ExponentialRows.ProductInsertion
import Mathlib.Tactic

/-!
# Genuine consecutive strictness for exponential product rows

The existing product-row theorem gives weak oriented interlacing and simplicity.
We expose its missing no-common-root conclusion, using the checked partial-product
invariant. Thus `StrictInterl` in the conclusions below is supplemented by
disjointness, which makes the alternation genuinely strict.

The cubic specialization includes complete-graph clustering with edge cap two.
Source: the unpublished arguments in RealRooted #2649 and #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- Positive product parameters exclude common roots of consecutive exponential rows. -/
theorem productRow_no_common_root {c : ℝ} (hc : 0 < c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    ∀ x, ¬ ((productRow c ρ d n).IsRoot x ∧
      (productRow c ρ d (n + 1)).IsRoot x) := by
  have hρ' : ∀ k, 0 ≤ ρ k := fun k => (hρ k).le
  apply partialProductRow_no_common_root (fun k => productNodes_nonneg hρ' _)
  · intro k _
    exact mul_nonneg hc.le
      (newtonDerivativeCoeff_nonneg (productNodes_monotone hρ' hmono) _ _)
  · intro k hk
    have h := newtonDerivativeCoeff_le_mul_succ (productNodes_monotone hρ' hmono)
      (productNodes_nonneg hρ') (n := d + 2) (j := d - k) (by lia)
    have hi : d - k + 1 = d + 1 - k := by lia
    have hj : d + 1 - (k + 1) = d - k := by lia
    rw [hi] at h
    rw [hj]
    nlinarith [mul_le_mul_of_nonneg_left h hc.le]
  · simp only [Nat.add_sub_cancel_left]
    rw [newtonDerivativeCoeff_one (by simp [productNodes]) (by simp [productNodes])]
    apply mul_pos hc
    apply mul_pos zero_lt_two
    apply prod_pos
    intro k hk
    have hk' := (mem_Ico.mp hk).1
    simpa [productNodes, show ¬ k < 2 by lia] using hρ (k - 2)

/-- Standard insertion rows of a positive real-rooted block product have genuinely
strict consecutive alternation: the oriented relation and disjoint real roots. -/
theorem insertionRow_strictInterl_of_blockProduct {c : ℝ} (hc : 0 < c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    let w := markedBlockWeights (C c * blockProduct ρ d)
    StrictInterl (insertionRow w n) (insertionRow w (n + 1)) ∧
      ∀ x, ¬ ((insertionRow w n).IsRoot x ∧ (insertionRow w (n + 1)).IsRoot x) := by
  refine ⟨(insertionRow_roots_of_blockProduct hc hρ hmono d n).2.1, ?_⟩
  simpa only [productRow_eq_insertionRow] using productRow_no_common_root hc hρ hmono d n

/-- Cubic exponential rows with positive pair weight strictly alternate consecutively.
The cubic weight may vanish, so the matching-polynomial endpoint is included. -/
theorem insertionRow_strictInterl_cubic {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3)
    StrictInterl (insertionRow w n) (insertionRow w (n + 1)) ∧
      ∀ x, ¬ ((insertionRow w n).IsRoot x ∧ (insertionRow w (n + 1)).IsRoot x) := by
  by_cases hb0 : b = 0
  · subst b
    simpa [blockProduct_eq] using insertionRow_strictInterl_of_blockProduct ha
      (ρ := fun _ => 1) (fun _ => zero_lt_one) (fun _ _ _ => le_rfl) 0 n
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have he : C b * blockProduct (fun _ => a / b) 1 =
        C a * X ^ 2 + C b * X ^ 3 := by
      simp only [blockProduct_eq, prod_range_one]
      calc
        _ = C (b * (a / b)) * X ^ 2 + C b * X ^ 3 := by
          simp only [map_mul]
          ring
        _ = _ := by rw [mul_div_cancel₀ a hb0]
    simpa only [he] using insertionRow_strictInterl_of_blockProduct hbp
      (ρ := fun _ => a / b) (fun _ => div_pos ha hbp) (fun _ _ _ => le_rfl) 1 n

/-- Cubic exponential rows have simple real zeros when the pair weight is positive. -/
theorem insertionRow_hasSimpleRoots_cubic {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) :
    HasSimpleRoots (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3)) n) := by
  have h := insertionRow_strictInterl_cubic ha hb n
  exact (h.1.hasSimpleRoots_of_no_common_root h.2).1

end RealRooted.ExponentialRows
