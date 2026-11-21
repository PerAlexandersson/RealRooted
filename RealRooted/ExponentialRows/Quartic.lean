module

public import RealRooted.ExponentialRows.RealRootedProduct
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Quartic exponential rows in the nonnegative-discriminant regime

For `a,b ≥ 0`, `c > 0`, and `b² ≥ 4ac`, the quadratic `a + bz + cz²` has two
nonpositive real zeros. We identify its ordered root parameters and apply the
partial-product recurrence. This includes `a = 0` and the repeated-root boundary.

Source: Theorem C and its quartic specialization in the unpublished RealRooted issue #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.ExponentialRows

/-- Ordered negated roots of `a + b z + c z²`, extended constantly after the second root. -/
noncomputable def quarticRoots (a b c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then (b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * c)
  else (b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * c)

/-- Quartic exponential rows, defined by the Newton partial-product recurrence. -/
noncomputable def quarticRow (a b c : ℝ) (n : ℕ) : ℝ[X] :=
  productRow c (quarticRoots a b c) 2 n

private lemma quarticRoots_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (k : ℕ) :
    0 ≤ quarticRoots a b c k := by
  have hs := Real.sqrt_nonneg (b ^ 2 - 4 * a * c)
  have hs_sq := Real.sq_sqrt (sub_nonneg.mpr hdisc)
  have hsb : Real.sqrt (b ^ 2 - 4 * a * c) ≤ b := by
    nlinarith [mul_nonneg ha hc.le]
  unfold quarticRoots
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr hsb) (by positivity)
  · positivity

private lemma quarticRoots_monotone (a b c : ℝ) (hc : 0 < c) :
    Monotone (quarticRoots a b c) := by
  intro i j hij
  unfold quarticRoots
  split_ifs with hi hj hj
  · exact le_rfl
  · apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]
  · lia
  · exact le_rfl

private lemma quarticRoots_sum (a b c : ℝ) (hc : c ≠ 0) :
    c * (quarticRoots a b c 0 + quarticRoots a b c 1) = b := by
  simp only [quarticRoots, Nat.one_ne_zero, ↓reduceIte]
  field_simp
  ring

private lemma quarticRoots_mul {a b c : ℝ} (hc : c ≠ 0)
    (hdisc : 4 * a * c ≤ b ^ 2) :
    c * (quarticRoots a b c 0 * quarticRoots a b c 1) = a := by
  have hs_sq := Real.sq_sqrt (sub_nonneg.mpr hdisc)
  simp only [quarticRoots, Nat.one_ne_zero, ↓reduceIte]
  generalize Real.sqrt (b ^ 2 - 4 * a * c) = s at *
  field_simp
  nlinarith

/-- The root parametrization gives exactly the requested quartic block polynomial. -/
theorem quartic_blockProduct_eq {a b c : ℝ} (hc : c ≠ 0)
    (hdisc : 4 * a * c ≤ b ^ 2) :
    C c * blockProduct (quarticRoots a b c) 2 =
      C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4 := by
  rw [blockProduct_eq]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  calc
    C c * (X ^ 2 * ((X + C (quarticRoots a b c 0)) *
        (X + C (quarticRoots a b c 1)))) =
        C (c * (quarticRoots a b c 0 * quarticRoots a b c 1)) * X ^ 2 +
          C (c * (quarticRoots a b c 0 + quarticRoots a b c 1)) * X ^ 3 + C c * X ^ 4 := by
      simp only [map_add, map_mul]
      ring
    _ = _ := by rw [quarticRoots_sum a b c hc, quarticRoots_mul hc hdisc]

/-- Quartic exponential rows are nonzero and real-rooted for nonnegative discriminant.
The degenerate case `a = 0` and equality in the discriminant bound are included. -/
theorem quarticRow_isRealRooted {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    quarticRow a b c n ≠ 0 ∧ (quarticRow a b c n).Splits :=
  productRow_isRealRooted hc.le (quarticRoots_nonneg ha hb hc hdisc)
    (quarticRoots_monotone a b c hc) 2 n

/-- Consecutive quartic rows interlace in the nonnegative-discriminant regime. -/
theorem quarticRow_strictInterl_succ {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    StrictInterl (quarticRow a b c n) (quarticRow a b c (n + 1)) :=
  productRow_strictInterl_succ hc.le (quarticRoots_nonneg ha hb hc hdisc)
    (quarticRoots_monotone a b c hc) 2 n

/-- Quartic rows at distance two interlace in the nonnegative-discriminant regime. -/
theorem quarticRow_strictInterl_add_two {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    StrictInterl (quarticRow a b c n) (quarticRow a b c (n + 2)) :=
  productRow_strictInterl_add_two hc.le (quarticRoots_nonneg ha hb hc hdisc)
    (quarticRoots_monotone a b c hc) 1 n

/-- Positive `a` makes every quartic row simple-rooted in this regime. -/
theorem quarticRow_hasSimpleRoots {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    HasSimpleRoots (quarticRow a b c n) := by
  have hnonneg := quarticRoots_nonneg ha.le hb hc hdisc
  have hprod : 0 < quarticRoots a b c 0 * quarticRoots a b c 1 := by
    have h := quarticRoots_mul hc.ne' hdisc
    nlinarith
  have h₀ : 0 < quarticRoots a b c 0 := by nlinarith [hnonneg 1]
  have h₁ : 0 < quarticRoots a b c 1 := by nlinarith [hnonneg 0]
  apply productRow_hasSimpleRoots hc _ (quarticRoots_monotone a b c hc) 2 n
  intro k
  by_cases hk : k = 0
  · simpa [hk] using h₀
  · simpa [quarticRoots, hk] using h₁

end RealRooted.ExponentialRows
