module

public import RealRooted.ExponentialRows.ProductInsertion
public import RealRooted.ExponentialRows.Quartic

/-!
# Quartic exponential rows on the standard insertion definition

We transfer the quartic corollary of Theorem C to the generic block-weight insertion
recurrence. Its checked exponential-formula identity identifies these same rows with
`n! [z^n] exp(z + t (a z² + b z³ + c z⁴))`.

Source: the unpublished RealRooted issue #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- The root-parametrized quartic row is the standard insertion row of the quartic weights. -/
theorem quarticRow_eq_insertionRow {a b c : ℝ} (hc : c ≠ 0)
    (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    quarticRow a b c n =
      insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n := by
  rw [quarticRow, productRow_eq_insertionRow, quartic_blockProduct_eq hc hdisc]

/-- Standard quartic insertion rows have only real zeros in the nonnegative-discriminant regime. -/
theorem insertionRow_isRealRooted_quartic {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    insertionRow w n ≠ 0 ∧ (insertionRow w n).Splits := by
  simpa only [quarticRow_eq_insertionRow hc.ne' hdisc] using
    quarticRow_isRealRooted ha hb hc hdisc n

/-- Standard quartic insertion rows interlace consecutively. -/
theorem insertionRow_strictInterl_quartic_succ {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    StrictInterl (insertionRow w n) (insertionRow w (n + 1)) := by
  simpa only [quarticRow_eq_insertionRow hc.ne' hdisc] using
    quarticRow_strictInterl_succ ha hb hc hdisc n

/-- Standard quartic insertion rows at distance two interlace. -/
theorem insertionRow_strictInterl_quartic_add_two {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    StrictInterl (insertionRow w n) (insertionRow w (n + 2)) := by
  simpa only [quarticRow_eq_insertionRow hc.ne' hdisc] using
    quarticRow_strictInterl_add_two ha hb hc hdisc n

/-- Positive quadratic constant coefficient gives simple zeros in every quartic insertion row. -/
theorem insertionRow_hasSimpleRoots_quartic {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 < c) (hdisc : 4 * a * c ≤ b ^ 2) (n : ℕ) :
    HasSimpleRoots
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n) := by
  simpa only [quarticRow_eq_insertionRow hc.ne' hdisc] using
    quarticRow_hasSimpleRoots ha hb hc hdisc n

/-- The standard quartic rows are the exact coefficients of the requested formal exponential. -/
theorem insertionRow_quartic_eq_exponential (a b c : ℝ) (n : ℕ) :
    insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n =
      C (n.factorial : ℝ) * PowerSeries.coeff n ((PowerSeries.exp ℝ[X]).subst
        (markedExponent (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4))) := by
  apply insertionRow_eq_marked_exponential
  · simp
  · simp

end RealRooted.ExponentialRows
