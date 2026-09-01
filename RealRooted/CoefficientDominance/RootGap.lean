import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Root-free intervals and reciprocal gaps

Elementary conversion from a root-free interval in reciprocal scale to a gap
between consecutive positive magnitudes.
-/

namespace RealRooted.CoefficientDominance

/-- Bounds at both endpoints of a root-free interval yield a multiplicative
gap between consecutive reciprocal magnitudes. -/
theorem gap_of_count {x : ℕ → ℝ} {j : ℕ} {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hxj : 0 < x j) (hlow : 1 / s₁ < x (j - 1)) (hhigh : x j ≤ 1 / s₂)
    (hs₂ : 0 < s₂) :
    s₂ / s₁ ≤ x (j - 1) / x j := by
  have hinverse : (0 : ℝ) < 1 / s₂ := by positivity
  have hrewrite : s₂ / s₁ = (1 / s₁) / (1 / s₂) := by
    field_simp
  have hs₁_inverse : (0 : ℝ) < 1 / s₁ := by positivity
  rw [hrewrite, div_le_div_iff₀ hinverse hxj]
  nlinarith [hlow, hhigh, hxj, hinverse, hs₁_inverse]

/-- A root-free interval of ratio at least `exp 2` yields a logarithmic gap at
least two between consecutive reciprocal magnitudes. -/
theorem log_gap_ge {x : ℕ → ℝ} {j : ℕ} {s₁ s₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hxj : 0 < x j)
    (hlow : 1 / s₁ < x (j - 1)) (hhigh : x j ≤ 1 / s₂)
    (hratio : Real.exp 2 ≤ s₂ / s₁) :
    2 ≤ Real.log (x (j - 1) / x j) := by
  have hgap := gap_of_count hs₁ hxj hlow hhigh hs₂
  have hbound : Real.exp 2 ≤ x (j - 1) / x j := le_trans hratio hgap
  have hpositive : 0 < x (j - 1) / x j :=
    lt_of_lt_of_le (Real.exp_pos 2) hbound
  have hlog := Real.log_le_log (Real.exp_pos 2) hbound
  rwa [Real.log_exp] at hlog

end RealRooted.CoefficientDominance
