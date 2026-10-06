import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Nonnegativity of real polynomials by continuity

A real polynomial that is nonnegative away from a single point is nonnegative
everywhere, since polynomial evaluation is continuous and the punctured
neighbourhoods of a real number are nontrivial. This is a candidate for
upstreaming to `Mathlib.Analysis.Polynomial.Basic`.
-/

open Filter Topology

namespace Polynomial

/-- A real polynomial that is nonnegative at every point other than `r` is
nonnegative everywhere. -/
theorem eval_nonneg_of_forall_ne {p : ℝ[X]} {r : ℝ}
    (h : ∀ t, t ≠ r → 0 ≤ p.eval t) (t : ℝ) : 0 ≤ p.eval t := by
  rcases ne_or_eq t r with ht | rfl
  · exact h t ht
  · exact ge_of_tendsto ((p.continuous.tendsto t).mono_left (nhdsWithin_le_nhds (s := {t}ᶜ)))
      (eventually_nhdsWithin_of_forall h)

end Polynomial
