import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The logarithmic derivative of `p'` at a simple root

Let `p` split over a field and let `r` be a simple root of `p`, so that `p'(r) ≠ 0`. Writing
`p = (X - r) q`, one has `p'(r) = q(r)` and `p''(r) = 2 q'(r)`, while the roots of `q` are
those of `p` with `r` removed once. The split logarithmic-derivative identity for `q` then gives

```text
p''(r) / p'(r) = 2 · Σ_{z ∈ p.roots.erase r} 1 / (r - z).
```
-/

open Polynomial

namespace RealRooted

variable {K : Type*} [Field K] [DecidableEq K] {p : K[X]} {r : K}

/-- At a simple root `r` of a split polynomial `p`, the ratio `p''(r) / p'(r)` is twice the sum
of `1 / (r - z)` over the other roots `z` of `p`, counted with multiplicity. -/
theorem eval_derivative_derivative_div_eval_derivative_of_splits (hs : p.Splits)
    (hr : p.IsRoot r) (hr' : p.derivative.eval r ≠ 0) :
    p.derivative.derivative.eval r / p.derivative.eval r =
      2 * ((p.roots.erase r).map fun z => 1 / (r - z)).sum := by
  have hfactor := mul_divByMonic_eq_iff_isRoot.mpr hr
  have hq : (p /ₘ (X - C r)).eval r = p.derivative.eval r := by
    conv_rhs => rw [← hfactor]
    simp
  have hqs : (p /ₘ (X - C r)).Splits := by
    refine hs.of_dvd ?_ ⟨X - C r, ?_⟩
    · rintro rfl
      simp at hr'
    · rw [mul_comm, hfactor]
  rw [eval_derivative_derivative_of_isRoot hr, ← hq, mul_div_assoc,
    hqs.eval_derivative_div_eval_of_ne_zero (hq ▸ hr'), roots_divByMonic_X_sub_C hr]

end RealRooted
