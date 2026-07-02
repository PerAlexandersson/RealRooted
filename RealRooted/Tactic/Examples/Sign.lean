import RealRooted.Tactic.Sign

/-!
# `rr_sign` examples

Regression tests for the coefficient-sign obligations that occur in OEIS
recurrence templates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) :
    (-(C c) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) :
    (-(C c) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) :
    (-(C c) * (1 + X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) :
    (C (-c) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hr : r ≤ 0) :
    (X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

end Tactic
end RealRooted
