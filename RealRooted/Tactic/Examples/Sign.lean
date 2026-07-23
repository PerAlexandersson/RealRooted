import RealRooted.Tactic.Sign

/-!
# `rr_sign` examples

Regression tests for the coefficient-sign obligations that occur in OEIS
recurrence templates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c := by
  rr_sign_side

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {n : Nat} (hn : 1 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 1) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {n : Nat} (hn : 2 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n : ℝ) * ((n : ℝ) + 1)) / 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {n : Nat} (hn : 2 ≤ n) {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) - 1))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

/-- Expanded `-(1-X)^2` lag as it appears in some OEIS recurrences. -/
example {r : ℝ} :
    (C (-1 : ℝ) + C (2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} {q : ℝ[X]} (hr : r ≤ 0) (hq : 0 ≤ q.eval r) :
    (X * q : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} {q : ℝ[X]}
    (hc : 0 ≤ c) (hr : r ≤ 0) (hq : 0 ≤ q.eval r) :
    (C c * X * q : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {n m : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n + 1 : Nat) : ℝ) + 2 * m + 2)⁻¹ *
        (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hr : r ≤ -1) :
    (1 + X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ -1) :
    (C c * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hr : r ≤ 1) :
    (X - 1 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 1) :
    (C c * (X - 1) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ -1) :
    (-(C c) * X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hlo : -1 ≤ r) (hhi : r ≤ -(1 / 2 : ℝ)) :
    ((1 + X) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ -(1 / 2 : ℝ)) :
    (C c * (1 + X) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hr : r ≤ 0) :
    (X * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X * (1 - X) * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * X * (1 - X) * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X - X ^ 3 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * (X - X ^ 3) : ℝ[X]).eval r ≤ 0 := by
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

example {c r : ℝ} (hc : 0 ≤ c) :
    (-(C c) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {c r : ℝ} {q : ℝ[X]} (hc : 0 ≤ c) :
    (-(C c) * q ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {b c r : ℝ} (hdisc : b ^ 2 ≤ 4 * c) :
    (-(X ^ 2 + C b * X + C c) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

/-- `A181738`-style negative-definite quadratic lag. -/
example {r : ℝ} :
    (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ)) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {r : ℝ} (hr : r ≤ 0) :
    (X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

end Tactic
end RealRooted
