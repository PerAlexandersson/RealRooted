import RealRooted.LiuOppositeSigns.XSub.QuarticCubicCommonRoot

/-!
# Quartic/cubic boundary statements

Proposition-valued interfaces for the normalized quartic/cubic boundary packages.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Strict-left-root and strictly negative right endpoint part of the remaining
quartic/cubic repeated-right boundary package. -/
def xSubQuarticCubicStrictLeftRepeatedRightBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a < b → b < c → c < d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w < 0 → 0 < μ →
          (u = v ∨ v = w) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Remaining boundary package for the normalized quartic/cubic terminal after
shared roots and the strict-side-root branch have been separated. -/
def xSubQuarticCubicSideBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (a = b ∨ b = c ∨ c = d ∨ u = v ∨ v = w ∨ d = 0 ∨ w = 0) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Repeated-left-root part of the remaining normalized quartic/cubic
boundary package. -/
def xSubQuarticCubicRepeatedLeftBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (a = b ∨ b = c ∨ c = d) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Repeated-right-root part of the remaining normalized quartic/cubic
boundary package. -/
def xSubQuarticCubicRepeatedRightBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (u = v ∨ v = w) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Endpoint-zero part of the remaining normalized quartic/cubic boundary
package. -/
def xSubQuarticCubicEndpointZeroBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (d = 0 ∨ w = 0) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Left-only endpoint-zero part of the normalized quartic/cubic boundary
package.  The right endpoint is assumed nonzero so that the double-zero corner
can be handled once, separately. -/
def xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          d = 0 → w ≠ 0 →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Right-only endpoint-zero part of the normalized quartic/cubic boundary
package.  The left endpoint is assumed nonzero so that the double-zero corner
can be handled once, separately. -/
def xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          w = 0 → d ≠ 0 →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits


end LiuOppositeSigns
end RealRooted
