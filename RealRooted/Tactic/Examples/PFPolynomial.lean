import RealRooted.Tactic.PFPolynomial

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasNonnegCoeffs p := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p = 0 ∨ p.Splits := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p.Splits := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    ∀ r ∈ p.roots, r ≤ 0 := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0) :
    p ≠ 0 ∧ p.Splits := by
  rr_pf using
    pf := hp,
    nonzero := hp0

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPolyaFreqSeq p.coeff := by
  rr_pf using pf := hp

end Tactic
end RealRooted
