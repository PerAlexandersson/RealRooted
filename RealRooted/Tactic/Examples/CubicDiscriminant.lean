import RealRooted.Tactic.CubicDiscriminant

/-!
# Cubic-discriminant tactic examples

Small regression examples for discriminant split criteria.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]}
    (hdeg : p.natDegree = 2)
    (hdisc : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)) :
    p.Splits := by
  rr_quadratic_splits_discriminant using
    degree := hdeg,
    discriminant := hdisc

example {p : ℝ[X]}
    (hdeg : p.natDegree = 3)
    (hdisc : 0 ≤ cubicDiscr p) :
    p.Splits := by
  rr_cubic_splits_discriminant using
    degree := hdeg,
    discriminant := hdisc

example {p : ℝ[X]}
    (hdeg : p.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr p) :
    p.Splits := by
  rr_natDegree_le_three_splits_discriminant using
    degree := hdeg,
    discriminant := hdisc

example {p : ℝ[X]} (hdeg : p.natDegree ≤ 3) :
    0 ≤ cubicDiscr p ↔ p.Splits := by
  rr_cubic_discriminant_iff_splits using
    degree := hdeg

end Tactic
end RealRooted
