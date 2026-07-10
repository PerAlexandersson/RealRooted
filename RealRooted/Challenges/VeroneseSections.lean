import RealRooted.VeroneseMatrix

/-!
# Veronese sections challenge entry point

Human statement:
https://www.symmetricfunctions.com/polyaFrequency.htm#veroneseSectionsRealRooted

Catalog reference: the standard PF/TNN proof via Aissen--Schoenberg--Whitney.

This module exposes the checked matrix-recursion proof that Veronese sections
of real-rooted polynomials with nonnegative coefficients are real-rooted or
zero.  The cyclic matrix construction remains in `RealRooted.VeroneseMatrix`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace VeroneseSections

/-- Veronese sections preserve real-rootedness for polynomials with
nonnegative coefficients, allowing the selected section to vanish. -/
theorem preserve_realRooted_nonneg
    {r k : ℕ} (hr : 0 < r) (hk : k < r) {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hp_ne : p ≠ 0) (hp_splits : p.Splits) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits :=
  RealRooted.isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix
    hr hk hpnn hp_ne hp_splits

end VeroneseSections
end Challenges
end RealRooted
