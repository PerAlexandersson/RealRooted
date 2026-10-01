import RealRooted.VeroneseMatrix

/-!
# Veronese sections challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "veronese-sections"

[[definitions]]
name = "RealRooted.veroneseSectionPolynomial"
module = "RealRooted.VeroneseSection"
label = "Veronese section"

[[theorems]]
name = "RealRooted.Challenges.VeroneseSections.preserve_realRooted_nonneg"
label = "Veronese sections preserve real-rootedness"
-->

<!-- realrooted-catalog-content -->
# Veronese sections

The $k$th $r$-Veronese section of a polynomial keeps the coefficients whose
indices are congruent to $k$ modulo $r$. Every Veronese section of a nonzero
real-rooted polynomial with nonnegative coefficients is zero or real-rooted.
This follows from the Pólya frequency characterization and total
nonnegativity.

## References

See the
[Veronese sections on symmetricfunctions.com](https://www.symmetricfunctions.com/polyaFrequency.htm#veroneseSectionsRealRooted).
<!-- /realrooted-catalog-content -->

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
theorem preserve_realRooted_nonneg :
    ∀ {r k : ℕ}, 0 < r → k < r → {p : ℝ[X]} →
      HasNonnegCoeffs p → p ≠ 0 → p.Splits →
        veroneseSectionPolynomial r k p = 0 ∨
          (veroneseSectionPolynomial r k p).Splits :=
  fun {_r} {_k} hr hk {_p} hp hp0 hsplits =>
    RealRooted.isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix
      hr hk hp hp0 hsplits

end VeroneseSections
end Challenges
end RealRooted
