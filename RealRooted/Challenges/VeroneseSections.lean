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
name = "RealRooted.Challenges.VeroneseSections.veroneseSectionPolynomial_eq_zero_or_splits"
label = "Veronese sections preserve real-rootedness"
-->

<!-- realrooted-catalog-content -->
# Veronese sections

The $k$th $r$-Veronese section of a polynomial keeps the coefficients whose
indices are congruent to $k$ modulo $r$. Let $0 \leq k < r$. If a polynomial
with nonnegative coefficients splits over $\mathbb R$, then its $k$th
$r$-Veronese section is zero or splits over $\mathbb R$.
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
theorem veroneseSectionPolynomial_eq_zero_or_splits {r k : ℕ} (hk : k < r) {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hsplits : p.Splits) :
    veroneseSectionPolynomial r k p = 0 ∨ (veroneseSectionPolynomial r k p).Splits := by
  have hr : 0 < r := by lia
  rcases eq_or_ne p 0 with rfl | hp0
  · left
    ext n
    simp [RealRooted.coeff_veroneseSectionPolynomial hr]
  · exact RealRooted.isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix
      hr hk hp hp0 hsplits

end VeroneseSections
end Challenges
end RealRooted
