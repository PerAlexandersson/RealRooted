module

public import RealRooted.VeroneseMatrix

/-!
# Veronese sections challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "veronese-sections"
formalized = "2026-10-05"
references = [
  "AthanasiadisWagner2024x",
]

[[definitions]]
name = "RealRooted.veroneseSectionPolynomial"
module = "RealRooted.VeroneseSection"
label = "Veronese section"

[[theorems]]
name = "RealRooted.veroneseSectionPolynomial_eq_zero_or_splits"
module = "RealRooted.VeroneseMatrix"
label = "Veronese sections preserve real-rootedness"
headline = true
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

A stronger fully interlacing statement appears in [@AthanasiadisWagner2024x].
See also the
[Veronese sections on symmetricfunctions.com](sf:veroneseSectionsRealRooted).
<!-- /realrooted-catalog-content -->

Human statement:
sf:veroneseSectionsRealRooted

Catalog reference: the standard PF/TNN proof via Aissen--Schoenberg--Whitney.

This module exposes the checked matrix-recursion proof that Veronese sections
of real-rooted polynomials with nonnegative coefficients are real-rooted or
zero.  The cyclic matrix construction remains in `RealRooted.VeroneseMatrix`.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace VeroneseSections

end VeroneseSections
end Challenges
end RealRooted
