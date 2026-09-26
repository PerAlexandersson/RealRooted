import RealRooted.VeroneseMatrix

/-!
# Veronese sections challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "veronese-sections"

[[definitions]]
name = "RealRooted.Challenges.VeroneseSections.VeroneseSection"

[[definitions]]
name = "RealRooted.Challenges.VeroneseSections.NonnegativeRealRootedPolynomial"

[[theorems]]
name = "RealRooted.Challenges.VeroneseSections.preserve_realRooted_nonneg"
-->

<!-- realrooted-catalog-content -->
# Veronese sections

The `k`th `r`-Veronese section retains the coefficients whose indices are
congruent to `k` modulo `r` and compresses their exponents.  The selected
theorem proves that every section of a nonzero real-rooted polynomial with
nonnegative coefficients is either zero or real-rooted.  Its proof uses the
project’s Pólya-frequency and cyclic-matrix infrastructure.

## References

The result is a standard consequence of the Pólya-frequency characterization
and total nonnegativity.  See the
[Veronese-section discussion on symmetricfunctions.com](https://www.symmetricfunctions.com/polyaFrequency.htm#veroneseSectionsRealRooted).
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

/-- Challenge-facing name for the `k`th `r`-Veronese section of a polynomial. -/
noncomputable abbrev VeroneseSection (r k : ℕ) (p : ℝ[X]) : ℝ[X] :=
  veroneseSectionPolynomial r k p

/-- Challenge-facing input class for the Veronese-section theorem. -/
abbrev NonnegativeRealRootedPolynomial (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ p ≠ 0 ∧ p.Splits

/-- Veronese sections preserve real-rootedness for polynomials with
nonnegative coefficients, allowing the selected section to vanish. -/
theorem preserve_realRooted_nonneg :
    ∀ {r k : ℕ}, 0 < r → k < r → {p : ℝ[X]} →
      NonnegativeRealRootedPolynomial p →
        VeroneseSection r k p = 0 ∨
          (VeroneseSection r k p).Splits :=
  fun {_r} {_k} hr hk {_p} hp =>
    RealRooted.isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix
      hr hk hp.1 hp.2.1 hp.2.2

end VeroneseSections
end Challenges
end RealRooted
