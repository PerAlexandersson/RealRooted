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
