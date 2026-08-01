import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosetsNarayana

/-!
# Braun--Jal Claim 7 for modified Narayana polynomials

This module combines the analytic Lemma 3.4 proof from the Turan development
with the endpoint-safe Claim 7 conversion.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- Braun--Jal Claim `(7)` for the concrete modified Narayana family.

The remaining hypotheses are intentionally explicit combinatorial inputs.
Equation `(2)` is the non-nesting-rook recurrence defining the auxiliary
family, while coefficientwise nonnegativity of `G n - G (n - 1)` comes from
the same board interpretation. We use these facts without formalizing the full
rook model; all analytic real-rootedness and interlacing steps are proved in
Lean. -/
theorem theorem41Claim7_modified
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1))) :
    Theorem41Claim7Statement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  theorem41Claim7_modified_of_section3 hrec2
    lemma34ModifiedNarayanaInterlacing_modified hH_nonneg

end GeneralizedSnakePosets
end RealRooted
