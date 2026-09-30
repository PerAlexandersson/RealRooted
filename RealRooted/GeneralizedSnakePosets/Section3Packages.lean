import RealRooted.GeneralizedSnakePosets.Statements

/-!
# Braun--Jal Section 3 packages

This module bundles the Section 3 recurrence and interlacing inputs used to
feed the abstract Braun--Jal Theorem 4.1 induction route.  It also contains the
order-polytope `h^*` statement wrappers that sit above the non-nesting rook
polynomial model.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

universe u

/-! ## Squarecase recurrence packages -/

/-- Existence statement for a squarecase model satisfying the computable
Braun--Jal Theorem 3.5 recurrence for some Section 3 families `P` and `G`. -/
def SquarecaseRookRecurrenceStatement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

/-- Data package for a concrete squarecase/non-nesting rook recurrence.

Later board files should construct this from the actual squarecase board model
and Braun--Jal's positive recurrence. -/
structure SquarecaseRookRecurrencePackage (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookRecurrencePackage

/-- Forget a recurrence data package to the corresponding existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    SquarecaseRookRecurrenceStatement model :=
  ⟨h.P, h.G, h.recurrence⟩

end SquarecaseRookRecurrencePackage

/-- Existence statement for a squarecase model equipped with the Section 3
inputs needed by the current Theorem 4.1 induction route. -/
def SquarecaseRookSection3Statement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem41Section3ComputableInputs model.snakePolynomial P G

/-- Data package for the squarecase/non-nesting rook model together with the
Narayana and recurrence inputs from Braun--Jal Section 3. -/
structure SquarecaseRookSection3Package (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookSection3Package

/-- The recurrence component of a Section 3 package as a standalone squarecase
recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Forget a Section 3 data package to the corresponding existence statement.
-/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookSection3Statement model :=
  ⟨h.P, h.G, ⟨h.lemma33, h.lemma34, h.recurrence⟩⟩

/-- A squarecase Section 3 package provides the existing computable input
bundle for the attached polynomial families. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    Theorem41Section3ComputableInputs model.snakePolynomial h.P h.G where
  lemma33 := h.lemma33
  lemma34 := h.lemma34
  recurrence := h.recurrence

/-- A squarecase Section 3 package provides the predicate-form input bundle for
the attached polynomial families. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    Theorem41Section3Inputs model.snakePolynomial h.P h.G :=
  theorem41Section3Inputs_of_computable h.computableInputs

/-- Feed a squarecase Section 3 package into the abstract Theorem 4.1 induction
route. -/
theorem theorem41 {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model)
    (hroute : Theorem41InductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3Inputs hroute h.inputs

/-- Feed a squarecase Section 3 package into the computable form of the
abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  hroute h.lemma33 h.lemma34 h.recurrence

/-- A squarecase Section 3 package also gives the standalone recurrence
existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookSection3Package

/-- Data package for the squarecase/non-nesting rook model when Lemma 3.4 is
proved in shifted nonnegative-parameter form. -/
structure SquarecaseRookSection3ShiftedPackage
    (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaShiftedInterlacingStatement P
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookSection3ShiftedPackage

/-- Convert a shifted Section 3 package to the existing paper-shaped Section 3
package. -/
def section3Package {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookSection3Package model where
  P := h.P
  G := h.G
  lemma33 := h.lemma33
  lemma34 := lemma34ModifiedNarayanaInterlacing_of_shifted h.lemma34
  recurrence := h.recurrence

/-- A shifted Section 3 package also gives the existing paper-shaped existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookSection3Statement model :=
  h.section3Package.statement

/-- A shifted Section 3 package provides the computable shifted input bundle.
-/
theorem computableShiftedInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3ComputableShiftedInputs
      model.snakePolynomial h.P h.G where
  lemma33 := h.lemma33
  lemma34 := h.lemma34
  recurrence := h.recurrence

/-- A shifted Section 3 package provides the paper-shaped computable input
bundle. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3ComputableInputs model.snakePolynomial h.P h.G :=
  theorem41Section3ComputableInputs_of_shifted h.computableShiftedInputs

/-- A shifted Section 3 package provides the predicate-form shifted input
bundle. -/
theorem shiftedInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3ShiftedInputs model.snakePolynomial h.P h.G :=
  theorem41Section3ShiftedInputs_of_computable h.computableShiftedInputs

/-- A shifted Section 3 package provides the existing predicate-form input
bundle. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    Theorem41Section3Inputs model.snakePolynomial h.P h.G :=
  theorem41Section3Inputs_of_shifted h.shiftedInputs

/-- The recurrence component of a shifted Section 3 package as a standalone
squarecase recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Feed a shifted squarecase Section 3 package into the abstract Theorem 4.1
induction route. -/
theorem theorem41 {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model)
    (hroute : Theorem41InductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3ShiftedInputs hroute h.shiftedInputs

/-- Feed a shifted squarecase Section 3 package into the computable form of
the abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model)
    (hroute :
      Theorem41InductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  hroute
    h.lemma33
    (lemma34ModifiedNarayanaInterlacing_of_shifted h.lemma34)
    h.recurrence

/-- A shifted squarecase Section 3 package also gives the standalone
recurrence existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookSection3ShiftedPackage

end GeneralizedSnakePosets
end RealRooted
