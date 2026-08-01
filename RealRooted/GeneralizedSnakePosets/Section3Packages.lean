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

/-- A squarecase recurrence package provides the computable Theorem 3.5
interface for its attached polynomial families. -/
theorem theorem35Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial h.P h.G :=
  h.recurrence

/-- A squarecase recurrence package also provides the predicate-form Theorem
3.5 interface. -/
theorem theorem35 {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    Theorem35GeneralizedSnakeRecurrenceStatement model.snakePolynomial h.P h.G :=
  theorem35_of_theorem35Computable h.recurrence

end SquarecaseRookRecurrencePackage

/-- Existence statement for a squarecase model equipped with the Section 3
inputs needed by the current Theorem 4.1 induction route. -/
def SquarecaseRookSection3Statement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem41Section3ComputableInputs model.snakePolynomial P G

/-- Existence statement for a squarecase model equipped with Section 3 inputs
where Lemma 3.4 is supplied in shifted nonnegative-parameter form. -/
def SquarecaseRookSection3ShiftedStatement
    (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem41Section3ComputableShiftedInputs model.snakePolynomial P G

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
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3Inputs h.inputs

/-- Feed a squarecase Section 3 package into the computable form of the
abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookModelTheorem41Statement model :=
  Theorem41InductionRouteComputable model.snakePolynomial h.P h.G
    h.lemma33 h.lemma34 h.recurrence

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

/-- Forget a shifted Section 3 data package to the corresponding existence
statement. -/
theorem shiftedStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookSection3ShiftedStatement model :=
  ⟨h.P, h.G, ⟨h.lemma33, h.lemma34, h.recurrence⟩⟩

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
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3ShiftedInputs h.shiftedInputs

/-- Feed a shifted squarecase Section 3 package into the computable form of
the abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3ShiftedPackage model) :
    SquarecaseRookModelTheorem41Statement model :=
  Theorem41InductionRouteComputable model.snakePolynomial h.P h.G
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

/-- Shifted squarecase Section 3 inputs imply the existing paper-shaped
Section 3 statement. -/
theorem squarecaseSection3Statement_of_shifted
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model) :
    SquarecaseRookSection3Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact ⟨P, G, theorem41Section3ComputableInputs_of_shifted hinputs⟩

/-- Section 3 inputs for a squarecase model include the Theorem 3.5 recurrence
input needed by the Braun--Jal induction. -/
theorem squarecaseRookRecurrenceStatement_of_section3Statement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookRecurrenceStatement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact ⟨P, G, hinputs.recurrence⟩

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3Statement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact theorem41_of_section3ComputableInputs hinputs

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3ComputableStatement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact Theorem41InductionRouteComputable model.snakePolynomial P G
    hinputs.lemma33 hinputs.lemma34 hinputs.recurrence

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3ShiftedStatement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_squarecaseSection3Statement
    (squarecaseSection3Statement_of_shifted hsection)

/-- A shifted statement-level squarecase Section 3 witness plus a computable
abstract induction route proves the non-nesting-rook Theorem 4.1 form. -/
theorem theorem41_of_squarecaseSection3ComputableShiftedStatement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact Theorem41InductionRouteComputable model.snakePolynomial P G
    hinputs.lemma33 (lemma34ModifiedNarayanaInterlacing_of_shifted hinputs.lemma34)
    hinputs.recurrence

/-- Statement that a chosen order-polytope `h^*` model agrees with the
non-nesting rook polynomial model for generalized snake words. -/
def OrderPolytopeHStarMatchesNonNestingRook
    (hStar M : SnakeWord → ℝ[X]) : Prop :=
  ∀ w : SnakeWord, hStar w = M w

/-- Final order-polytope `h^*` real-rootedness statement, isolated from the
rook-polynomial model. -/
def OrderPolytopeHStarRealRootedStatement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length → hStar w ≠ 0 ∧ (hStar w).Splits

/-- Final order-polytope `h^*` interlacing statement, isolated from the
rook-polynomial model. -/
def OrderPolytopeHStarInterlacesStatement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    Interlaces (hStar w.deleteFinal) (hStar w)

/-- Full order-polytope `h^*` form of Braun--Jal Theorem 4.1 after the
Stanley/Alexandersson--Jal matching interface has identified the `h^*`
polynomials with non-nesting rook polynomials. -/
def OrderPolytopeHStarTheorem41Statement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (hStar w ≠ 0 ∧ (hStar w).Splits) ∧
      Interlaces (hStar w.deleteFinal) (hStar w)

/-- The full order-polytope `h^*` Theorem 4.1 wrapper implies its
real-rootedness projection. -/
theorem orderPolytopeHStarRealRooted_of_hStarTheorem41
    {hStar : SnakeWord → ℝ[X]}
    (h : OrderPolytopeHStarTheorem41Statement hStar) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  exact (h hw).1

/-- The full order-polytope `h^*` Theorem 4.1 wrapper implies its interlacing
projection. -/
theorem orderPolytopeHStarInterlaces_of_hStarTheorem41
    {hStar : SnakeWord → ℝ[X]}
    (h : OrderPolytopeHStarTheorem41Statement hStar) :
    OrderPolytopeHStarInterlacesStatement hStar := by
  intro w hw
  exact (h hw).2

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  simpa [hmatch w] using
    nonNestingRook_ne_zero_and_splits_of_theorem41 hBJ (w := w) hw

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` interlacing wrapper. -/
theorem orderPolytopeHStarInterlaces_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarInterlacesStatement hStar := by
  intro w hw
  simpa [hmatch w, hmatch w.deleteFinal] using
    nonNestingRook_deleteFinal_interlaces_of_theorem41 hBJ (w := w) hw

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface gives
the full order-polytope `h^*` version of Braun--Jal Theorem 4.1. -/
theorem orderPolytopeHStarTheorem41_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarTheorem41Statement hStar := by
  intro w hw
  exact ⟨orderPolytopeHStarRealRooted_of_theorem41 hBJ hmatch hw,
    orderPolytopeHStarInterlaces_of_theorem41 hBJ hmatch hw⟩

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (theorem41_of_squarecaseSection3Statement hsection) hmatch

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the final `h^*` interlacing wrapper.
-/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (theorem41_of_squarecaseSection3Statement hsection) hmatch

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the full final `h^*` Theorem 4.1
wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (theorem41_of_squarecaseSection3Statement hsection) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (hsection.theorem41Computable) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` interlacing
wrapper. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (hsection.theorem41Computable) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the full final `h^*` Theorem 4.1
wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (hsection.theorem41Computable) hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hsection)
    hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
interlacing wrapper. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hsection)
    hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the full final `h^*`
Theorem 4.1 wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hsection)
    hmatch

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route and order-polytope matching proves `h^*` real-rootedness. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ShiftedStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_squarecaseSection3Statement
    (squarecaseSection3Statement_of_shifted hsection) hmatch

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route and order-polytope matching proves `h^*` interlacing. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ShiftedStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_squarecaseSection3Statement
    (squarecaseSection3Statement_of_shifted hsection) hmatch

/-- A shifted statement-level squarecase Section 3 witness plus the abstract
induction route and order-polytope matching proves the full `h^*` Theorem 4.1.
-/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ShiftedStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_squarecaseSection3Statement
    (squarecaseSection3Statement_of_shifted hsection) hmatch

/-- A shifted squarecase Section 3 package, a matching computable induction
route, and the order-polytope matching prove `h^*` real-rootedness. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ShiftedPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedPackage model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (hsection.theorem41Computable) hmatch

/-- A shifted squarecase Section 3 package, a matching computable induction
route, and the order-polytope matching prove `h^*` interlacing. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ShiftedPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedPackage model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (hsection.theorem41Computable) hmatch

/-- A shifted squarecase Section 3 package, a matching computable induction
route, and the order-polytope matching prove the full `h^*` Theorem 4.1. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ShiftedPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3ShiftedPackage model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (hsection.theorem41Computable) hmatch

end GeneralizedSnakePosets
end RealRooted
