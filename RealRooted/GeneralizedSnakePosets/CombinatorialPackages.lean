import RealRooted.GeneralizedSnakePosets.Statements

/-!
# The combinatorial packages

This module bundles combinatorial recurrence and interlacing inputs used to
feed the abstract snake-interlacing induction route.  It also contains the
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
the snake-recurrence recurrence for some combinatorial families `P` and `G`. -/
def SquarecaseRookRecurrenceStatement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

/-- Data package for a concrete squarecase/non-nesting rook recurrence.

Later board files should construct this from the actual squarecase board model
and Braun--Jal's positive recurrence. -/
structure SquarecaseRookRecurrencePackage (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  recurrence :
    GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookRecurrencePackage

/-- Forget a recurrence data package to the corresponding existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    SquarecaseRookRecurrenceStatement model :=
  ⟨h.P, h.G, h.recurrence⟩

end SquarecaseRookRecurrencePackage

/-- Existence statement for a squarecase model equipped with the combinatorial
inputs needed by the current snake-interlacing induction route. -/
def SquarecaseRookCombinatorialStatement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    SnakeInterlacingComputableInputs model.snakePolynomial P G

/-- Data package for the squarecase/non-nesting rook model together with the
Narayana and recurrence inputs from the combinatorial inputs. -/
structure SquarecaseRookCombinatorialPackage (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  auxiliaryGInterlacing : AuxiliaryGInterlacesStatement P G
  affineNarayana : AffineModifiedNarayanaInterlacingStatement P
  recurrence :
    GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookCombinatorialPackage

/-- The recurrence component of a combinatorial package as a standalone squarecase
recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Forget a combinatorial data package to the corresponding existence statement.
-/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model) :
    SquarecaseRookCombinatorialStatement model :=
  ⟨h.P, h.G, ⟨h.auxiliaryGInterlacing, h.affineNarayana, h.recurrence⟩⟩

/-- A squarecase combinatorial package provides the existing computable input
bundle for the attached polynomial families. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model) :
    SnakeInterlacingComputableInputs model.snakePolynomial h.P h.G where
  auxiliaryGInterlacing := h.auxiliaryGInterlacing
  affineNarayana := h.affineNarayana
  recurrence := h.recurrence

/-- A squarecase combinatorial package provides the predicate-form input bundle for
the attached polynomial families. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model) :
    SnakeInterlacingInputs model.snakePolynomial h.P h.G :=
  snakeInterlacingInputs_of_computable h.computableInputs

/-- Feed a squarecase combinatorial package into the abstract snake-interlacing induction
route. -/
theorem snakeInterlacing {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model)
    (hroute : SnakeInterlacingInductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelSnakeInterlacingStatement model :=
  snakeInterlacing_of_combinatorialInputs hroute h.inputs

/-- Feed a squarecase combinatorial package into the computable form of the
abstract snake-interlacing induction route. -/
theorem snakeInterlacingComputable {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model)
    (hroute :
      SnakeInterlacingInductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelSnakeInterlacingStatement model :=
  hroute h.auxiliaryGInterlacing h.affineNarayana h.recurrence

/-- A squarecase combinatorial package also gives the standalone recurrence
existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialPackage model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookCombinatorialPackage

/-- Data package for the squarecase/non-nesting rook model when the affine Narayana interlacing
lemma is
proved in shifted nonnegative-parameter form. -/
structure SquarecaseRookCombinatorialShiftedPackage
    (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  auxiliaryGInterlacing : AuxiliaryGInterlacesStatement P G
  affineNarayana : AffineModifiedNarayanaShiftedInterlacingStatement P
  recurrence :
    GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookCombinatorialShiftedPackage

/-- Convert a shifted combinatorial package to the existing paper-shaped combinatorial
package. -/
def combinatorialPackage {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SquarecaseRookCombinatorialPackage model where
  P := h.P
  G := h.G
  auxiliaryGInterlacing := h.auxiliaryGInterlacing
  affineNarayana := affineModifiedNarayanaInterlacing_of_shifted h.affineNarayana
  recurrence := h.recurrence

/-- A shifted combinatorial package also gives the existing paper-shaped existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SquarecaseRookCombinatorialStatement model :=
  h.combinatorialPackage.statement

/-- A shifted combinatorial package provides the computable shifted input bundle.
-/
theorem computableShiftedInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SnakeInterlacingComputableShiftedInputs
      model.snakePolynomial h.P h.G where
  auxiliaryGInterlacing := h.auxiliaryGInterlacing
  affineNarayana := h.affineNarayana
  recurrence := h.recurrence

/-- A shifted combinatorial package provides the paper-shaped computable input
bundle. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SnakeInterlacingComputableInputs model.snakePolynomial h.P h.G :=
  snakeInterlacingComputableInputs_of_shifted h.computableShiftedInputs

/-- A shifted combinatorial package provides the predicate-form shifted input
bundle. -/
theorem shiftedInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SnakeInterlacingShiftedInputs model.snakePolynomial h.P h.G :=
  snakeInterlacingShiftedInputs_of_computable h.computableShiftedInputs

/-- A shifted combinatorial package provides the existing predicate-form input
bundle. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SnakeInterlacingInputs model.snakePolynomial h.P h.G :=
  snakeInterlacingInputs_of_shifted h.shiftedInputs

/-- The recurrence component of a shifted combinatorial package as a standalone
squarecase recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Feed a shifted squarecase combinatorial package into the abstract snake-interlacing
induction route. -/
theorem snakeInterlacing {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model)
    (hroute : SnakeInterlacingInductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelSnakeInterlacingStatement model :=
  snakeInterlacing_of_combinatorialShiftedInputs hroute h.shiftedInputs

/-- Feed a shifted squarecase combinatorial package into the computable form of
the abstract snake-interlacing induction route. -/
theorem snakeInterlacingComputable {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model)
    (hroute :
      SnakeInterlacingInductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelSnakeInterlacingStatement model :=
  hroute
    h.auxiliaryGInterlacing
    (affineModifiedNarayanaInterlacing_of_shifted h.affineNarayana)
    h.recurrence

/-- A shifted squarecase combinatorial package also gives the standalone
recurrence existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookCombinatorialShiftedPackage model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookCombinatorialShiftedPackage

/-- The combinatorial inputs for a squarecase model include snake-recurrence recurrence
input needed by the Braun--Jal induction. -/
theorem squarecaseRookRecurrenceStatement_of_combinatorialStatement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookCombinatorialStatement model) :
    SquarecaseRookRecurrenceStatement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact ⟨P, G, hinputs.recurrence⟩

/-- A statement-level squarecase combinatorial witness plus the abstract induction
route proves the non-nesting-rook form of the snake interlacing theorem. -/
theorem snakeInterlacing_of_squarecaseCombinatorialStatement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        SnakeInterlacingInductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookCombinatorialStatement model) :
    SquarecaseRookModelSnakeInterlacingStatement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact snakeInterlacing_of_combinatorialComputableInputs (hroute P G) hinputs

/-- A statement-level squarecase combinatorial witness plus a computable abstract
induction route proves the non-nesting-rook form of the snake interlacing theorem. -/
theorem snakeInterlacing_of_squarecaseCombinatorialComputableStatement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        SnakeInterlacingInductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookCombinatorialStatement model) :
    SquarecaseRookModelSnakeInterlacingStatement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact hroute P G hinputs.auxiliaryGInterlacing hinputs.affineNarayana hinputs.recurrence

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

/-- The snake interlacing theorem plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_snakeInterlacing
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : NonNestingRookInterlacingStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  simpa [hmatch w] using
    nonNestingRook_ne_zero_and_splits_of_snakeInterlacing hBJ (w := w) hw

/-- A statement-level squarecase combinatorial witness plus the abstract induction
route and order-polytope matching proves the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseCombinatorialStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        SnakeInterlacingInductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookCombinatorialStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_snakeInterlacing
    (snakeInterlacing_of_squarecaseCombinatorialStatement hroute hsection) hmatch

/-- A squarecase combinatorial package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseCombinatorialPackage
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookCombinatorialPackage model)
    (hroute :
      SnakeInterlacingInductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_snakeInterlacing
    (hsection.snakeInterlacingComputable hroute) hmatch

/-- A statement-level squarecase combinatorial witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseCombinatorialComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        SnakeInterlacingInductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookCombinatorialStatement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_snakeInterlacing
    (snakeInterlacing_of_squarecaseCombinatorialComputableStatement hroute hsection)
    hmatch

end GeneralizedSnakePosets
end RealRooted
