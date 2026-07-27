import RealRooted.GeneralizedSnakePosets
import RealRooted.GeneralizedSnakePosetsNarayana

open Polynomial

/-!
# Braun--Jal generalized snake posets challenge entry point

Human statement:
https://arxiv.org/abs/2607.00922

Original publication: B. Braun and A. Jal, "Order polytopes of generalized
snake posets are h^*-real-rooted", arXiv:2607.00922.

This module exposes the current challenge-facing interfaces for the
Braun--Jal generalized-snake-poset theorem route.  The combinatorial model,
Section 3 recurrence interfaces, Narayana inputs, and current bounded checks
remain in `RealRooted.GeneralizedSnakePosets` and
`RealRooted.GeneralizedSnakePosetsNarayana`.
-/

noncomputable section

namespace RealRooted

open GeneralizedSnakePosets

namespace Challenges
namespace BraunJal

/-- Challenge-facing name for generalized snake-word letters. -/
abbrev SnakeLetter :=
  GeneralizedSnakePosets.SnakeLetter

/-- Challenge-facing name for generalized snake words. -/
abbrev SnakeWord :=
  GeneralizedSnakePosets.SnakeWord

/-- Challenge-facing name for an abstract squarecase/non-nesting rook model. -/
abbrev SquarecaseRookModel :=
  GeneralizedSnakePosets.SquarecaseRookModel

/-- Challenge-facing name for a non-nesting rook polynomial family. -/
abbrev NonNestingRookPolynomialFamily :=
  GeneralizedSnakePosets.SnakeWord → ℝ[X]

/-- Challenge-facing target for Braun--Jal Theorem 4.1 in rook-polynomial form. -/
abbrev Theorem41Target (M : NonNestingRookPolynomialFamily) : Prop :=
  Theorem41NonNestingRookStatement M

/-- Challenge-facing target for Braun--Jal Theorem 4.1 from a squarecase model. -/
abbrev SquarecaseTheorem41Target (model : SquarecaseRookModel) : Prop :=
  SquarecaseRookModelTheorem41Statement model

/-- Challenge-facing name for the modified Narayana family `P_n`. -/
abbrev ModifiedNarayanaPolynomial (n : ℕ) : ℝ[X] :=
  modifiedNarayanaPolynomial n

/-- Challenge-facing name for Braun--Jal's auxiliary family `G_n`. -/
abbrev AuxiliaryG (n : ℕ) : ℝ[X] :=
  FiniteSkewBoard.auxiliaryG n

/-- Challenge-facing statement that `P_n` is the modified Narayana family. -/
abbrev ModifiedNarayanaFamily (N P : ℕ → ℝ[X]) : Prop :=
  ModifiedNarayanaFamilyStatement N P

/-- Challenge-facing form of Braun--Jal equation (2). -/
abbrev AuxiliaryGRecurrence (P G : ℕ → ℝ[X]) : Prop :=
  NarayanaAuxiliaryGRecurrenceStatement P G

/-- Challenge-facing form of Braun--Jal Lemma 3.3. -/
abbrev AuxiliaryGInterlaces (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G

/-- Challenge-facing form of Braun--Jal Lemma 3.4. -/
abbrev ModifiedNarayanaInterlacing (P : ℕ → ℝ[X]) : Prop :=
  Lemma34ModifiedNarayanaInterlacingStatement P

/-- Shifted nonnegative-parameter form of Braun--Jal Lemma 3.4. -/
abbrev ModifiedNarayanaShiftedInterlacing (P : ℕ → ℝ[X]) : Prop :=
  Lemma34ModifiedNarayanaShiftedInterlacingStatement P

/-- Challenge-facing Section 3 input bundle using the shifted Lemma 3.4 form. -/
abbrev Section3Inputs (M : NonNestingRookPolynomialFamily)
    (P G : ℕ → ℝ[X]) : Prop :=
  Theorem41Section3ComputableShiftedInputs M P G

/-- Challenge-facing squarecase Section 3 input statement. -/
abbrev SquarecaseSection3Inputs (model : SquarecaseRookModel) : Prop :=
  SquarecaseRookSection3ShiftedStatement model

/-- Challenge-facing matching between order-polytope `h^*` and rook models. -/
abbrev OrderPolytopeHStarMatchesNonNestingRook
    (hStar M : NonNestingRookPolynomialFamily) : Prop :=
  GeneralizedSnakePosets.OrderPolytopeHStarMatchesNonNestingRook hStar M

/-- Challenge-facing order-polytope `h^*` form of Braun--Jal Theorem 4.1. -/
abbrev OrderPolytopeHStarTheorem41Target
    (hStar : NonNestingRookPolynomialFamily) : Prop :=
  OrderPolytopeHStarTheorem41Statement hStar

/-- The real-rootedness projection of Braun--Jal Theorem 4.1. -/
theorem theorem41_realRooted_part {M : NonNestingRookPolynomialFamily}
    (h : Theorem41Target M) {w : SnakeWord} (hw : 1 ≤ w.length) :
    M w ≠ 0 ∧ (M w).Splits :=
  nonNestingRook_ne_zero_and_splits_of_theorem41 h hw

/-- The final-letter-deletion interlacing projection of Braun--Jal Theorem 4.1. -/
theorem theorem41_interlacing_part {M : NonNestingRookPolynomialFamily}
    (h : Theorem41Target M) {w : SnakeWord} (hw : 1 ≤ w.length) :
    Interlaces (M w.deleteFinal) (M w) :=
  nonNestingRook_deleteFinal_interlaces_of_theorem41 h hw

/-- Squarecase Section 3 inputs imply the rook-polynomial Theorem 4.1 target,
assuming the abstract induction route. -/
theorem theorem41_of_squarecaseSection3
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseSection3Inputs model) :
    SquarecaseTheorem41Target model :=
  theorem41_of_squarecaseSection3ShiftedStatement hroute hsection

/-- Squarecase Section 3 inputs and `h^*` matching imply the order-polytope
Theorem 4.1 target, assuming the abstract induction route. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3
    {hStar : NonNestingRookPolynomialFamily} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseSection3Inputs model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Target hStar :=
  orderPolytopeHStarTheorem41_of_squarecaseSection3ShiftedStatement
    hroute hsection hmatch

/-- The existing Narayana sequence gives the concrete modified Narayana family. -/
theorem modifiedNarayana_family :
    ModifiedNarayanaFamily narayana ModifiedNarayanaPolynomial :=
  modifiedNarayanaFamily_narayana

/-- Consecutive modified Narayana polynomials are in proper position. -/
theorem modifiedNarayana_prec_succ (n : ℕ) :
    Prec (ModifiedNarayanaPolynomial n) (ModifiedNarayanaPolynomial (n + 1)) :=
  modifiedNarayanaPolynomial_prec_succ n

/-- Braun--Jal equation (2), checked for the concrete families through `n = 8`. -/
theorem auxiliaryG_recurrence_upTo_eight :
    NarayanaAuxiliaryGRecurrenceUpToStatement
      ModifiedNarayanaPolynomial AuxiliaryG 8 :=
  narayanaAuxiliaryGRecurrence_modified_upTo_eight

/-- Braun--Jal Lemma 3.3, checked for the concrete families through `n = 6`. -/
theorem auxiliaryG_interlaces_upTo_six :
    Lemma33AuxiliaryGInterlacesUpToStatement
      ModifiedNarayanaPolynomial AuxiliaryG 6 :=
  lemma33AuxiliaryGInterlaces_modified_upTo_six

/-- Narayana Turan sign input for Lemma 3.4, checked through `m = 5`. -/
theorem modifiedNarayana_turan_nonneg_on_nonpos_upTo_five :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 5 :=
  modifiedNarayanaTuranNonnegOnNonpos_upTo_five

/-- Narayana Turan sign input for Lemma 3.4, checked through `m = 6`. -/
theorem modifiedNarayana_turan_nonneg_on_nonpos_upTo_six :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 6 :=
  modifiedNarayanaTuranNonnegOnNonpos_upTo_six

/-- Narayana Turan sign input for Lemma 3.4, checked through `m = 7`. -/
theorem modifiedNarayana_turan_nonneg_on_nonpos_upTo_seven :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 7 :=
  modifiedNarayanaTuranNonnegOnNonpos_upTo_seven

/-- The `lambda = nu = 0` specialization of Braun--Jal Lemma 3.4. -/
theorem modifiedNarayana_lemma34_zero_zero
    {m : ℕ} (hm : 2 ≤ m) :
    Prec ((C (0 : ℝ) * X + C (0 : ℝ)) * ModifiedNarayanaPolynomial (m - 1) +
        ModifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (0 : ℝ)) * ModifiedNarayanaPolynomial m +
        ModifiedNarayanaPolynomial (m + 1)) :=
  lemma34ModifiedNarayanaInterlacing_modified_zero_zero hm

/-- The shifted `lambda = 0, mu = 1` specialization of Braun--Jal Lemma 3.4. -/
theorem modifiedNarayana_lemma34_shifted_zero_one
    {m : ℕ} (hm : 2 ≤ m) :
    Prec ((C (0 : ℝ) * X + C (1 : ℝ)) * ModifiedNarayanaPolynomial (m - 1) +
        narayanaDifference ModifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (1 : ℝ)) * ModifiedNarayanaPolynomial m +
        narayanaDifference ModifiedNarayanaPolynomial (m + 1)) :=
  lemma34ModifiedNarayanaShiftedInterlacing_modified_zero_one hm

end BraunJal
end Challenges
end RealRooted
