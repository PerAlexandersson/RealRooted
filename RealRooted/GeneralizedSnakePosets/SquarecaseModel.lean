import RealRooted.GeneralizedSnakePosets.FiniteBoard
import RealRooted.GeneralizedSnakePosets.SnakeWord

/-!
# Squarecase rook models for generalized snake posets

This module contains the abstract squarecase/non-nesting rook model interface
and the adapter from concrete finite skew boards.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

universe u

/-- Abstract squarecase/non-nesting rook model for generalized snake words.

The concrete squarecase encoding is deliberately not fixed here.  Later files
can instantiate `Board`, `boardOfSnake`, and `nonNestingRookPolynomial` with a
Ferrers/skew-shape model while reusing the theorem-shaped interfaces below. -/
structure SquarecaseRookModel where
  Board : Type u
  boardOfSnake : SnakeWord → Board
  nonNestingRookPolynomial : Board → ℝ[X]

namespace SquarecaseRookModel

/-- The non-nesting rook polynomial attached to a generalized snake word in a
chosen squarecase model. -/
def snakePolynomial (model : SquarecaseRookModel) (w : SnakeWord) : ℝ[X] :=
  model.nonNestingRookPolynomial (model.boardOfSnake w)

end SquarecaseRookModel

/-- A finite-skew-board assignment for snake words gives an abstract squarecase
rook model. -/
def squarecaseRookModelOfFiniteSkewBoard
    (boardOfSnake : SnakeWord → FiniteSkewBoard) : SquarecaseRookModel where
  Board := FiniteSkewBoard
  boardOfSnake := boardOfSnake
  nonNestingRookPolynomial := FiniteSkewBoard.rookPolynomial

@[simp] theorem squarecaseRookModelOfFiniteSkewBoard_snakePolynomial
    (boardOfSnake : SnakeWord → FiniteSkewBoard) (w : SnakeWord) :
    (squarecaseRookModelOfFiniteSkewBoard boardOfSnake).snakePolynomial w =
      (boardOfSnake w).rookPolynomial :=
  rfl

/-- Finite-skew-board squarecase models have constant coefficient one for every
snake-word polynomial. -/
@[simp] theorem squarecaseRookModelOfFiniteSkewBoard_snakePolynomial_coeff_zero
    (boardOfSnake : SnakeWord → FiniteSkewBoard) (w : SnakeWord) :
    ((squarecaseRookModelOfFiniteSkewBoard boardOfSnake).snakePolynomial w).coeff 0 = 1 :=
  FiniteSkewBoard.rookPolynomial_coeff_zero _

/-- Finite-skew-board squarecase models have nonzero snake-word polynomials. -/
theorem squarecaseRookModelOfFiniteSkewBoard_snakePolynomial_ne_zero
    (boardOfSnake : SnakeWord → FiniteSkewBoard) (w : SnakeWord) :
    (squarecaseRookModelOfFiniteSkewBoard boardOfSnake).snakePolynomial w ≠ 0 :=
  FiniteSkewBoard.rookPolynomial_ne_zero _

end GeneralizedSnakePosets
end RealRooted
