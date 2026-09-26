import RealRooted.Applications.OEIS.A144438
import RealRooted.Applications.OEIS.A144438.TotalBridge
import RealRooted.MultivariateStability.Diagonal

/-!
# Diagonal bridge for the Deco total

This file identifies the univariate diagonal of the recurrence-defined Deco
layer total with `decoEulerian`.  Combining that algebraic recurrence theorem
with the checked total-decomposition bridge proves real-rootedness of the
diagonalized admissible-code and normalized-fiber enumerators.  It also
transports proper position, interlacing, strict root negativity, and root
simplicity from the recurrence family to both total models.

This does not assert multivariate stability of the outer fiber sum.
-/

open Polynomial

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The univariate diagonal of the dehomogenized recurrence-defined layer
total. -/
def decoLayerDiagonal (n : Nat) : ℝ[X] :=
  MvPolynomial.diagonal
    (MvPolynomial.dehomogenize (decoLayerTotal n))

@[simp] theorem decoLayerDiagonal_zero : decoLayerDiagonal 0 = 1 := by
  simp [decoLayerDiagonal, decoLayerTotal]

@[simp] theorem decoLayerDiagonal_one :
    decoLayerDiagonal 1 = 1 + Polynomial.X := by
  rw [decoLayerDiagonal, decoLayerTotal_one,
    dehomogenize_decoNormalLayerStep
      (MvPolynomial.isHomogeneous_X Real
        (none : DecoLayerCoord 0))]
  simp [MvPolynomial.diagonal, MvPolynomial.eulerOperator]

/-- Diagonal restriction turns the multivariate layer recurrence into the
univariate Deco Eulerian recurrence. -/
theorem decoLayerDiagonal_recurrence (n : Nat) :
    decoLayerDiagonal (n + 2) =
      (Polynomial.X - Polynomial.X ^ 2) *
          (decoLayerDiagonal (n + 1)).derivative +
        (Polynomial.C 1 + Polynomial.C ((2 : ℝ) + n) * Polynomial.X) *
          decoLayerDiagonal (n + 1) +
        Polynomial.X * decoLayerDiagonal n := by
  rw [decoLayerDiagonal, decoLayerTotal_recurrence, map_add,
    dehomogenize_decoNormalLayerStep
      (decoLayerTotal_isHomogeneous (n + 1)),
    dehomogenize_decoExceptionalLayerStep]
  unfold decoLayerDiagonal
  simp only [MvPolynomial.diagonal_add, MvPolynomial.diagonal_mul,
    MvPolynomial.diagonal_X, MvPolynomial.diagonal_rename,
    MvPolynomial.diagonal_sub, MvPolynomial.diagonal_C,
    MvPolynomial.diagonal_eulerOperator, MvPolynomial.diagonal_sum]
  rw [← MvPolynomial.derivative_diagonal]
  push_cast
  simp only [map_one]
  ring_nf

/-- The recurrence-defined layer diagonal is exactly the algebraic
Deco Eulerian family. -/
theorem decoLayerDiagonal_eq_decoEulerian :
    ∀ n : Nat, decoLayerDiagonal n = decoEulerian n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [decoLayerDiagonal_recurrence, decoEulerian_recurrence, ih0, ih1]

/-- The ordinary-coordinate recursive total has `decoEulerian` as its
univariate diagonal. -/
theorem diagonal_decoBottomTotal_eq_decoEulerian (n : Nat) :
    MvPolynomial.diagonal (decoBottomTotal n) = decoEulerian n := by
  rw [← rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal]
  simpa [decoLayerDiagonal] using decoLayerDiagonal_eq_decoEulerian n

/-- The admissible-code enumerator specializes diagonally to the algebraic
A144438 facade. -/
theorem diagonal_admissibleCodePolynomial_eq_A144438 (n : Nat) :
    MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 2)) =
      A144438 n := by
  rw [admissibleCodePolynomial_eq_decoBottomTotal,
    diagonal_decoBottomTotal_eq_decoEulerian]

/-- The normalized-fiber sum specializes diagonally to the algebraic A144438
facade. -/
theorem diagonal_normalizedFiberPolynomial_eq_A144438 (n : Nat) :
    MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 2)) =
      A144438 n := by
  rw [normalizedFiberPolynomial_eq_decoBottomTotal,
    diagonal_decoBottomTotal_eq_decoEulerian]

/-- Consecutive diagonalized admissible-code enumerators are in proper
position. -/
theorem diagonal_admissibleCodePolynomial_strictInterl (n : Nat) :
    StrictInterl
      (MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 2)))
      (MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 3))) := by
  rw [diagonal_admissibleCodePolynomial_eq_A144438 n,
    diagonal_admissibleCodePolynomial_eq_A144438 (n + 1)]
  exact A144438_strictInterl n

/-- Consecutive diagonalized normalized-fiber enumerators are in proper
position. -/
theorem diagonal_normalizedFiberPolynomial_strictInterl (n : Nat) :
    StrictInterl
      (MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 2)))
      (MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 3))) := by
  rw [diagonal_normalizedFiberPolynomial_eq_A144438 n,
    diagonal_normalizedFiberPolynomial_eq_A144438 (n + 1)]
  exact A144438_strictInterl n

/-- Consecutive diagonalized admissible-code enumerators interlace. -/
theorem diagonal_admissibleCodePolynomial_interlaces (n : Nat) :
    Interlaces
      (MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 2)))
      (MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 3))) := by
  rw [diagonal_admissibleCodePolynomial_eq_A144438 n,
    diagonal_admissibleCodePolynomial_eq_A144438 (n + 1)]
  exact A144438_interlaces n

/-- Consecutive diagonalized normalized-fiber enumerators interlace. -/
theorem diagonal_normalizedFiberPolynomial_interlaces (n : Nat) :
    Interlaces
      (MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 2)))
      (MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 3))) := by
  rw [diagonal_normalizedFiberPolynomial_eq_A144438 n,
    diagonal_normalizedFiberPolynomial_eq_A144438 (n + 1)]
  exact A144438_interlaces n

/-- Every individual normalization fiber remains real-rooted after diagonal
restriction. -/
theorem diagonal_fiberPolynomial_splits {h : Nat}
    (c : DecoNormalizedCode h) :
    (MvPolynomial.diagonal
      (DecoNormalizedCode.fiberPolynomial (R := Real) c)).Splits :=
  (DecoNormalizedCode.fiberPolynomial_mvRealStable c).diagonal_splits

/-- Every exact-history layer remains real-rooted after dehomogenization and
diagonal restriction. -/
theorem diagonal_decoExactLayerDehomogenized_splits {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    (MvPolynomial.diagonal (decoExactLayerDehomogenized H)).Splits :=
  (decoExactLayerDehomogenized_mvRealStable H).diagonal_splits

/-- The diagonalized admissible-code enumerator is real-rooted. -/
theorem diagonal_admissibleCodePolynomial_splits (n : Nat) :
    (MvPolynomial.diagonal
      (admissibleCodePolynomial (R := Real) (n + 2))).Splits := by
  rw [diagonal_admissibleCodePolynomial_eq_A144438]
  exact A144438_splits n

/-- The diagonalized normalized-fiber enumerator is real-rooted.  This is a
univariate conclusion and does not claim stability of the multivariate sum. -/
theorem diagonal_normalizedFiberPolynomial_splits (n : Nat) :
    (MvPolynomial.diagonal
      (normalizedFiberPolynomial (R := Real) (n + 2))).Splits := by
  rw [diagonal_normalizedFiberPolynomial_eq_A144438]
  exact A144438_splits n

/-- Every root of a diagonalized admissible-code enumerator is strictly
negative. -/
theorem diagonal_admissibleCodePolynomial_root_neg (n : Nat) {r : Real}
    (hr : (MvPolynomial.diagonal
      (admissibleCodePolynomial (R := Real) (n + 2))).IsRoot r) :
    r < 0 := by
  rw [diagonal_admissibleCodePolynomial_eq_A144438] at hr
  exact A144438_root_neg n hr

/-- Every root of a diagonalized normalized-fiber enumerator is strictly
negative. -/
theorem diagonal_normalizedFiberPolynomial_root_neg (n : Nat) {r : Real}
    (hr : (MvPolynomial.diagonal
      (normalizedFiberPolynomial (R := Real) (n + 2))).IsRoot r) :
    r < 0 := by
  rw [diagonal_normalizedFiberPolynomial_eq_A144438] at hr
  exact A144438_root_neg n hr

/-- Every diagonalized admissible-code enumerator has simple roots. -/
theorem diagonal_admissibleCodePolynomial_hasSimpleRoots (n : Nat) :
    HasSimpleRoots
      (MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 2))) := by
  rw [diagonal_admissibleCodePolynomial_eq_A144438]
  exact A144438_hasSimpleRoots n

/-- Every diagonalized normalized-fiber enumerator has simple roots. -/
theorem diagonal_normalizedFiberPolynomial_hasSimpleRoots (n : Nat) :
    HasSimpleRoots
      (MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 2))) := by
  rw [diagonal_normalizedFiberPolynomial_eq_A144438]
  exact A144438_hasSimpleRoots n

/-! ## Deprecated proper-position names -/

@[deprecated diagonal_admissibleCodePolynomial_strictInterl
  (since := "2026-09-26")]
alias diagonal_admissibleCodePolynomial_prec :=
  diagonal_admissibleCodePolynomial_strictInterl

@[deprecated diagonal_normalizedFiberPolynomial_strictInterl
  (since := "2026-09-26")]
alias diagonal_normalizedFiberPolynomial_prec :=
  diagonal_normalizedFiberPolynomial_strictInterl

end

end RealRooted.Applications.OEIS
