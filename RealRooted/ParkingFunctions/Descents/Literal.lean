import RealRooted.ParkingFunctions.Descents.Basic

/-!
# Literal all-word descent polynomials

This module defines the actual finite descent enumerator over all words on a
finite alphabet.  The separate threshold-matrix recurrence in `Words` is
proved split, but identifying it with this literal finite sum is a subsequent
combinatorial theorem.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The literal descent polynomial of all words of length `n` on an alphabet
of size `m`.  The empty word has weight one. -/
def literalWordDescentPolynomial (m : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => descentGeneratingPolynomial (R := ℝ)
      (Finset.univ : Finset (Fin (n + 1) → Fin m))

@[simp]
theorem literalWordDescentPolynomial_zero (m : ℕ) :
    literalWordDescentPolynomial m 0 = 1 := rfl

@[simp]
theorem descentNumber_fin_one (m : ℕ) (w : Fin 1 → Fin m) :
    descentNumber w = 0 := by
  unfold descentNumber descentSet
  simp

@[simp]
theorem literalWordDescentPolynomial_one (m : ℕ) :
    literalWordDescentPolynomial m 1 = C (m : ℝ) := by
  simp [literalWordDescentPolynomial, descentGeneratingPolynomial]

end

end RealRooted.ParkingFunctions
