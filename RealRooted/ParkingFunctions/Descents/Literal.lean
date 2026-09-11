import RealRooted.ParkingFunctions.Descents.Basic
import Mathlib.Data.Fin.Rev

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

/-- The literal all-word descent enumerator with fixed final letter, encoded
in reverse order to match the threshold-matrix recurrence. -/
def literalWordDescentRefined (m r : ℕ) (i : Fin m) : ℝ[X] :=
  ∑ w : Fin r → Fin m, X ^ descentNumber (Fin.snoc w i.rev)

@[simp]
theorem literalWordDescentRefined_zero (m : ℕ) (i : Fin m) :
    literalWordDescentRefined m 0 i = 1 := by
  simp [literalWordDescentRefined, descentNumber_fin_one]

/-- Splitting the penultimate letter gives the reversed-last-letter threshold
recurrence for the literal refined enumerators. -/
theorem literalWordDescentRefined_succ (m r : ℕ) (i : Fin m) :
    literalWordDescentRefined m (r + 1) i =
      ∑ j : Fin m, (if j < i then X else 1) * literalWordDescentRefined m r j := by
  unfold literalWordDescentRefined
  rw [show (∑ w : Fin (r + 1) → Fin m,
      (X : ℝ[X]) ^ descentNumber (Fin.snoc w i.rev)) =
      ∑ x : Fin m, ∑ w : Fin r → Fin m,
        X ^ descentNumber (Fin.snoc (Fin.snoc w x) i.rev) by
    symm
    simpa only [Fintype.sum_prod_type] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin m)
        (fun x => X ^ descentNumber (Fin.snoc (Fin.snoc x.2 x.1) i.rev)) _
        (fun _ => rfl)]
  have hrev : (∑ x : Fin m, ∑ w : Fin r → Fin m,
      (X : ℝ[X]) ^ descentNumber (Fin.snoc (Fin.snoc w x) i.rev)) =
      ∑ j : Fin m, ∑ w : Fin r → Fin m,
        (X : ℝ[X]) ^ descentNumber (Fin.snoc (Fin.snoc w j.rev) i.rev) := by
    symm
    exact Fintype.sum_equiv Fin.revPerm
      (fun j => ∑ w : Fin r → Fin m,
        (X : ℝ[X]) ^ descentNumber (Fin.snoc (Fin.snoc w j.rev) i.rev))
      (fun x => ∑ w : Fin r → Fin m,
        (X : ℝ[X]) ^ descentNumber (Fin.snoc (Fin.snoc w x) i.rev))
      (fun _ => rfl)
  rw [hrev]
  simp_rw [descentWeight_snoc]
  simp only [Fin.snoc_last, Fin.rev_lt_rev]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]

/-- The literal all-word polynomial is the sum of its reversed-final-letter
refinement. -/
theorem literalWordDescentPolynomial_succ (m r : ℕ) :
    literalWordDescentPolynomial m (r + 1) =
      ∑ i : Fin m, literalWordDescentRefined m r i := by
  unfold literalWordDescentPolynomial descentGeneratingPolynomial literalWordDescentRefined
  change (∑ w : Fin (r + 1) → Fin m, (X : ℝ[X]) ^ descentNumber w) = _
  rw [show (∑ w : Fin (r + 1) → Fin m, (X : ℝ[X]) ^ descentNumber w) =
      ∑ x : Fin m, ∑ w : Fin r → Fin m,
        X ^ descentNumber (Fin.snoc w x) by
    symm
    simpa only [Fintype.sum_prod_type] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin m)
        (fun x => (X : ℝ[X]) ^ descentNumber (Fin.snoc x.2 x.1)) _
        (fun _ => rfl)]
  symm
  exact Fintype.sum_equiv Fin.revPerm
    (fun i => ∑ w : Fin r → Fin m,
      (X : ℝ[X]) ^ descentNumber (Fin.snoc w i.rev))
    (fun x => ∑ w : Fin r → Fin m,
      (X : ℝ[X]) ^ descentNumber (Fin.snoc w x))
    (fun _ => rfl)

end

end RealRooted.ParkingFunctions
