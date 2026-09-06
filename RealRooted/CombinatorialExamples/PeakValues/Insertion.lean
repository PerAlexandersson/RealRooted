import RealRooted.CombinatorialExamples.PeakValues

/-!
# Inserting the maximum into a permutation

This file begins the order-preserving insertion infrastructure used to derive
the peak-value recurrence. The insertion slot is a position in the new
permutation, and the old positions and values retain their relative order.
-/

namespace RealRooted

/-- Rename the final value of a rank-`n + 1` polynomial as `none`, retaining
the old values as `some i`. -/
noncomputable def identifyLast (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  MvPolynomial.renameEquiv ℝ (finSuccEquiv' (Fin.last n)) P

/-- Embed a polynomial in the old variables into the enlarged value set. -/
noncomputable def liftOld {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  MvPolynomial.rename some P

/-- Insert the new maximum value into `π` at `slot`, preserving the order of
the old positions and the names of the old values. -/
def insertMaximum {n : ℕ} (slot : Fin (n + 1))
    (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' slot).trans
    (π.optionCongr.trans (finSuccEquiv' (Fin.last n)).symm)

@[simp] theorem insertMaximum_apply_slot {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    insertMaximum slot π slot = Fin.last n := by
  simp [insertMaximum]

@[simp] theorem insertMaximum_apply_succAbove {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    insertMaximum slot π (slot.succAbove i) = (π i).castSucc := by
  simp [insertMaximum]

end RealRooted
