import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Discriminants and separability

Over a field, a polynomial of positive degree has nonzero discriminant if and only if it is
separable, that is, coprime to its derivative. The proof compares the discriminant with the
resultant `resultant f f.derivative` through `Polynomial.resultant_deriv`, padding the degree
of the derivative with `Polynomial.resultant_add_right_deg`, so no characteristic assumption
is needed.
-/

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- Over a field, a polynomial of positive degree has nonzero discriminant if and only if it
is separable. -/
theorem discr_ne_zero_iff_separable (hf : f.natDegree ≠ 0) : f.discr ≠ 0 ↔ f.Separable := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf natDegree_zero
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (natDegree_derivative_le f)
  have hres := resultant_deriv (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hf))
  rw [hk, resultant_add_right_deg (k := k) (hg := le_rfl), coeff_natDegree] at hres
  have hiff : f.discr = 0 ↔ f.resultant f.derivative = 0 := by
    constructor
    · intro h
      rw [h, mul_zero] at hres
      simpa [hlc] using hres
    · intro h
      rw [h, mul_zero] at hres
      simpa [hlc] using hres.symm
  rw [separable_def, ne_eq, hiff, resultant_eq_zero_iff]
  simp [hf0]

/-- A polynomial of positive degree with nonzero discriminant is separable. -/
theorem separable_of_discr_ne_zero (hf : f.natDegree ≠ 0) (hdiscr : f.discr ≠ 0) :
    f.Separable :=
  (discr_ne_zero_iff_separable hf).mp hdiscr

/-- A separable polynomial of positive degree has nonzero discriminant. -/
theorem Separable.discr_ne_zero (hsep : f.Separable) (hf : f.natDegree ≠ 0) : f.discr ≠ 0 :=
  (discr_ne_zero_iff_separable hf).mpr hsep

/-- A polynomial of positive degree with nonzero discriminant is squarefree. -/
theorem squarefree_of_discr_ne_zero (hf : f.natDegree ≠ 0) (hdiscr : f.discr ≠ 0) :
    Squarefree f :=
  (separable_of_discr_ne_zero hf hdiscr).squarefree

end Polynomial
