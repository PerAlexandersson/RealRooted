module

public import Mathlib.Algebra.Polynomial.Mirror
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Tactic

/-!
# Parity refinements for polynomial sign variations

This file records the endpoint-sign parity of the zero-filtered coefficient
list and its consequence for multiplication by a positive linear factor.
-/

@[expose] public section

open SignType

namespace Polynomial

variable {R : Type*}

/-- Removing the leading term of a polynomial with another nonzero term does
not change its trailing coefficient. -/
theorem trailingCoeff_eraseLead_of_ne_zero [Semiring R] {p : R[X]}
    (h : p.eraseLead ≠ 0) :
    p.eraseLead.trailingCoeff = p.trailingCoeff := by
  have hmem : p.eraseLead.natTrailingDegree ∈ p.eraseLead.support :=
    natTrailingDegree_mem_support_of_nonzero h
  have hlt : p.eraseLead.natTrailingDegree < p.natDegree :=
    lt_natDegree_of_mem_eraseLead_support hmem
  have hecoeff : p.eraseLead.coeff p.eraseLead.natTrailingDegree ≠ 0 :=
    coeff_natTrailingDegree_ne_zero.mpr h
  have hpcoeff : p.coeff p.eraseLead.natTrailingDegree ≠ 0 := by
    rwa [eraseLead_coeff_of_ne _ hlt.ne] at hecoeff
  have hle : p.natTrailingDegree ≤ p.eraseLead.natTrailingDegree :=
    natTrailingDegree_le_of_ne_zero hpcoeff
  have hp : p ≠ 0 := by
    rintro rfl
    simp at h
  have hptrail : p.coeff p.natTrailingDegree ≠ 0 :=
    coeff_natTrailingDegree_ne_zero.mpr hp
  have hpdeg : p.natTrailingDegree ≠ p.natDegree :=
    (hle.trans_lt hlt).ne
  have hecoeff' : p.eraseLead.coeff p.natTrailingDegree ≠ 0 := by
    rwa [eraseLead_coeff_of_ne _ hpdeg]
  have hle' : p.eraseLead.natTrailingDegree ≤ p.natTrailingDegree :=
    natTrailingDegree_le_of_ne_zero hecoeff'
  rw [trailingCoeff, trailingCoeff, le_antisymm hle' hle,
    eraseLead_coeff_of_ne _ hpdeg]

section Ring

variable [Ring R] [LinearOrder R]

/-- The parity of the coefficient sign variations is determined by the signs
of the first and last nonzero coefficients. -/
theorem even_signVariations_iff_sign_leadingCoeff_eq_sign_trailingCoeff
    {p : R[X]} (hp : p ≠ 0) :
    Even p.signVariations ↔
      sign p.leadingCoeff = sign p.trailingCoeff := by
  generalize hn : p.support.card = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases he : p.eraseLead = 0
      · have hmono : monomial p.natDegree p.leadingCoeff = p := by
          simpa [he] using p.eraseLead_add_monomial_natDegree_leadingCoeff
        rw [← hmono]
        simp [trailingCoeff, natTrailingDegree_monomial
          (leadingCoeff_ne_zero.mpr hp)]
      · have hcard : p.eraseLead.support.card < p.support.card :=
          eraseLead_support_card_lt hp
        have hi := ih p.eraseLead.support.card (by lia) he rfl
        have htrail := trailingCoeff_eraseLead_of_ne_zero he
        rw [signVariations_eq_eraseLead_add_ite hp]
        rw [htrail] at hi
        have hpLead : sign p.leadingCoeff ≠ 0 := by simp [hp]
        have heLead : sign p.eraseLead.leadingCoeff ≠ 0 := by simp [he]
        have hpTrail : sign p.trailingCoeff ≠ 0 := by
          simp [trailingCoeff_nonzero_iff_nonzero.mpr hp]
        generalize hpSign : sign p.leadingCoeff = sp at hpLead ⊢
        generalize heSign : sign p.eraseLead.leadingCoeff = se at heLead hi ⊢
        generalize htSign : sign p.trailingCoeff = st at hpTrail hi ⊢
        fin_cases sp <;> fin_cases se <;> fin_cases st <;>
          simp_all [Nat.even_add_one]

end Ring

section StrictOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplication by `X - C r`, for positive `r`, reverses the parity of the
coefficient sign-variation count. -/
theorem even_signVariations_X_sub_C_mul_iff_not
    {p : R[X]} {r : R} (hr : 0 < r) (hp : p ≠ 0) :
    Even (((X - C r) * p).signVariations) ↔
      ¬Even p.signVariations := by
  have hprod : (X - C r) * p ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero r) hp
  rw [even_signVariations_iff_sign_leadingCoeff_eq_sign_trailingCoeff hprod,
    even_signVariations_iff_sign_leadingCoeff_eq_sign_trailingCoeff hp]
  have hlead : ((X - C r) * p).leadingCoeff = p.leadingCoeff := by
    simp
  have htrailFactor : (X - C r : R[X]).trailingCoeff = -r := by
    rw [trailingCoeff_eq_coeff_zero]
    · simp
    · simp [hr.ne']
  rw [hlead, trailingCoeff_mul, htrailFactor]
  have htrailSign : sign (-r * p.trailingCoeff) = -sign p.trailingCoeff := by
    rw [sign_mul]
    simp [hr]
  rw [htrailSign]
  have hpLead : sign p.leadingCoeff ≠ 0 := by simp [hp]
  have hpTrail : sign p.trailingCoeff ≠ 0 := by
    simp [trailingCoeff_nonzero_iff_nonzero.mpr hp]
  generalize hpSign : sign p.leadingCoeff = sp at hpLead ⊢
  generalize htSign : sign p.trailingCoeff = st at hpTrail ⊢
  fin_cases sp <;> fin_cases st <;> simp_all

/-- Multiplication by a positive linear factor changes the sign-variation
count by a positive odd number. -/
theorem odd_signVariations_sub_of_X_sub_C_mul
    {p : R[X]} {r : R} (hr : 0 < r) (hp : p ≠ 0) :
    Odd (((X - C r) * p).signVariations - p.signVariations) := by
  have hle : p.signVariations ≤ ((X - C r) * p).signVariations :=
    (succ_signVariations_le_X_sub_C_mul hr hp).trans' (Nat.le_add_right _ _)
  rw [Nat.odd_sub hle]
  have htoggle := even_signVariations_X_sub_C_mul_iff_not hr hp
  grind [Nat.not_even_iff_odd]

end StrictOrderedRing

end Polynomial
