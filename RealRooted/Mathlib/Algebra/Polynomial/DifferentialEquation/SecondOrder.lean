/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

import Mathlib.Tactic

/-!
# Algebraic lemmas for second-order polynomial differential equations

The results in this file do not depend on a particular classical polynomial
family. They isolate an ordinary-point simple-root criterion and a factorized
second-derivative elimination identity.
-/

@[expose] public section

namespace Polynomial

/-- A nonzero polynomial solution of a second-order ODE cannot have a multiple
root at an ordinary point of the leading coefficient. No nonvanishing
assumption on either lower-order coefficient is needed. -/
theorem eval_derivative_ne_zero_of_second_order_ode
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {T A B C₀ : R[X]} {r : R}
    (hT : T ≠ 0)
    (hode : A * T.derivative.derivative + B * T.derivative + C₀ * T = 0)
    (hr : T.IsRoot r) (hAr : A.eval r ≠ 0) :
    T.derivative.eval r ≠ 0 := by
  intro hder_eval
  have hder_root : T.derivative.IsRoot r := by
    simpa [Polynomial.IsRoot.def] using hder_eval
  let k := T.rootMultiplicity r
  have hk2 : 2 ≤ k := by
    dsimp [k]
    exact (one_lt_rootMultiplicity_iff_isRoot hT).2 ⟨hr, hder_root⟩
  have hT_degree_pos : 0 < T.degree := degree_pos_of_root hT hr
  have hT_natDegree_pos : 0 < T.natDegree :=
    natDegree_pos_iff_degree_pos.mpr hT_degree_pos
  have hder_ne : T.derivative ≠ 0 :=
    derivative_ne_zero.mpr hT_natDegree_pos.ne'
  have hder_degree_pos : 0 < T.derivative.degree :=
    degree_pos_of_root hder_ne hder_root
  have hder_natDegree_pos : 0 < T.derivative.natDegree :=
    natDegree_pos_iff_degree_pos.mpr hder_degree_pos
  have hderder_ne : T.derivative.derivative ≠ 0 :=
    derivative_ne_zero.mpr hder_natDegree_pos.ne'
  have hmult_der : T.derivative.rootMultiplicity r = k - 1 := by
    dsimp [k]
    exact derivative_rootMultiplicity_of_root hr
  have hmult_derder :
      T.derivative.derivative.rootMultiplicity r = k - 2 := by
    rw [derivative_rootMultiplicity_of_root hder_root, hmult_der]
    lia
  have hA_notroot : ¬A.IsRoot r := by
    simpa [Polynomial.IsRoot.def] using hAr
  have hA_ne : A ≠ 0 := by
    intro hA
    subst A
    simp at hAr
  have hmult_A : A.rootMultiplicity r = 0 :=
    rootMultiplicity_eq_zero hA_notroot
  have hleft_ne : A * T.derivative.derivative ≠ 0 :=
    mul_ne_zero hA_ne hderder_ne
  have hmult_left :
      (A * T.derivative.derivative).rootMultiplicity r = k - 2 := by
    rw [rootMultiplicity_mul hleft_ne, hmult_A, hmult_derder, zero_add]
  have hdiv_der :
      (X - C r) ^ (k - 1) ∣ T.derivative := by
    apply (le_rootMultiplicity_iff hder_ne).mp
    rw [hmult_der]
  have hdiv_T : (X - C r) ^ (k - 1) ∣ T := by
    exact (pow_dvd_pow (X - C r) (by lia : k - 1 ≤ k)).trans
      (pow_rootMultiplicity_dvd T r)
  have hdiv_lower :
      (X - C r) ^ (k - 1) ∣ B * T.derivative + C₀ * T :=
    dvd_add (dvd_mul_of_dvd_right hdiv_der B) (dvd_mul_of_dvd_right hdiv_T C₀)
  have hlower_eq :
      B * T.derivative + C₀ * T = -(A * T.derivative.derivative) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_assoc, add_comm, add_left_comm] using hode
  have hdiv_left : (X - C r) ^ (k - 1) ∣ A * T.derivative.derivative := by
    rw [hlower_eq] at hdiv_lower
    simpa using hdiv_lower
  have hmult_ge :
      k - 1 ≤ (A * T.derivative.derivative).rootMultiplicity r :=
    (le_rootMultiplicity_iff hleft_ne).mpr hdiv_left
  rw [hmult_left] at hmult_ge
  lia

/-- Eliminate the second derivative from a factorized second-order ODE after
multiplying by one copy of the right factor. -/
theorem second_derivative_reduce_of_second_order_ode
    {R : Type*} [CommRing R]
    (T U V B C₀ : R[X]) (c₀ c₁ c₂ : R)
    (hode : V * U * T.derivative.derivative +
      B * T.derivative + C₀ * T = 0) :
    V * (C c₀ * T + C c₁ * (U * T.derivative) +
      C c₂ * (U ^ 2 * T.derivative.derivative)) =
      (C c₀ * V - C c₂ * U * C₀) * T +
        (C c₁ * V * U - C c₂ * U * B) * T.derivative := by
  linear_combination C c₂ * U * hode

end Polynomial
