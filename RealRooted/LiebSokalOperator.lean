import RealRooted.Multiaffine

/-!
# The multivariate differential action

This file defines the finite-variable differential action `F(-∂){G}` used in
the Lieb--Sokal theorem. It also proves the algebraic part of that theorem's
conclusion: this action preserves multiaffineness of `G`.
-/

open BigOperators

namespace RealRooted

noncomputable section

/-- Apply the partial derivative in variable `i` exactly `n` times. -/
def iteratedPDerivAt {R sigma : Type*} [CommSemiring R] (i : sigma) :
    ℕ → MvPolynomial sigma R → MvPolynomial sigma R
  | 0, P => P
  | n + 1, P => MvPolynomial.pderiv i (iteratedPDerivAt i n P)

/-- A fixed enumeration of a finite variable type, used to define iterated
partial differentiation without imposing an order on the variable type. -/
def differentialVariableOrder (sigma : Type*) [Fintype sigma] : List sigma :=
  List.ofFn fun i : Fin (Fintype.card sigma) =>
    (Fintype.equivFin sigma).symm i

@[simp] theorem mem_differentialVariableOrder
    {sigma : Type*} [Fintype sigma] (i : sigma) :
    i ∈ differentialVariableOrder sigma := by
  rw [differentialVariableOrder, List.mem_ofFn]
  exact ⟨Fintype.equivFin sigma i, Equiv.symm_apply_apply _ i⟩

theorem nodup_differentialVariableOrder (sigma : Type*) [Fintype sigma] :
    (differentialVariableOrder sigma).Nodup := by
  rw [differentialVariableOrder, List.nodup_ofFn]
  exact (Fintype.equivFin sigma).symm.injective

/-- Apply the constant-coefficient differential monomial `∂^d` to `P`. -/
def applyMonomialDifferential
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (d : sigma →₀ ℕ) (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  (differentialVariableOrder sigma).foldl
    (fun Q i => iteratedPDerivAt i (d i) Q) P

@[simp] theorem applyMonomialDifferential_zero
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (P : MvPolynomial sigma R) :
    applyMonomialDifferential (0 : sigma →₀ ℕ) P = P := by
  unfold applyMonomialDifferential
  generalize differentialVariableOrder sigma = l
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldl_cons, Finsupp.zero_apply, iteratedPDerivAt]
      exact ih P

/-- The constant-coefficient differential action `F(-∂){G}`. -/
def applyNegDifferential
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F G : MvPolynomial sigma R) : MvPolynomial sigma R :=
  F.sum fun d c =>
    MvPolynomial.C ((-1 : R) ^ (d.sum fun _ n => n) * c) *
      applyMonomialDifferential d G

@[simp] theorem applyNegDifferential_C
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (c : R) (G : MvPolynomial sigma R) :
    applyNegDifferential (MvPolynomial.C c) G = MvPolynomial.C c * G := by
  unfold applyNegDifferential
  rw [MvPolynomial.sum_C (by simp)]
  simp [applyMonomialDifferential_zero]

@[simp] theorem applyNegDifferential_zero_left
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (G : MvPolynomial sigma R) :
    applyNegDifferential 0 G = 0 := by
  simpa using applyNegDifferential_C (0 : R) G

@[simp] theorem iteratedPDerivAt_zero
    {R sigma : Type*} [CommSemiring R] (i : sigma) (n : ℕ) :
    iteratedPDerivAt i n (0 : MvPolynomial sigma R) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedPDerivAt, ih]

@[simp] theorem applyMonomialDifferential_zero_right
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (d : sigma →₀ ℕ) :
    applyMonomialDifferential d (0 : MvPolynomial sigma R) = 0 := by
  unfold applyMonomialDifferential
  generalize differentialVariableOrder sigma = l
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldl_cons, iteratedPDerivAt_zero]
      exact ih

@[simp] theorem applyNegDifferential_zero_right
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F : MvPolynomial sigma R) :
    applyNegDifferential F 0 = 0 := by
  unfold applyNegDifferential
  rw [MvPolynomial.sum_def]
  apply Finset.sum_eq_zero
  intro d hd
  simp

theorem iteratedPDerivAt_add
    {R sigma : Type*} [CommSemiring R] (i : sigma) (n : ℕ)
    (P Q : MvPolynomial sigma R) :
    iteratedPDerivAt i n (P + Q) =
      iteratedPDerivAt i n P + iteratedPDerivAt i n Q := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedPDerivAt, ih, map_add]

theorem applyMonomialDifferential_add
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (d : sigma →₀ ℕ) (P Q : MvPolynomial sigma R) :
    applyMonomialDifferential d (P + Q) =
      applyMonomialDifferential d P + applyMonomialDifferential d Q := by
  unfold applyMonomialDifferential
  generalize differentialVariableOrder sigma = l
  induction l generalizing P Q with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldl_cons, iteratedPDerivAt_add, ih]
      rfl

theorem applyNegDifferential_add_right
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F G H : MvPolynomial sigma R) :
    applyNegDifferential F (G + H) =
      applyNegDifferential F G + applyNegDifferential F H := by
  unfold applyNegDifferential
  rw [MvPolynomial.sum_def, MvPolynomial.sum_def, MvPolynomial.sum_def]
  simp only [applyMonomialDifferential_add, mul_add, Finset.sum_add_distrib]

theorem applyNegDifferential_add_left
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F H G : MvPolynomial sigma R) :
    applyNegDifferential (F + H) G =
      applyNegDifferential F G + applyNegDifferential H G := by
  unfold applyNegDifferential
  classical
  apply Finsupp.sum_add_index'
  · intro d
    simp
  · intro d a b
    simp [mul_add, add_mul]

theorem isMultiaffine_iteratedPDerivAt
    {R sigma : Type*} [CommSemiring R] {P : MvPolynomial sigma R}
    (hP : MvPolynomial.IsMultiaffine P) (i : sigma) :
    ∀ n, MvPolynomial.IsMultiaffine (iteratedPDerivAt i n P) := by
  intro n
  induction n with
  | zero => exact hP
  | succ n ih => exact ih.pderiv i

theorem isMultiaffine_applyMonomialDifferential
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    {P : MvPolynomial sigma R} (hP : MvPolynomial.IsMultiaffine P)
    (d : sigma →₀ ℕ) :
    MvPolynomial.IsMultiaffine (applyMonomialDifferential d P) := by
  unfold applyMonomialDifferential
  generalize differentialVariableOrder sigma = l
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih =>
      exact ih (isMultiaffine_iteratedPDerivAt hP i (d i))

/-- The differential action preserves multiaffineness of its argument. -/
theorem isMultiaffine_applyNegDifferential
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F : MvPolynomial sigma R) {G : MvPolynomial sigma R}
    (hG : MvPolynomial.IsMultiaffine G) :
    MvPolynomial.IsMultiaffine (applyNegDifferential F G) := by
  unfold applyNegDifferential
  rw [MvPolynomial.sum_def]
  apply MvPolynomial.IsMultiaffine.sum
  intro d hd
  exact (isMultiaffine_applyMonomialDifferential hG d).C_mul _

end

end RealRooted
