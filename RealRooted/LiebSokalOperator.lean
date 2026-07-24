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
