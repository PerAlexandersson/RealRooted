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

private theorem foldl_iteratedPDerivAt_single_of_not_mem
    {R sigma : Type*} [CommSemiring R] (i : sigma)
    (l : List sigma) (P : MvPolynomial sigma R) (hi : i ∉ l) :
    l.foldl
        (fun Q j => iteratedPDerivAt j ((Finsupp.single i 1) j) Q) P = P := by
  induction l generalizing P with
  | nil => rfl
  | cons j l ih =>
      have hji : j ≠ i := by
        intro h
        apply hi
        simp [h]
      have hil : i ∉ l := by
        intro h
        exact hi (by simp [h])
      rw [List.foldl_cons, Finsupp.single_eq_of_ne hji, iteratedPDerivAt]
      exact ih P hil

private theorem foldl_iteratedPDerivAt_single
    {R sigma : Type*} [CommSemiring R] (i : sigma)
    (l : List sigma) (P : MvPolynomial sigma R)
    (hi : i ∈ l) (hl : l.Nodup) :
    l.foldl
        (fun Q j => iteratedPDerivAt j ((Finsupp.single i 1) j) Q) P =
      MvPolynomial.pderiv i P := by
  induction l generalizing P with
  | nil => simp at hi
  | cons j l ih =>
      rw [List.foldl_cons]
      by_cases hji : j = i
      · subst j
        have hil : i ∉ l := List.nodup_cons.mp hl |>.1
        simp only [Finsupp.single_eq_same, iteratedPDerivAt]
        exact foldl_iteratedPDerivAt_single_of_not_mem i l
          (MvPolynomial.pderiv i P) hil
      · have hij : i ≠ j := Ne.symm hji
        have hil : i ∈ l := by simpa [hij] using hi
        have hlnodup : l.Nodup := List.nodup_cons.mp hl |>.2
        rw [Finsupp.single_eq_of_ne hji, iteratedPDerivAt]
        exact ih P hil hlnodup

@[simp] theorem applyMonomialDifferential_single
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (i : sigma) (P : MvPolynomial sigma R) :
    applyMonomialDifferential (Finsupp.single i 1) P =
      MvPolynomial.pderiv i P := by
  unfold applyMonomialDifferential
  exact foldl_iteratedPDerivAt_single i (differentialVariableOrder sigma) P
    (mem_differentialVariableOrder i) (nodup_differentialVariableOrder sigma)

/-- The constant-coefficient differential action `F(-∂){G}`. -/
def applyNegDifferential
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F G : MvPolynomial sigma R) : MvPolynomial sigma R :=
  F.sum fun d c =>
    MvPolynomial.C ((-1 : R) ^ (d.sum fun _ n => n) * c) *
      applyMonomialDifferential d G

/-- Eliminate variable `i` by replacing its linear occurrence with negative
partial differentiation in variable `j`. -/
def contractVariables {R sigma : Type*} [CommRing R]
    (i j : sigma) (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  MvPolynomial.specializeZero i P -
    MvPolynomial.pderiv j (MvPolynomial.pderiv i P)

/-- Put two polynomials in disjoint left and right variable blocks. -/
def pairedProduct {R sigma : Type*} [CommRing R]
    (F G : MvPolynomial sigma R) : MvPolynomial (Sum sigma sigma) R :=
  MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G

/-- Successively replace each left variable by negative partial
differentiation in its paired right variable. -/
def contractVariablePairs {R sigma : Type*} [CommRing R]
    (l : List sigma) (P : MvPolynomial (Sum sigma sigma) R) :
    MvPolynomial (Sum sigma sigma) R :=
  l.foldl (fun Q i => contractVariables (Sum.inl i) (Sum.inr i) Q) P

@[simp] theorem applyNegDifferential_monomial
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (d : sigma →₀ ℕ) (c : R) (G : MvPolynomial sigma R) :
    applyNegDifferential (MvPolynomial.monomial d c) G =
      MvPolynomial.C ((-1 : R) ^ (d.sum fun _ n => n) * c) *
        applyMonomialDifferential d G := by
  unfold applyNegDifferential
  rw [MvPolynomial.sum_monomial_eq]
  simp

@[simp] theorem applyNegDifferential_C
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (c : R) (G : MvPolynomial sigma R) :
    applyNegDifferential (MvPolynomial.C c) G = MvPolynomial.C c * G := by
  unfold applyNegDifferential
  rw [MvPolynomial.sum_C (by simp)]
  simp [applyMonomialDifferential_zero]

@[simp] theorem applyNegDifferential_X
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (i : sigma) (G : MvPolynomial sigma R) :
    applyNegDifferential (MvPolynomial.X i) G =
      -MvPolynomial.pderiv i G := by
  rw [MvPolynomial.X, applyNegDifferential_monomial]
  simp

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

/-- A paired coordinate contraction preserves multiaffineness. -/
theorem isMultiaffine_contractVariables
    {R sigma : Type*} [CommRing R]
    {P : MvPolynomial sigma R} (hP : MvPolynomial.IsMultiaffine P)
    (i j : sigma) :
    MvPolynomial.IsMultiaffine (contractVariables i j P) := by
  exact (hP.specializeZero_preserves i).sub ((hP.pderiv i).pderiv j)

private theorem inl_notMem_vars_rename_inr
    {R sigma : Type*} [CommRing R] (i : sigma)
    (G : MvPolynomial sigma R) :
    Sum.inl i ∉ (MvPolynomial.rename Sum.inr G).vars := by
  intro h
  obtain ⟨j, hj, hji⟩ := MvPolynomial.mem_vars_rename Sum.inr G h
  exact Sum.inr_ne_inl hji

private theorem inr_notMem_vars_rename_inl
    {R sigma : Type*} [CommRing R] (i : sigma)
    (F : MvPolynomial sigma R) :
    Sum.inr i ∉ (MvPolynomial.rename Sum.inl F).vars := by
  intro h
  obtain ⟨j, hj, hji⟩ := MvPolynomial.mem_vars_rename Sum.inl F h
  exact Sum.inl_ne_inr hji

theorem pderiv_inl_pairedProduct
    {R sigma : Type*} [CommRing R] (i : sigma)
    (F G : MvPolynomial sigma R) :
    MvPolynomial.pderiv (Sum.inl i) (pairedProduct F G) =
      pairedProduct (MvPolynomial.pderiv i F) G := by
  rw [pairedProduct, pairedProduct, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_rename Sum.inl_injective,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (inl_notMem_vars_rename_inr i G)]
  simp

theorem pderiv_inr_pairedProduct
    {R sigma : Type*} [CommRing R] (i : sigma)
    (F G : MvPolynomial sigma R) :
    MvPolynomial.pderiv (Sum.inr i) (pairedProduct F G) =
      pairedProduct F (MvPolynomial.pderiv i G) := by
  rw [pairedProduct, pairedProduct, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_rename Sum.inr_injective,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (inr_notMem_vars_rename_inl i F)]
  simp

theorem specializeZero_inl_pairedProduct
    {R sigma : Type*} [CommRing R]
    (i : sigma) (F G : MvPolynomial sigma R) :
    MvPolynomial.specializeZero (Sum.inl i) (pairedProduct F G) =
      pairedProduct (MvPolynomial.specializeZero i F) G := by
  rw [pairedProduct, pairedProduct, MvPolynomial.specializeZero_mul,
    MvPolynomial.specializeZero_rename Sum.inl Sum.inl_injective]
  rw [MvPolynomial.specializeZero_eq_self_of_notMem_vars
    (Sum.inl i) (MvPolynomial.rename Sum.inr G)
    (inl_notMem_vars_rename_inr i G)]

theorem contractVariables_pairedProduct
    {R sigma : Type*} [CommRing R]
    (i : sigma) (F G : MvPolynomial sigma R) :
    contractVariables (Sum.inl i) (Sum.inr i) (pairedProduct F G) =
      pairedProduct (MvPolynomial.specializeZero i F) G -
        pairedProduct (MvPolynomial.pderiv i F) (MvPolynomial.pderiv i G) := by
  rw [contractVariables, specializeZero_inl_pairedProduct,
    pderiv_inl_pairedProduct, pderiv_inr_pairedProduct]

theorem contractVariables_pairedProduct_monomial
    {R sigma : Type*} [CommRing R]
    (i : sigma) (d : sigma →₀ ℕ) (c : R)
    (G : MvPolynomial sigma R) (hdi : d i ≤ 1) :
    contractVariables (Sum.inl i) (Sum.inr i)
        (pairedProduct (MvPolynomial.monomial d c) G) =
      if d i = 0 then pairedProduct (MvPolynomial.monomial d c) G
      else pairedProduct
        (MvPolynomial.monomial (d - Finsupp.single i 1) (-c))
        (MvPolynomial.pderiv i G) := by
  rw [contractVariables_pairedProduct, MvPolynomial.specializeZero_monomial,
    MvPolynomial.pderiv_monomial]
  have hcases : d i = 0 ∨ d i = 1 := by lia
  rcases hcases with h | h
  · simp [h, pairedProduct]
  · simp [h, pairedProduct]

theorem contractVariables_add
    {R sigma : Type*} [CommRing R]
    (i j : sigma) (P Q : MvPolynomial sigma R) :
    contractVariables i j (P + Q) =
      contractVariables i j P + contractVariables i j Q := by
  rw [contractVariables, contractVariables, contractVariables,
    MvPolynomial.specializeZero_add]
  simp only [map_add]
  abel

theorem contractVariablePairs_add
    {R sigma : Type*} [CommRing R]
    (l : List sigma) (P Q : MvPolynomial (Sum sigma sigma) R) :
    contractVariablePairs l (P + Q) =
      contractVariablePairs l P + contractVariablePairs l Q := by
  unfold contractVariablePairs
  induction l generalizing P Q with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons,
        contractVariables_add, ih]

@[simp] theorem contractVariablePairs_zero
    {R sigma : Type*} [CommRing R] (l : List sigma) :
    contractVariablePairs l (0 : MvPolynomial (Sum sigma sigma) R) = 0 := by
  unfold contractVariablePairs
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldl_cons]
      have hstep : contractVariables (Sum.inl i) (Sum.inr i)
          (0 : MvPolynomial (Sum sigma sigma) R) = 0 := by
        simp [contractVariables]
      rw [hstep]
      exact ih

theorem pairedProduct_add_left
    {R sigma : Type*} [CommRing R]
    (F H G : MvPolynomial sigma R) :
    pairedProduct (F + H) G = pairedProduct F G + pairedProduct H G := by
  simp [pairedProduct, add_mul]

theorem contractVariablePairs_sum
    {R sigma I : Type*} [CommRing R]
    (l : List sigma) (s : Finset I)
    (P : I → MvPolynomial (Sum sigma sigma) R) :
    contractVariablePairs l (∑ i ∈ s, P i) =
      ∑ i ∈ s, contractVariablePairs l (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [contractVariablePairs_add, ih]

/-- Sum the exponents indexed by a list of variables. -/
def listExponentSum {sigma : Type*} (l : List sigma) (d : sigma →₀ ℕ) : ℕ :=
  (l.map fun i => d i).sum

/-- Apply the differential monomial along an explicitly supplied variable
list. -/
def applyMonomialDifferentialAlong
    {R sigma : Type*} [CommSemiring R]
    (l : List sigma) (d : sigma →₀ ℕ) (G : MvPolynomial sigma R) :
    MvPolynomial sigma R :=
  l.foldl (fun Q i => iteratedPDerivAt i (d i) Q) G

theorem listExponentSum_congr
    {sigma : Type*} {l : List sigma} {d e : sigma →₀ ℕ}
    (h : ∀ i ∈ l, d i = e i) :
    listExponentSum l d = listExponentSum l e := by
  unfold listExponentSum
  rw [List.map_congr_left h]

theorem applyMonomialDifferentialAlong_congr
    {R sigma : Type*} [CommSemiring R]
    {l : List sigma} {d e : sigma →₀ ℕ}
    (h : ∀ i ∈ l, d i = e i) (G : MvPolynomial sigma R) :
    applyMonomialDifferentialAlong l d G =
      applyMonomialDifferentialAlong l e G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
      change applyMonomialDifferentialAlong l d
          (iteratedPDerivAt i (d i) G) =
        applyMonomialDifferentialAlong l e
          (iteratedPDerivAt i (e i) G)
      rw [h i (by simp)]
      apply ih
      intro j hj
      exact h j (by simp [hj])

/-- Iterated paired contraction of a multiaffine monomial gives its signed
constant-coefficient differential action on the right factor. -/
theorem contractVariablePairs_pairedProduct_monomial
    {R sigma : Type*} [CommRing R] [DecidableEq sigma]
    (l : List sigma) (hl : l.Nodup)
    (d : sigma →₀ ℕ) (hsupport : d.support ⊆ l.toFinset)
    (hdegree : ∀ i, d i ≤ 1) (c : R) (G : MvPolynomial sigma R) :
    contractVariablePairs l (pairedProduct (MvPolynomial.monomial d c) G) =
      MvPolynomial.C ((-1 : R) ^ listExponentSum l d * c) *
        MvPolynomial.rename Sum.inr (applyMonomialDifferentialAlong l d G) := by
  classical
  induction l generalizing d c G with
  | nil =>
      have hd : d = 0 := by
        ext i
        by_contra hi
        have hisupport : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
        simpa using hsupport hisupport
      subst d
      simp [contractVariablePairs, pairedProduct, listExponentSum,
        applyMonomialDifferentialAlong]
  | cons i l ih =>
      have hil : i ∉ l := List.nodup_cons.mp hl |>.1
      have hlnodup : l.Nodup := List.nodup_cons.mp hl |>.2
      have hcases : d i = 0 ∨ d i = 1 := by
        have := hdegree i
        lia
      rcases hcases with hdi | hdi
      · have hsupportTail : d.support ⊆ l.toFinset := by
          intro j hj
          have hjcons := hsupport hj
          rw [List.toFinset_cons, Finset.mem_insert] at hjcons
          rcases hjcons with hji | hjl
          · subst j
            exact (Finsupp.mem_support_iff.mp hj hdi).elim
          · exact hjl
        change contractVariablePairs l
            (contractVariables (Sum.inl i) (Sum.inr i)
              (pairedProduct (MvPolynomial.monomial d c) G)) = _
        rw [contractVariables_pairedProduct_monomial i d c G (hdegree i), if_pos hdi]
        simpa [listExponentSum, applyMonomialDifferentialAlong, hdi,
          iteratedPDerivAt] using
          ih hlnodup d hsupportTail hdegree c G
      · let e := d - Finsupp.single i 1
        have hei : e i = 0 := by simp [e, hdi]
        have hsupportTail : e.support ⊆ l.toFinset := by
          intro j hj
          have hji : j ≠ i := by
            intro hji
            subst j
            exact (Finsupp.mem_support_iff.mp hj hei).elim
          have hdj : d j ≠ 0 := by
            simpa [e, Finsupp.single_eq_of_ne hji] using
              (Finsupp.mem_support_iff.mp hj)
          have hjcons := hsupport (Finsupp.mem_support_iff.mpr hdj)
          rw [List.toFinset_cons, Finset.mem_insert] at hjcons
          exact hjcons.resolve_left hji
        have hedegree : ∀ j, e j ≤ 1 := by
          intro j
          exact (Nat.sub_le _ _).trans (hdegree j)
        have heq : ∀ j ∈ l, e j = d j := by
          intro j hj
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hil hj
          simp [e, Finsupp.single_eq_of_ne hji]
        have hsum : listExponentSum l e = listExponentSum l d :=
          listExponentSum_congr heq
        have hfold (H : MvPolynomial sigma R) :
            applyMonomialDifferentialAlong l e H =
              applyMonomialDifferentialAlong l d H :=
          applyMonomialDifferentialAlong_congr heq H
        change contractVariablePairs l
            (contractVariables (Sum.inl i) (Sum.inr i)
              (pairedProduct (MvPolynomial.monomial d c) G)) = _
        rw [contractVariables_pairedProduct_monomial i d c G (hdegree i),
          if_neg (by simp [hdi])]
        have hrec := ih hlnodup e hsupportTail hedegree (-c)
          (MvPolynomial.pderiv i G)
        rw [hsum, hfold] at hrec
        simp only [e] at hrec
        simpa [listExponentSum, applyMonomialDifferentialAlong, hdi,
          iteratedPDerivAt, pow_add] using hrec

theorem listExponentSum_differentialVariableOrder
    {sigma : Type*} [Fintype sigma] (d : sigma →₀ ℕ) :
    listExponentSum (differentialVariableOrder sigma) d =
      d.sum fun _ n => n := by
  classical
  rw [show listExponentSum (differentialVariableOrder sigma) d =
      ((differentialVariableOrder sigma).map fun i => d i).sum by rfl]
  rw [← List.sum_toFinset (fun i => d i)
    (nodup_differentialVariableOrder sigma)]
  have hall : (differentialVariableOrder sigma).toFinset = Finset.univ := by
    ext i
    simp
  rw [hall, Finsupp.sum_fintype d (fun _ n => n) (by simp)]

theorem applyMonomialDifferentialAlong_differentialVariableOrder
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (d : sigma →₀ ℕ) (G : MvPolynomial sigma R) :
    applyMonomialDifferentialAlong (differentialVariableOrder sigma) d G =
      applyMonomialDifferential d G := by
  rfl

/-- Contracting every left/right variable pair in `F(x) G(y)` realizes the
constant-coefficient differential action `F(-∂){G}` in the right block. -/
theorem contractVariablePairs_pairedProduct
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F G : MvPolynomial sigma R)
    (hF : MvPolynomial.IsMultiaffine F) :
    contractVariablePairs (differentialVariableOrder sigma) (pairedProduct F G) =
      MvPolynomial.rename Sum.inr (applyNegDifferential F G) := by
  classical
  unfold applyNegDifferential
  rw [MvPolynomial.sum_def]
  conv_lhs => rw [MvPolynomial.as_sum F]
  rw [pairedProduct, map_sum, Finset.sum_mul, contractVariablePairs_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change contractVariablePairs (differentialVariableOrder sigma)
      (pairedProduct (MvPolynomial.monomial d (MvPolynomial.coeff d F)) G) = _
  rw [contractVariablePairs_pairedProduct_monomial
    (differentialVariableOrder sigma)
    (nodup_differentialVariableOrder sigma) d
    (by intro i hi; simp) (fun i => MvPolynomial.degreeOf_le_iff.mp (hF i) d hd)]
  rw [listExponentSum_differentialVariableOrder,
    applyMonomialDifferentialAlong_differentialVariableOrder]
  simp

/-- A product in disjoint left and right variable blocks is multiaffine when
both factors are. -/
theorem isMultiaffine_pairedProduct
    {R sigma : Type*} [CommRing R]
    {F G : MvPolynomial sigma R}
    (hF : MvPolynomial.IsMultiaffine F)
    (hG : MvPolynomial.IsMultiaffine G) :
    MvPolynomial.IsMultiaffine (pairedProduct F G) := by
  apply (hF.rename Sum.inl_injective).mul_of_disjoint_vars
    (hG.rename Sum.inr_injective)
  rw [Finset.disjoint_left]
  intro x hxF hxG
  obtain ⟨i, hi, rfl⟩ := MvPolynomial.mem_vars_rename Sum.inl F hxF
  obtain ⟨j, hj, hji⟩ := MvPolynomial.mem_vars_rename Sum.inr G hxG
  exact Sum.inr_ne_inl hji

/-- Iterated paired contraction preserves multiaffineness. -/
theorem isMultiaffine_contractVariablePairs
    {R sigma : Type*} [CommRing R]
    {P : MvPolynomial (Sum sigma sigma) R}
    (hP : MvPolynomial.IsMultiaffine P) (l : List sigma) :
    MvPolynomial.IsMultiaffine (contractVariablePairs l P) := by
  unfold contractVariablePairs
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih =>
      rw [List.foldl_cons]
      exact ih (isMultiaffine_contractVariables hP (Sum.inl i) (Sum.inr i))

end

end RealRooted
