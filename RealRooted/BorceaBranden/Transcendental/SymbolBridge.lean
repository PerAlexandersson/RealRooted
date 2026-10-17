import RealRooted.BorceaBranden.Transcendental.PivotForward
import RealRooted.BorceaBranden.FiniteSymbolClassification
import RealRooted.MultivariateStability.Inversion

open scoped BigOperators

noncomputable section

namespace RealRooted.BorceaBranden

variable {τ σ : Type*} [Finite τ] [Fintype σ]

/-- Invert one named variable by transporting it to the distinguished `Option.none`
coordinate of `invertVariable`. -/
def invertVariableAt {υ : Type*} [DecidableEq υ] (d : ℕ) (i : υ)
    (p : MvPolynomial υ ℂ) : MvPolynomial υ ℂ :=
  MvPolynomial.rename (Equiv.optionSubtypeNe i)
    (invertVariable d
      (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm p))

/-- Named-variable inversion preserves upper-half-plane stability at any degree bound. -/
theorem MvUpperHalfPlaneStable.invertVariableAt
    {υ : Type*} [DecidableEq υ] {p : MvPolynomial υ ℂ}
    (i : υ) (d : ℕ) (hdegree : p.degreeOf i ≤ d)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStable (invertVariableAt d i p) := by
  unfold RealRooted.BorceaBranden.invertVariableAt
  apply MvUpperHalfPlaneStable.rename
  apply MvUpperHalfPlaneStable.invertVariable
  · have hrename := MvPolynomial.degreeOf_rename_of_injective
      (Equiv.optionSubtypeNe i).symm.injective i (p := p)
    simpa using hrename.trans_le hdegree
  · exact hp.rename

private theorem coeff_invertVariable_of_degree
    {υ : Type*} {p : MvPolynomial (Option υ) ℂ} (d : ℕ)
    (hdegree : p.degreeOf none ≤ d) (e : Option υ →₀ ℕ) :
    (invertVariable d p).coeff e =
      if e none ≤ d then
        (-1 : ℂ) ^ (d - e none) *
          p.coeff (e.some.optionElim (d - e none))
      else 0 := by
  unfold invertVariable
  let q := Polynomial.reflect d
    (((MvPolynomial.optionEquivLeft ℂ υ) p).comp (-Polynomial.X))
  rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none ℂ υ e
    ((MvPolynomial.optionEquivLeft ℂ υ).symm q)]
  rw [AlgEquiv.apply_symm_apply]
  dsimp only [q]
  rw [Polynomial.coeff_reflect]
  simp only [show (-Polynomial.X : Polynomial (MvPolynomial υ ℂ)) =
    Polynomial.C (-1) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases he : e none ≤ d
  · rw [ite_eq_left he, Polynomial.revAt_le he]
    rw [show (-1 : MvPolynomial υ ℂ) ^ (d - e none) =
      MvPolynomial.C ((-1 : ℂ) ^ (d - e none)) by simp]
    rw [mul_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.optionEquivLeft_coeff_coeff]
  · rw [ite_eq_right he, Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge he)]
    have hcoeff : p.coeff e = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hes
      have := MvPolynomial.degreeOf_le_iff.mp hdegree e hes
      exact he this
    rw [show (-1 : MvPolynomial υ ℂ) ^ e none =
      MvPolynomial.C ((-1 : ℂ) ^ e none) by simp]
    rw [mul_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.optionEquivLeft_coeff_coeff]
    have hcoeff' : p.coeff (e.some.optionElim (e none)) = 0 := by
      simpa using hcoeff
    rw [hcoeff', mul_zero]

private theorem degreeOf_invertVariable_none_le
    {υ : Type*} {p : MvPolynomial (Option υ) ℂ} (d : ℕ)
    (hdegree : p.degreeOf none ≤ d) :
    (invertVariable d p).degreeOf none ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro e he
  rw [MvPolynomial.mem_support_iff] at he
  rw [coeff_invertVariable_of_degree d hdegree e] at he
  by_contra hle
  rw [ite_eq_right hle] at he
  exact he rfl

private theorem degreeOf_invertVariable_some_le
    {υ : Type*} {p : MvPolynomial (Option υ) ℂ} (d : ℕ)
    (hdegree : p.degreeOf none ≤ d) (j : υ) :
    (invertVariable d p).degreeOf (some j) ≤ p.degreeOf (some j) := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro e he
  rw [MvPolynomial.mem_support_iff] at he
  rw [coeff_invertVariable_of_degree d hdegree e] at he
  by_cases hle : e none ≤ d
  · rw [ite_eq_left hle] at he
    have hin : p.coeff (e.some.optionElim (d - e none)) ≠ 0 :=
      (mul_ne_zero_iff.mp he).2
    have hbound := MvPolynomial.monomial_le_degreeOf (some j)
      (MvPolynomial.mem_support_iff.mpr hin)
    simpa using hbound
  · rw [ite_eq_right hle] at he
    exact (he rfl).elim

private theorem degreeOf_invertVariableAt_self_le
    {υ : Type*} [DecidableEq υ] {p : MvPolynomial υ ℂ}
    (i : υ) (d : ℕ) (hdegree : p.degreeOf i ≤ d) :
    (invertVariableAt d i p).degreeOf i ≤ d := by
  unfold invertVariableAt
  change (MvPolynomial.rename (Equiv.optionSubtypeNe i)
    (invertVariable d (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm p))).degreeOf
      ((Equiv.optionSubtypeNe i) none) ≤ d
  rw [MvPolynomial.degreeOf_rename_of_injective
    (Equiv.optionSubtypeNe i).injective]
  apply degreeOf_invertVariable_none_le d
  have hrename := MvPolynomial.degreeOf_rename_of_injective
    (Equiv.optionSubtypeNe i).symm.injective i (p := p)
  simpa using hrename.trans_le hdegree

private theorem degreeOf_invertVariableAt_of_ne_le
    {υ : Type*} [DecidableEq υ] {p : MvPolynomial υ ℂ}
    (i j : υ) (hji : j ≠ i) (d : ℕ) (hdegree : p.degreeOf i ≤ d) :
    (invertVariableAt d i p).degreeOf j ≤ p.degreeOf j := by
  unfold invertVariableAt
  rw [← (Equiv.optionSubtypeNe i).apply_symm_apply j,
    MvPolynomial.degreeOf_rename_of_injective
      (Equiv.optionSubtypeNe i).injective]
  rw [Equiv.optionSubtypeNe_symm_of_ne hji]
  have hisolated :
      (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm p).degreeOf none ≤ d := by
    simpa using (MvPolynomial.degreeOf_rename_of_injective
      (Equiv.optionSubtypeNe i).symm.injective i (p := p)).trans_le hdegree
  calc
    (invertVariable d
        (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm p)).degreeOf
          (some ⟨j, hji⟩) ≤
        (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm p).degreeOf
          (some ⟨j, hji⟩) :=
      degreeOf_invertVariable_some_le d hisolated ⟨j, hji⟩
    _ = p.degreeOf j := by
      simpa [Equiv.optionSubtypeNe_symm_of_ne hji] using
        (MvPolynomial.degreeOf_rename_of_injective
          (Equiv.optionSubtypeNe i).symm.injective j (p := p))

/-- Compose named-variable inversions in the order of a finite list. -/
def invertVariables {υ : Type*} [DecidableEq υ] (d : υ → ℕ) :
    List υ → MvPolynomial υ ℂ → MvPolynomial υ ℂ
  | [], p => p
  | i :: s, p => invertVariables d s (invertVariableAt (d i) i p)

private theorem degreeOf_invertVariables_le
    {υ : Type*} [DecidableEq υ] (d : υ → ℕ) (s : List υ)
    (p : MvPolynomial υ ℂ) (hdegree : ∀ i, p.degreeOf i ≤ d i) :
    ∀ i, (invertVariables d s p).degreeOf i ≤ d i := by
  induction s generalizing p with
  | nil => exact hdegree
  | cons j s ih =>
      apply ih
      intro i
      by_cases hij : i = j
      · subst i
        exact degreeOf_invertVariableAt_self_le j (d j) (hdegree j)
      · exact (degreeOf_invertVariableAt_of_ne_le j i hij (d j) (hdegree j)).trans
          (hdegree i)

/-- A finite composition of `invertVariable` in named coordinates preserves stability
when the corresponding coordinate degree bounds hold. -/
theorem MvUpperHalfPlaneStable.invertVariables
    {υ : Type*} [DecidableEq υ] (d : υ → ℕ) (s : List υ)
    {p : MvPolynomial υ ℂ} (hdegree : ∀ i, p.degreeOf i ≤ d i)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStable (invertVariables d s p) := by
  induction s generalizing p with
  | nil => exact hp
  | cons i s ih =>
      apply ih (degreeOf_invertVariables_le d [i] p hdegree)
      exact MvUpperHalfPlaneStable.invertVariableAt i (d i) (hdegree i) hp

private theorem coeff_invertVariableAt_of_degree
    {υ : Type*} [DecidableEq υ] {p : MvPolynomial υ ℂ}
    (i : υ) (d : ℕ) (hdegree : p.degreeOf i ≤ d) (m : υ →₀ ℕ) :
    (invertVariableAt d i p).coeff m =
      if m i ≤ d then
        (-1 : ℂ) ^ (d - m i) * p.coeff (m.update i (d - m i))
      else 0 := by
  let a := Equiv.optionSubtypeNe i
  let n := m.mapDomain a.symm
  have hn : n.mapDomain a = m := by
    ext j
    rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
    simp
  unfold invertVariableAt
  conv_lhs => rw [← hn]
  rw [MvPolynomial.coeff_rename_mapDomain a a.injective]
  have hisolated :
      (MvPolynomial.rename a.symm p).degreeOf none ≤ d := by
    simpa [a] using (MvPolynomial.degreeOf_rename_of_injective
      a.symm.injective i (p := p)).trans_le hdegree
  rw [coeff_invertVariable_of_degree d hisolated n]
  have hnone : n none = m i := by
    rw [Finsupp.mapDomain_equiv_apply]
    simp [a]
  rw [hnone]
  by_cases hle : m i ≤ d
  · rw [ite_eq_left hle]
    let u := m.update i (d - m i)
    have hu : u.mapDomain a.symm = n.some.optionElim (d - m i) := by
      ext o
      cases o with
      | none =>
          rw [Finsupp.mapDomain_equiv_apply]
          simp [u, n, a]
      | some j =>
          rw [Finsupp.mapDomain_equiv_apply]
          rw [Equiv.symm_symm, Finsupp.optionElim_apply_some]
          change u (a (some j)) = n.some j
          simp only [a, Equiv.optionSubtypeNe_some]
          dsimp only [n]
          change u j.1 = (m.mapDomain a.symm) (some j)
          rw [Finsupp.mapDomain_equiv_apply]
          simp [u, a, j.property]
    rw [← hu, MvPolynomial.coeff_rename_mapDomain a.symm a.symm.injective]
    simp [u, hle]
  · rw [ite_eq_right hle]
    simp [hle]

private def complementOnList {υ : Type*} [Finite υ]
    (d : υ → ℕ) (s : List υ) (m : υ →₀ ℕ) : υ →₀ ℕ := by
  classical
  let _ := Fintype.ofFinite υ
  exact Finsupp.equivFunOnFinite.symm fun i =>
    if i ∈ s then d i - m i else m i

private def inversionExponent {υ : Type*}
    (d : υ → ℕ) (s : List υ) (m : υ →₀ ℕ) : ℕ :=
  (s.map fun i => d i - m i).sum

private theorem coeff_invertVariables_of_nodup
    {υ : Type*} [Finite υ] [DecidableEq υ]
    (d : υ → ℕ) (s : List υ) (hs : s.Nodup)
    (p : MvPolynomial υ ℂ) (hdegree : ∀ i, p.degreeOf i ≤ d i)
    (m : υ →₀ ℕ) (hm : ∀ i ∈ s, m i ≤ d i) :
    (invertVariables d s p).coeff m =
      (-1 : ℂ) ^ inversionExponent d s m *
        p.coeff (complementOnList d s m) := by
  induction s generalizing p m with
  | nil => simp [invertVariables, inversionExponent, complementOnList]
  | cons i s ih =>
      rw [List.nodup_cons] at hs
      rw [invertVariables]
      have hnext := degreeOf_invertVariables_le d [i] p hdegree
      rw [ih hs.2 (invertVariableAt (d i) i p) hnext m
        (fun j hj => hm j (List.mem_cons_of_mem i hj))]
      have hcomp_i : complementOnList d s m i = m i := by
        simp [complementOnList, hs.1]
      rw [coeff_invertVariableAt_of_degree i (d i) (hdegree i)]
      rw [hcomp_i, ite_eq_left (hm i (List.mem_cons_self))]
      have hcomp :
          (complementOnList d s m).update i (d i - m i) =
            complementOnList d (i :: s) m := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [complementOnList, hs.1]
        · simp [complementOnList, hji]
      rw [hcomp]
      simp only [inversionExponent, List.map_cons, List.sum_cons]
      rw [pow_add]
      ring

private def rightVariableList (τ σ : Type*) [Fintype σ] : List (τ ⊕ σ) :=
  List.ofFn fun k : Fin (Fintype.card σ) =>
    Sum.inr ((Fintype.equivFin σ).symm k)

private theorem rightVariableList_nodup (τ σ : Type*) [Fintype σ] :
    (rightVariableList τ σ).Nodup := by
  rw [rightVariableList, List.nodup_ofFn]
  exact Sum.inr_injective.comp (Fintype.equivFin σ).symm.injective

omit [Finite τ] in
private theorem inr_mem_rightVariableList (i : σ) :
    Sum.inr i ∈ rightVariableList τ σ := by
  rw [rightVariableList, List.mem_ofFn', Set.mem_range]
  exact ⟨Fintype.equivFin σ i, by simp⟩

omit [Finite τ] in
private theorem mem_rightVariableList_eq_inr
    (x : τ ⊕ σ) (hx : x ∈ rightVariableList τ σ) :
    ∃ i, x = Sum.inr i := by
  rw [rightVariableList, List.mem_ofFn', Set.mem_range] at hx
  obtain ⟨k, rfl⟩ := hx
  exact ⟨(Fintype.equivFin σ).symm k, rfl⟩

private def rightInversionBounds (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) : τ ⊕ σ → ℕ :=
  Sum.elim (fun i => p.degreeOf (Sum.inl i)) (fun i => β i)

/-- The finite right-block composition of `invertVariable`, with degree `β i` in
the coordinate `w_i`. -/
def invertRightVariables (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ) :
    MvPolynomial (τ ⊕ σ) ℂ := by
  classical
  exact invertVariables (rightInversionBounds β p) (rightVariableList τ σ) p

omit [Finite τ] in
/-- The finite right-block composition of `invertVariable` preserves stability. -/
theorem MvUpperHalfPlaneStable.invertRightVariables
    (β : σ →₀ ℕ) {p : MvPolynomial (τ ⊕ σ) ℂ}
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStable (invertRightVariables β p) := by
  classical
  unfold RealRooted.BorceaBranden.invertRightVariables
  apply MvUpperHalfPlaneStable.invertVariables
  · rintro (i | i)
    · exact le_rfl
    · exact hdegree i
  · exact hp

omit [Finite τ] in
private theorem inversionExponent_rightVariableList
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (e : τ ⊕ σ →₀ ℕ) :
    inversionExponent (rightInversionBounds β p) (rightVariableList τ σ) e =
      ∑ i, (β i - e (Sum.inr i)) := by
  classical
  unfold inversionExponent rightVariableList
  simp only [List.map_ofFn, List.sum_ofFn, rightInversionBounds]
  rw [← (Fintype.equivFin σ).symm.sum_comp]
  rfl

private theorem complementOnList_rightVariableList
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (e : τ ⊕ σ →₀ ℕ) :
    complementOnList (rightInversionBounds β p) (rightVariableList τ σ) e =
      (Finsupp.sumFinsuppEquivProdFinsupp e).1.sumElim
        (β - (Finsupp.sumFinsuppEquivProdFinsupp e).2) := by
  classical
  ext x
  cases x with
  | inl i =>
      simp [complementOnList, rightVariableList, List.mem_ofFn', Set.mem_range]
  | inr i =>
      simp [complementOnList, inr_mem_rightVariableList (τ := τ) i,
        rightInversionBounds]

/-- Complement/sign coefficient formula for the finite right-block composition of
`invertVariable`. -/
theorem coeff_invertRightVariables (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ)
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i)
    (e : τ ⊕ σ →₀ ℕ) :
    (invertRightVariables β p).coeff e =
      if (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β then
        (-1 : ℂ) ^
            (∑ i, (β i - (Finsupp.sumFinsuppEquivProdFinsupp e).2 i)) *
          p.coeff
            ((Finsupp.sumFinsuppEquivProdFinsupp e).1.sumElim
              (β - (Finsupp.sumFinsuppEquivProdFinsupp e).2))
      else 0 := by
  classical
  let d := rightInversionBounds β p
  let s := rightVariableList τ σ
  have hd : ∀ x, p.degreeOf x ≤ d x := by
    rintro (i | i)
    · exact le_rfl
    · exact hdegree i
  by_cases hle : (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β
  · rw [ite_eq_left hle]
    unfold invertRightVariables
    rw [coeff_invertVariables_of_nodup d s (rightVariableList_nodup τ σ) p hd e]
    · rw [inversionExponent_rightVariableList,
        complementOnList_rightVariableList]
      congr 2
    · intro x hx
      obtain ⟨i, rfl⟩ := mem_rightVariableList_eq_inr x hx
      exact hle i
  · rw [ite_eq_right hle]
    rw [Finsupp.le_def] at hle
    push Not at hle
    obtain ⟨i, hi⟩ := hle
    apply MvPolynomial.notMem_support_iff.mp
    intro hes
    have hmon := MvPolynomial.monomial_le_degreeOf (Sum.inr i) hes
    have hout := degreeOf_invertVariables_le d s p hd (Sum.inr i)
    change (invertRightVariables β p).degreeOf (Sum.inr i) ≤ β i at hout
    exact (Nat.not_le_of_gt hi) (hmon.trans hout)

/-- The signed reciprocal in a finite right-coordinate degree box. -/
def signedRightBoxReciprocal (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) : MvPolynomial (τ ⊕ σ) ℂ := by
  classical
  exact glue (fun α => MvPolynomial.coeffPoly (β - α) p)
    (fun α => (-1 : ℝ) ^ (∑ i, (β i - α i))) β

/-- The paper-normalized reciprocal; its output coefficient at `w^α` has sign
`(-1)^|α|`. -/
def paperRightBoxReciprocal (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) : MvPolynomial (τ ⊕ σ) ℂ := by
  classical
  exact glue (fun α => MvPolynomial.coeffPoly (β - α) p)
    (fun α => (-1 : ℝ) ^ (∑ i, α i)) β

omit [Finite τ] in
/-- Coefficient formula for the signed right-box reciprocal. -/
theorem coeff_signedRightBoxReciprocal (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) (e : τ ⊕ σ →₀ ℕ) :
    (signedRightBoxReciprocal β p).coeff e =
      if (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β then
        ((-1 : ℂ) ^
          (∑ i, (β i - (Finsupp.sumFinsuppEquivProdFinsupp e).2 i))) *
          p.coeff
            ((Finsupp.sumFinsuppEquivProdFinsupp e).1.sumElim
              (β - (Finsupp.sumFinsuppEquivProdFinsupp e).2))
      else 0 := by
  classical
  rw [signedRightBoxReciprocal, coeff_glue]
  unfold seriesCoeff
  rw [MvPolynomial.coeff_coeffPoly]
  split_ifs with h
  · push_cast
    rfl
  · simp

/-- The direct complement/sign formula agrees with the finite right-coordinate
composition of `invertVariable`. -/
theorem invertRightVariables_eq_signedRightBoxReciprocal
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i) :
    invertRightVariables β p = signedRightBoxReciprocal β p := by
  ext e
  rw [coeff_invertRightVariables β p hdegree e,
    coeff_signedRightBoxReciprocal]

/-- The arbitrary-degree signed right-box reciprocal preserves stability. -/
theorem MvUpperHalfPlaneStable.signedRightBoxReciprocal
    (β : σ →₀ ℕ) {p : MvPolynomial (τ ⊕ σ) ℂ}
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStable (signedRightBoxReciprocal β p) := by
  rw [← invertRightVariables_eq_signedRightBoxReciprocal β p hdegree]
  exact MvUpperHalfPlaneStable.invertRightVariables β hdegree hp

omit [Finite τ] in
/-- Coefficient formula for the paper-normalized right-box reciprocal. -/
theorem coeff_paperRightBoxReciprocal (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) (e : τ ⊕ σ →₀ ℕ) :
    (paperRightBoxReciprocal β p).coeff e =
      if (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β then
        ((-1 : ℂ) ^
          (∑ i, (Finsupp.sumFinsuppEquivProdFinsupp e).2 i)) *
          p.coeff
            ((Finsupp.sumFinsuppEquivProdFinsupp e).1.sumElim
              (β - (Finsupp.sumFinsuppEquivProdFinsupp e).2))
      else 0 := by
  classical
  rw [paperRightBoxReciprocal, coeff_glue]
  unfold seriesCoeff
  rw [MvPolynomial.coeff_coeffPoly]
  split_ifs with h
  · push_cast
    rfl
  · simp

private theorem neg_one_pow_box_sub (β α : σ →₀ ℕ) (hαβ : α ≤ β) :
    (-1 : ℂ) ^ (∑ i, β i) * (-1 : ℂ) ^ (∑ i, (β i - α i)) =
      (-1 : ℂ) ^ (∑ i, α i) := by
  have hsum : (∑ i, β i) = (∑ i, α i) + ∑ i, (β i - α i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (Nat.add_sub_of_le (hαβ i)).symm
  rw [hsum, pow_add]
  have hsquare : (-1 : ℂ) ^ (∑ i, (β i - α i)) *
      (-1 : ℂ) ^ (∑ i, (β i - α i)) = 1 := by
    rw [← mul_pow]
    simp
  rw [mul_assoc, hsquare, mul_one]

omit [Finite τ] in
/-- The paper normalization is the signed reciprocal multiplied by the global sign
`(-1)^|β|`. -/
theorem paperRightBoxReciprocal_eq_globalSign_mul
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ) :
    paperRightBoxReciprocal β p =
      MvPolynomial.C ((-1 : ℂ) ^ (∑ i, β i)) * signedRightBoxReciprocal β p := by
  classical
  ext e
  rw [coeff_paperRightBoxReciprocal, MvPolynomial.coeff_C_mul,
    coeff_signedRightBoxReciprocal]
  split_ifs with hle
  · rw [← mul_assoc, neg_one_pow_box_sub β _ hle]
  · simp

/-- The paper-normalized right-box reciprocal preserves stability. -/
theorem MvUpperHalfPlaneStable.paperRightBoxReciprocal
    (β : σ →₀ ℕ) {p : MvPolynomial (τ ⊕ σ) ℂ}
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStable (paperRightBoxReciprocal β p) := by
  rw [paperRightBoxReciprocal_eq_globalSign_mul]
  apply MvUpperHalfPlaneStable.C_mul
  · exact MvUpperHalfPlaneStable.signedRightBoxReciprocal β hdegree hp
  · simp

/-- The signed right-box reciprocal has right-coordinate degree at most the box. -/
theorem degreeOf_signedRightBoxReciprocal_inr_le
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i) (i : σ) :
    (signedRightBoxReciprocal β p).degreeOf (Sum.inr i) ≤ β i := by
  classical
  rw [← invertRightVariables_eq_signedRightBoxReciprocal β p hdegree]
  let d := rightInversionBounds β p
  let s := rightVariableList τ σ
  have hd : ∀ x, p.degreeOf x ≤ d x := by
    rintro (j | j)
    · exact le_rfl
    · exact hdegree j
  exact degreeOf_invertVariables_le d s p hd (Sum.inr i)

private theorem neg_one_pow_box_sub_mul (β α : σ →₀ ℕ) (hαβ : α ≤ β) :
    (-1 : ℂ) ^ (∑ i, (β i - α i)) * (-1 : ℂ) ^ (∑ i, α i) =
      (-1 : ℂ) ^ (∑ i, β i) := by
  have hsum : (∑ i, β i) = (∑ i, (β i - α i)) + ∑ i, α i := by
    rw [add_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (Nat.add_sub_of_le (hαβ i)).symm
  rw [hsum, pow_add]

omit [Finite τ] in
/-- Applying the signed right-box reciprocal twice gives the global sign
`(-1)^|β|`. -/
theorem signedRightBoxReciprocal_involutive
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i) :
    signedRightBoxReciprocal β (signedRightBoxReciprocal β p) =
      MvPolynomial.C ((-1 : ℂ) ^ (∑ i, β i)) * p := by
  classical
  ext e
  rw [coeff_signedRightBoxReciprocal, MvPolynomial.coeff_C_mul]
  let E : (τ ⊕ σ →₀ ℕ) ≃ (τ →₀ ℕ) × (σ →₀ ℕ) :=
    Finsupp.sumFinsuppEquivProdFinsupp
  by_cases hle : (E e).2 ≤ β
  · have hle' : (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β := by
      simpa only [E] using hle
    rw [ite_eq_left hle']
    rw [coeff_signedRightBoxReciprocal]
    have hsub : β - (E e).2 ≤ β := fun i => Nat.sub_le _ _
    have hpair :
        Finsupp.sumFinsuppEquivProdFinsupp
            ((E e).1.sumElim (β - (E e).2)) =
          ((E e).1, β - (E e).2) := by
      change E (E.symm ((E e).1, β - (E e).2)) = _
      exact E.apply_symm_apply _
    rw [hpair]
    rw [ite_eq_left hsub]
    have hsubsub : β - (β - (E e).2) = (E e).2 := by
      ext i
      exact Nat.sub_sub_self (hle i)
    have he : (E e).1.sumElim (E e).2 = e := by
      change E.symm (E e) = e
      exact E.symm_apply_apply e
    rw [hsubsub, he, ← mul_assoc]
    have houter :
        (∑ i, (β i - (Finsupp.sumFinsuppEquivProdFinsupp e).2 i)) =
          ∑ i, (β i - (E e).2 i) := by
      rfl
    have hinner :
        (∑ i, (β i - (β - (E e).2) i)) = ∑ i, (E e).2 i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Nat.sub_sub_self (hle i)
    rw [houter, hinner]
    rw [neg_one_pow_box_sub_mul β (E e).2 hle]
  · have hle' : ¬(Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β := by
      simpa only [E] using hle
    rw [ite_eq_right hle']
    have hpzero : p.coeff e = 0 := by
      rw [Finsupp.le_def] at hle'
      push Not at hle'
      obtain ⟨i, hi⟩ := hle'
      apply MvPolynomial.notMem_support_iff.mp
      intro hes
      have hmon := MvPolynomial.monomial_le_degreeOf (Sum.inr i) hes
      exact (Nat.not_le_of_gt hi) (hmon.trans (hdegree i))
    rw [hpzero, mul_zero]

/-- Stability is equivalent before and after the signed right-box reciprocal. -/
theorem signedRightBoxReciprocal_stable_iff
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i) :
    MvUpperHalfPlaneStable (signedRightBoxReciprocal β p) ↔
      MvUpperHalfPlaneStable p := by
  constructor
  · intro hrecip
    have htwice := MvUpperHalfPlaneStable.signedRightBoxReciprocal β
      (fun i => degreeOf_signedRightBoxReciprocal_inr_le β p hdegree i) hrecip
    rw [signedRightBoxReciprocal_involutive β p hdegree] at htwice
    intro z hz
    have hne := htwice z hz
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hne
    exact (mul_ne_zero_iff.mp hne).2
  · exact fun hp => MvUpperHalfPlaneStable.signedRightBoxReciprocal β hdegree hp

/-- Stability is equivalent before and after the normalized right-box reciprocal. -/
theorem paperRightBoxReciprocal_stable_iff
    (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (hdegree : ∀ i, p.degreeOf (Sum.inr i) ≤ β i) :
    MvUpperHalfPlaneStable (paperRightBoxReciprocal β p) ↔
      MvUpperHalfPlaneStable p := by
  rw [paperRightBoxReciprocal_eq_globalSign_mul]
  constructor
  · intro hscaled
    apply (signedRightBoxReciprocal_stable_iff β p hdegree).mp
    intro z hz
    have hne := hscaled z hz
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hne
    exact (mul_ne_zero_iff.mp hne).2
  · intro hp
    exact MvUpperHalfPlaneStable.C_mul
      ((signedRightBoxReciprocal_stable_iff β p hdegree).mpr hp) (by simp)

private theorem fall_mul_signedInvFactorial_eq_boxChoose
    (α β : σ →₀ ℕ) :
    (fall α β : ℂ) * signedInvFactorial α =
      (-1 : ℂ) ^ (∑ i, α i) *
        (MvPolynomial.boxChoose (fun i => β i) α : ℂ) := by
  classical
  unfold fall signedInvFactorial multiFactorial MvPolynomial.boxChoose
  have hdesc :
      (∏ i, (β i).descFactorial (α i)) =
        (∏ i, (α i).factorial) * ∏ i, (β i).choose (α i) := by
    simp_rw [Nat.descFactorial_eq_factorial_mul_choose,
      Finset.prod_mul_distrib]
  have hdescReal :
      (∏ i, ((β i).descFactorial (α i) : ℝ)) =
        ((∏ i, (α i).factorial) * ∏ i, (β i).choose (α i) : ℕ) := by
    exact_mod_cast hdesc
  rw [hdescReal]
  push_cast
  have hfactorial : (∏ i, ((α i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _hi => by
      exact_mod_cast Nat.factorial_ne_zero (α i)
  field_simp

omit [Finite τ] [Fintype σ] in
private theorem coeffPoly_eq_sourceCoefficientGeneral
    (p : MvPolynomial (τ ⊕ σ) ℂ) (α : σ →₀ ℕ) :
    MvPolynomial.coeffPoly α p = sourceCoefficientGeneral p α := by
  ext γ
  rw [MvPolynomial.coeff_coeffPoly, coeff_sourceCoefficientGeneral]

omit [Finite τ] in
private theorem coeff_algebraicSymbol_at_complement
    (β : σ →₀ ℕ) (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (α : σ →₀ ℕ) (hαβ : α ≤ β) (γ : τ →₀ ℕ) :
    (MvPolynomial.algebraicSymbol (fun i => β i)
      (degreeBoxRestriction (fun i => β i) T)).coeff
        (γ.sumElim (β - α)) =
      (MvPolynomial.boxChoose (fun i => β i) α : ℂ) *
        (T (MvPolynomial.monomial α 1)).coeff γ := by
  classical
  let r : {r : σ →₀ ℕ // ∀ i, r i ≤ β i} :=
    ⟨β - α, fun i => Nat.sub_le _ _⟩
  have hcomp :
      boxComplementIndex (fun i => β i) r =
        (⟨α, hαβ⟩ : {m : σ →₀ ℕ // ∀ i, m i ≤ β i}) := by
    apply Subtype.ext
    ext i
    simp [r, Nat.sub_sub_self (hαβ i)]
  have hsource := congrArg (fun p : MvPolynomial τ ℂ => p.coeff γ)
    (sourceCoefficientGeneral_algebraicSymbol (fun i => β i)
      (degreeBoxRestriction (fun i => β i) T) r)
  rw [coeff_sourceCoefficientGeneral, MvPolynomial.coeff_C_mul] at hsource
  rw [hcomp] at hsource
  simp only [degreeBoxRestriction, LinearMap.comp_apply, Submodule.coe_subtype,
    MvPolynomial.coe_basisDegreeOfLE] at hsource
  have hchoose := boxChoose_boxComplementIndex (fun i => β i) r
  rw [hcomp] at hchoose
  simpa only [r, degreeBoxRestriction, hchoose] using hsource

omit [Finite τ] in
/-- The normalized right-box reciprocal of the algebraic symbol is exactly the Jensen
truncation `T[(1 - zw)^β]`.  This is the algebraic identity in
Borcea--Brändén, arXiv:0809.0401, Remark 1.1. -/
theorem paperRightBoxReciprocal_algebraicSymbol
    (β : σ →₀ ℕ) (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) :
    paperRightBoxReciprocal β
        (MvPolynomial.algebraicSymbol (fun i => β i)
          (degreeBoxRestriction (fun i => β i) T)) =
      jensenTruncation β T := by
  classical
  ext e
  rw [coeff_paperRightBoxReciprocal, coeff_jensenTruncation]
  split_ifs with hle
  · rw [coeff_algebraicSymbol_at_complement β T _ hle]
    unfold transcendentalSymbolCoeff seriesCoeff
    rw [coeff_transcendentalSymbolPolynomial]
    rw [← mul_assoc]
    rw [← fall_mul_signedInvFactorial_eq_boxChoose]
    ring
  · simp

/-- The finite algebraic symbol is stable exactly when the Jensen truncation is
stable.  This is the L9 bridge used in the complex transcendental classification of
Borcea--Brändén, arXiv:0809.0401, Theorem 1.3. -/
theorem algebraicSymbol_stable_iff_jensenTruncation_stable
    (β : σ →₀ ℕ) (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvUpperHalfPlaneStable
        (MvPolynomial.algebraicSymbol (fun i => β i)
          (degreeBoxRestriction (fun i => β i) T)) ↔
      MvUpperHalfPlaneStable (jensenTruncation β T) := by
  rw [← paperRightBoxReciprocal_algebraicSymbol β T]
  exact (paperRightBoxReciprocal_stable_iff β _
    (MvPolynomial.degreeOf_algebraicSymbol_inr_le _ _)).symm

end RealRooted.BorceaBranden
