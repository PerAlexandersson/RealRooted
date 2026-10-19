import RealRooted.MultivariateStability.MorrisBFlow
import RealRooted.Mathlib.Analysis.Normed.Operator.Trotter
import RealRooted.Mathlib.Analysis.Normed.Algebra.Exponential
import RealRooted.MultivariateStability.CoeffLimit
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# The Liu--Zhang Morris flow

This file proves Theorem 4.9 of Liu--Zhang, arXiv:2609.15201v2. On the
finite-dimensional space of symmetric polynomials of total degree at most
`N`, the exponential of `t * (B_q - A_q)` preserves real stability for
`t ≥ 0`. The proof identifies the two factor flows on the monomial and
elementary bases and applies the Lie--Trotter product formula.
-/

open MvPolynomial

namespace RealRooted.LiuZhang

noncomputable section

private theorem exp_apply_of_eigenvector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) (x : E) (c : ℝ)
    (hx : T x = c • x) :
    NormedSpace.exp T x = Real.exp c • x := by
  have hpow : ∀ n : ℕ, (T ^ n) x = c ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx,
          pow_succ, smul_smul]
  have hs : Summable fun n : ℕ =>
      ((n.factorial : ℝ)⁻¹ • T ^ n) := by
    simpa only [NormedSpace.expSeries_apply_eq] using
      NormedSpace.expSeries_summable T
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) x = _
  rw [show (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) x =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • T ^ n) x by
    simpa using (ContinuousLinearMap.apply ℝ E x).map_tsum hs]
  simp_rw [smul_apply, hpow, smul_smul]
  have hc : Summable fun n : ℕ => (n.factorial : ℝ)⁻¹ * c ^ n := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.summable_pow_div_factorial c
  rw [hc.tsum_smul_const x]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  congr

/-- The index type of pairs `(n, μ)` with `n ≤ N` and `μ` a partition of `n` with at most `q`
parts. -/
abbrev MorrisDegreeIndex (q N : ℕ) :=
  Σ n : Fin (N + 1), {mu : n.val.Partition // mu.parts.card ≤ q}

noncomputable instance (q N : ℕ) : Fintype (MorrisDegreeIndex q N) :=
  Fintype.ofFinite _

/-- The monomial symmetric polynomial of the partition of an index `(n, μ)`, in `q` variables. -/
def morrisMsymm (q N : ℕ) (i : MorrisDegreeIndex q N) :
    MvPolynomial (Fin q) ℝ :=
  msymm (Fin q) ℝ i.2.1

/-- The submodule of `MvPolynomial (Fin q) ℝ` spanned by the monomial symmetric polynomials
`morrisMsymm q N i`. -/
def morrisDegreeSubmodule (q N : ℕ) :
    Submodule ℝ (MvPolynomial (Fin q) ℝ) :=
  Submodule.span ℝ (Set.range (morrisMsymm q N))

/-- The space of symmetric polynomials in `q` variables of total degree at most `N`, spanned by the
monomial symmetric polynomials `morrisMsymm q N`. -/
abbrev MorrisDegreeSpace (q N : ℕ) := morrisDegreeSubmodule q N

noncomputable instance (q N : ℕ) :
    Module.Finite ℝ (MorrisDegreeSpace q N) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range (morrisMsymm q N))

theorem morrisMsymm_mem (q N : ℕ) (i : MorrisDegreeIndex q N) :
    morrisMsymm q N i ∈ morrisDegreeSubmodule q N :=
  Submodule.subset_span (Set.mem_range_self i)

theorem msymm_mem_morrisDegreeSubmodule {q N n : ℕ}
    (mu : n.Partition) (hmu : mu.parts.card ≤ q) (hn : n ≤ N) :
    msymm (Fin q) ℝ mu ∈ morrisDegreeSubmodule q N := by
  let i : MorrisDegreeIndex q N :=
    ⟨⟨n, Nat.lt_succ_iff.mpr hn⟩, ⟨mu, hmu⟩⟩
  exact morrisMsymm_mem q N i

theorem mem_morrisDegreeSubmodule_of_homogeneous {q N n : ℕ}
    {P : MvPolynomial (Fin q) ℝ} (hP : P.IsSymmetric)
    (hhom : P.IsHomogeneous n) (hn : n ≤ N) :
    P ∈ morrisDegreeSubmodule q N := by
  rw [eq_sum_msymm hP hhom]
  apply Submodule.sum_mem
  intro mu _
  apply Submodule.smul_mem
  by_cases hmu : mu.parts.card ≤ q
  · exact msymm_mem_morrisDegreeSubmodule mu hmu hn
  · rw [msymm_eq_zero_of_card_lt mu (by simpa using Nat.lt_of_not_ge hmu)]
    exact Submodule.zero_mem _

theorem IsSymmetric.mem_morrisDegreeSubmodule {q N : ℕ}
    {P : MvPolynomial (Fin q) ℝ} (hP : P.IsSymmetric)
    (hdeg : P.totalDegree ≤ N) :
    P ∈ morrisDegreeSubmodule q N := by
  rw [← P.sum_homogeneousComponent]
  apply Submodule.sum_mem
  intro n hn
  rw [Finset.mem_range] at hn
  apply mem_morrisDegreeSubmodule_of_homogeneous
  · intro e
    rw [rename_homogeneousComponent, hP e]
  · exact homogeneousComponent_isHomogeneous n P
  · exact (Nat.lt_succ_iff.mp hn).trans hdeg

theorem isSymmetric_of_mem_morrisDegreeSubmodule {q N : ℕ}
    {P : MvPolynomial (Fin q) ℝ}
    (hP : P ∈ morrisDegreeSubmodule q N) : P.IsSymmetric := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      exact msymm_isSymmetric (σ := Fin q) (R := ℝ) i.2.1
  | zero => simp
  | add P Q _ _ hP hQ => exact hP.add hQ
  | smul r P _ hP => exact hP.smul r

/-- The elementary product `morrisElementary q μ` attached to an index `(n, μ)`. -/
def morrisElementaryPoly (q N : ℕ) (i : MorrisDegreeIndex q N) :
    MvPolynomial (Fin q) ℝ :=
  morrisElementary (R := ℝ) q i.2.1

/-- The submodule spanned by the elementary products `morrisElementaryPoly q N i`. -/
def morrisElementarySubmodule (q N : ℕ) :
    Submodule ℝ (MvPolynomial (Fin q) ℝ) :=
  Submodule.span ℝ (Set.range (morrisElementaryPoly q N))

theorem morrisElementary_mem_morrisDegreeSubmodule {q N n : ℕ}
    (mu : n.Partition) (hmu : mu.parts.card ≤ q) (hn : n ≤ N) :
    morrisElementary (R := ℝ) q mu ∈ morrisDegreeSubmodule q N := by
  rw [morrisElementary,
    esymmPart_conjugate_eq_msymm_add_lower mu hmu]
  apply Submodule.add_mem
  · exact msymm_mem_morrisDegreeSubmodule mu hmu hn
  · apply Submodule.sum_mem
    intro eta _
    apply Submodule.smul_mem
    by_cases hlen : eta.parts.card ≤ q
    · exact msymm_mem_morrisDegreeSubmodule eta hlen hn
    · rw [msymm_eq_zero_of_card_lt eta (by simpa using Nat.lt_of_not_ge hlen)]
      exact Submodule.zero_mem _

theorem morrisDegreeSubmodule_eq_elementary (q N : ℕ) :
    morrisDegreeSubmodule q N = morrisElementarySubmodule q N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb⟩ := msymm_eq_esymmPart_conjugate_add_lower
      (K := ℝ) i.2.1 i.2.2
    rw [show morrisMsymm q N i = msymm (Fin q) ℝ i.2.1 by rfl,
      hb]
    apply Submodule.add_mem
    · apply Submodule.subset_span
      exact ⟨i, rfl⟩
    · apply Submodule.sum_mem
      intro eta heta
      apply Submodule.smul_mem
      have heta' := (mem_strictDominanceDownset.mp heta).2
      let j : MorrisDegreeIndex q N :=
        ⟨i.1, ⟨eta, heta'⟩⟩
      exact Submodule.subset_span ⟨j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact morrisElementary_mem_morrisDegreeSubmodule i.2.1 i.2.2
      (Nat.lt_succ_iff.mp i.1.isLt)

theorem totalDegree_le_of_mem_morrisDegreeSubmodule {q N : ℕ}
    {P : MvPolynomial (Fin q) ℝ}
    (hP : P ∈ morrisDegreeSubmodule q N) : P.totalDegree ≤ N := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      exact (isHomogeneous_msymm (σ := Fin q) (R := ℝ) i.2.1).totalDegree_le.trans
        (Nat.lt_succ_iff.mp i.1.isLt)
  | zero => simp
  | add P Q _ _ hP hQ =>
      exact (totalDegree_add P Q).trans (max_le hP hQ)
  | smul r P _ hP => exact (totalDegree_smul_le r P).trans hP

theorem morrisA_mem_morrisDegreeSubmodule {q N : ℕ}
    {P : MvPolynomial (Fin q) ℝ}
    (hP : P ∈ morrisDegreeSubmodule q N) :
    morrisA q P ∈ morrisDegreeSubmodule q N := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      rw [morrisMsymm, morrisA_msymm]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      exact Submodule.smul_mem _ _ (morrisMsymm_mem q N i)
  | zero => simp
  | add P Q _ _ hP hQ =>
      rw [map_add]
      exact Submodule.add_mem _ hP hQ
  | smul r P _ hP =>
      rw [map_smul]
      exact Submodule.smul_mem _ r hP

theorem morrisB_mem_morrisDegreeSubmodule {q N : ℕ}
    {P : MvPolynomial (Fin q) ℝ}
    (hP : P ∈ morrisDegreeSubmodule q N) :
    morrisB q P ∈ morrisDegreeSubmodule q N := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      let mu : {mu : i.1.val.Partition // mu.parts.card ≤ q} := i.2
      let b := fun eta : {eta : i.1.val.Partition // eta.parts.card ≤ q} =>
        msymm (Fin q) ℝ eta.1
      let c := fun eta : {eta : i.1.val.Partition // eta.parts.card ≤ q} =>
        (morrisBWeight q eta.1.conjugate : ℝ)
      have htri := morrisB_isTriangularOn_msymm
        (R := ℝ) (N := i.1.val) (q := q) mu
      have hlower : LinearMap.lowerSpan (R := ℝ) b mu ≤
          morrisDegreeSubmodule q N := by
        apply Submodule.span_le.mpr
        rintro _ ⟨eta, _heta, rfl⟩
        exact msymm_mem_morrisDegreeSubmodule eta.1 eta.2
          (Nat.lt_succ_iff.mp i.1.isLt)
      have hrem : morrisB q (b mu) - c mu • b mu ∈
          morrisDegreeSubmodule q N := hlower htri
      have hdiag : c mu • b mu ∈ morrisDegreeSubmodule q N := by
        apply Submodule.smul_mem
        exact msymm_mem_morrisDegreeSubmodule mu.1 mu.2
          (Nat.lt_succ_iff.mp i.1.isLt)
      change morrisB q (b mu) ∈ morrisDegreeSubmodule q N
      simpa only [sub_add_cancel] using
        (morrisDegreeSubmodule q N).add_mem hrem hdiag
  | zero => simp
  | add P Q _ _ hP hQ =>
      rw [map_add]
      exact Submodule.add_mem _ hP hQ
  | smul r P _ hP =>
      rw [map_smul]
      exact Submodule.smul_mem _ r hP

/-- The operator `A_q`, restricted to `MorrisDegreeSpace q N`. -/
def morrisAOnDegree (q N : ℕ) :
    MorrisDegreeSpace q N →ₗ[ℝ] MorrisDegreeSpace q N :=
  (morrisA q).restrict fun _ hP =>
    morrisA_mem_morrisDegreeSubmodule hP

/-- The operator `B_q`, restricted to `MorrisDegreeSpace q N`. -/
def morrisBOnDegree (q N : ℕ) :
    MorrisDegreeSpace q N →ₗ[ℝ] MorrisDegreeSpace q N :=
  (morrisB q).restrict fun _ hP =>
    morrisB_mem_morrisDegreeSubmodule hP

/-- The operator `B_q - A_q`, restricted to `MorrisDegreeSpace q N`. -/
def morrisDOnDegree (q N : ℕ) :
    MorrisDegreeSpace q N →ₗ[ℝ] MorrisDegreeSpace q N :=
  morrisBOnDegree q N - morrisAOnDegree q N

@[simp] theorem coe_morrisAOnDegree (q N : ℕ)
    (P : MorrisDegreeSpace q N) :
    (morrisAOnDegree q N P : MvPolynomial (Fin q) ℝ) = morrisA q P := rfl

@[simp] theorem coe_morrisBOnDegree (q N : ℕ)
    (P : MorrisDegreeSpace q N) :
    (morrisBOnDegree q N P : MvPolynomial (Fin q) ℝ) = morrisB q P := rfl

@[simp] theorem coe_morrisDOnDegree (q N : ℕ)
    (P : MorrisDegreeSpace q N) :
    (morrisDOnDegree q N P : MvPolynomial (Fin q) ℝ) = morrisD q P := by
  rw [morrisDOnDegree, LinearMap.sub_apply, morrisD_apply]
  rfl

private def realCoordinateDiagonalLinearMap {sigma : Type*}
    (gamma : ℕ → ℝ) (i : sigma) :
    MvPolynomial sigma ℝ →ₗ[ℝ] MvPolynomial sigma ℝ where
  toFun := BorceaBranden.realCoordinateDiagonalOperator gamma i
  map_add' P Q := by
    ext m
    simp [BorceaBranden.coeff_realCoordinateDiagonalOperator, mul_add]
  map_smul' r P := by
    ext m
    simp [BorceaBranden.coeff_realCoordinateDiagonalOperator]
    ring

private def coordinateDiagonalList {sigma : Type*}
    (gamma : ℕ → ℝ) (l : List sigma) :
    MvPolynomial sigma ℝ →ₗ[ℝ] MvPolynomial sigma ℝ :=
  l.foldr (fun i T => realCoordinateDiagonalLinearMap gamma i * T) 1

private theorem coeff_coordinateDiagonalList {sigma : Type*}
    (gamma : ℕ → ℝ) (l : List sigma)
    (P : MvPolynomial sigma ℝ) (m : sigma →₀ ℕ) :
    (coordinateDiagonalList gamma l P).coeff m =
      (l.map fun i => gamma (m i)).prod * P.coeff m := by
  induction l with
  | nil => simp [coordinateDiagonalList]
  | cons i l ih =>
      change (realCoordinateDiagonalLinearMap gamma i
        (coordinateDiagonalList gamma l P)).coeff m = _
      rw [show (realCoordinateDiagonalLinearMap gamma i
          (coordinateDiagonalList gamma l P)).coeff m =
        gamma (m i) * (coordinateDiagonalList gamma l P).coeff m by
          exact BorceaBranden.coeff_realCoordinateDiagonalOperator _ _ _ _]
      rw [ih]
      simp only [List.map_cons, List.prod_cons]
      ring

private theorem prod_exp_list {alpha : Type*} (l : List alpha)
    (f : alpha → ℝ) :
    (l.map fun i => Real.exp (f i)).prod = Real.exp (l.map f).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Real.exp_add]

private theorem sum_map_toList {alpha M : Type*}
    [AddCommMonoid M] (s : Finset alpha) (f : alpha → M) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi]

/-- The algebraic flow of `-A_q`, diagonal on monomials. -/
def morrisAFlow (q : ℕ) (t : ℝ) :
    MvPolynomial (Fin q) ℝ →ₗ[ℝ] MvPolynomial (Fin q) ℝ :=
  coordinateDiagonalList (quadraticExponentialMultiplier t)
    Finset.univ.toList

@[simp] theorem coeff_morrisAFlow (q : ℕ) (t : ℝ)
    (P : MvPolynomial (Fin q) ℝ) (m : Fin q →₀ ℕ) :
    (morrisAFlow q t P).coeff m =
      Real.exp (-t * ∑ i : Fin q, m i * (m i - 1)) * P.coeff m := by
  classical
  rw [morrisAFlow, coeff_coordinateDiagonalList]
  simp only [quadraticExponentialMultiplier]
  rw [prod_exp_list]
  congr 2
  rw [sum_map_toList]
  push_cast
  rw [← Finset.mul_sum]

/-- The algebraic flow of `-A_q` preserves real stability. -/
theorem MvRealStable.morrisAFlow {q : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {P : MvPolynomial (Fin q) ℝ} (hP : MvRealStable P) :
    MvRealStable (morrisAFlow q t P) := by
  rw [RealRooted.LiuZhang.morrisAFlow]
  generalize (Finset.univ : Finset (Fin q)).toList = l
  induction l with
  | nil => simpa [coordinateDiagonalList] using hP
  | cons i l ih =>
      simp only [coordinateDiagonalList, List.foldr_cons,
        Module.End.mul_apply]
      apply BorceaBranden.mvRealStable_quadraticExponentialMultiplier ht i
      simpa [coordinateDiagonalList] using ih

private theorem morrisAFlow_monomial (q : ℕ) (t : ℝ)
    (m : Fin q →₀ ℕ) (r : ℝ) :
    morrisAFlow q t (monomial m r) =
      monomial m
        (Real.exp (-t * ∑ i : Fin q, m i * (m i - 1)) * r) := by
  ext d
  by_cases hdm : d = m
  · subst d
    simp [coeff_morrisAFlow, coeff_monomial]
  · simp [coeff_morrisAFlow, coeff_monomial, Ne.symm hdm]

theorem morrisAFlow_msymm {n q : ℕ} (t : ℝ) (mu : n.Partition) :
    morrisAFlow q t (msymm (Fin q) ℝ mu) =
      Real.exp (-t * morrisAWeight mu) • msymm (Fin q) ℝ mu := by
  rw [msymm, map_sum]
  simp_rw [prod_map_X_eq_monomial_toFinsupp, morrisAFlow_monomial]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [show (∑ i : Fin q, s.1.1.toFinsupp i *
      (s.1.1.toFinsupp i - 1)) = morrisAWeight mu by
    rw [sum_toFinsupp_mul_pred_eq_morrisAWeight_ofSym s.1, s.2]]
  simp [MvPolynomial.smul_monomial]

theorem morrisAFlow_mem_morrisDegreeSubmodule {q N : ℕ}
    (t : ℝ) {P : MvPolynomial (Fin q) ℝ}
    (hP : P ∈ morrisDegreeSubmodule q N) :
    morrisAFlow q t P ∈ morrisDegreeSubmodule q N := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      rw [morrisMsymm, morrisAFlow_msymm]
      exact Submodule.smul_mem _ _ (morrisMsymm_mem q N i)
  | zero => simp
  | add P Q _ _ hP hQ =>
      rw [map_add]
      exact Submodule.add_mem _ hP hQ
  | smul r P _ hP =>
      rw [map_smul]
      exact Submodule.smul_mem _ r hP

/-- The flow of `-A_q` at time `t`, restricted to `MorrisDegreeSpace q N`. -/
def morrisAFlowOnDegree (q N : ℕ) (t : ℝ) :
    MorrisDegreeSpace q N →ₗ[ℝ] MorrisDegreeSpace q N :=
  (morrisAFlow q t).restrict fun _ hP =>
    morrisAFlow_mem_morrisDegreeSubmodule t hP

/-- The linear equivalence between `MorrisDegreeSpace q N` and its coordinate space, given by a
chosen basis. -/
noncomputable def morrisDegreeEquiv (q N : ℕ) :
    MorrisDegreeSpace q N ≃ₗ[ℝ]
      Module.Free.ChooseBasisIndex ℝ (MorrisDegreeSpace q N) → ℝ :=
  (Module.Free.chooseBasis ℝ (MorrisDegreeSpace q N)).repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℝ ℝ _

/-- The coordinate space `ℝ ^ k` of `MorrisDegreeSpace q N`, indexed by a chosen basis. -/
abbrev MorrisDegreeCoords (q N : ℕ) :=
  Module.Free.ChooseBasisIndex ℝ (MorrisDegreeSpace q N) → ℝ

/-- The endomorphism of `MorrisDegreeCoords q N` corresponding to an endomorphism `T` of
`MorrisDegreeSpace q N`. -/
def endOnMorrisDegreeCoords (q N : ℕ)
    (T : MorrisDegreeSpace q N →ₗ[ℝ] MorrisDegreeSpace q N) :
    MorrisDegreeCoords q N →ₗ[ℝ] MorrisDegreeCoords q N :=
  morrisDegreeEquiv q N |>.conj T

/-- The operator `A_q` on `MorrisDegreeSpace q N`, written in coordinates. -/
def morrisACoords (q N : ℕ) :
    MorrisDegreeCoords q N →ₗ[ℝ] MorrisDegreeCoords q N :=
  endOnMorrisDegreeCoords q N (morrisAOnDegree q N)

/-- The operator `B_q` on `MorrisDegreeSpace q N`, written in coordinates. -/
def morrisBCoords (q N : ℕ) :
    MorrisDegreeCoords q N →ₗ[ℝ] MorrisDegreeCoords q N :=
  endOnMorrisDegreeCoords q N (morrisBOnDegree q N)

/-- The operator `B_q - A_q` on `MorrisDegreeSpace q N`, written in coordinates. -/
def morrisDCoords (q N : ℕ) :
    MorrisDegreeCoords q N →ₗ[ℝ] MorrisDegreeCoords q N :=
  endOnMorrisDegreeCoords q N (morrisDOnDegree q N)

/-- The flow of `-A_q` at time `t` on `MorrisDegreeSpace q N`, written in coordinates. -/
def morrisAFlowCoords (q N : ℕ) (t : ℝ) :
    MorrisDegreeCoords q N →ₗ[ℝ] MorrisDegreeCoords q N :=
  endOnMorrisDegreeCoords q N (morrisAFlowOnDegree q N t)

/-- The operator `A_q` on `MorrisDegreeCoords q N`, as a continuous linear map. -/
def morrisAContinuous (q N : ℕ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  LinearMap.toContinuousLinearMap (morrisACoords q N)

/-- The operator `B_q` on `MorrisDegreeCoords q N`, as a continuous linear map. -/
def morrisBContinuous (q N : ℕ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  LinearMap.toContinuousLinearMap (morrisBCoords q N)

/-- The operator `B_q - A_q` on `MorrisDegreeCoords q N`, as a continuous linear map. -/
def morrisDContinuous (q N : ℕ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  LinearMap.toContinuousLinearMap (morrisDCoords q N)

/-- The flow of `-A_q` at time `t` on `MorrisDegreeCoords q N`, as a continuous linear map. -/
def morrisAFlowContinuous (q N : ℕ) (t : ℝ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  LinearMap.toContinuousLinearMap (morrisAFlowCoords q N t)

private def morrisMsymmDegree (q N : ℕ)
    (i : MorrisDegreeIndex q N) : MorrisDegreeSpace q N :=
  ⟨morrisMsymm q N i, morrisMsymm_mem q N i⟩

theorem morrisAContinuous_morrisMsymm (q N : ℕ)
    (i : MorrisDegreeIndex q N) :
    morrisAContinuous q N
        (morrisDegreeEquiv q N (morrisMsymmDegree q N i)) =
      (morrisAWeight i.2.1 : ℝ) •
        morrisDegreeEquiv q N (morrisMsymmDegree q N i) := by
  simp only [morrisAContinuous]
  change morrisACoords q N
      (morrisDegreeEquiv q N (morrisMsymmDegree q N i)) = _
  rw [morrisACoords, endOnMorrisDegreeCoords,
    LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply]
  change morrisDegreeEquiv q N (morrisAOnDegree q N
      ((morrisDegreeEquiv q N).symm
        (morrisDegreeEquiv q N (morrisMsymmDegree q N i)))) = _
  rw [(morrisDegreeEquiv q N).symm_apply_apply]
  rw [show morrisAOnDegree q N (morrisMsymmDegree q N i) =
      (morrisAWeight i.2.1 : ℝ) • morrisMsymmDegree q N i by
    apply Subtype.ext
    simpa [morrisMsymmDegree, morrisAOnDegree, morrisMsymm,
      Nat.cast_smul_eq_nsmul] using
        morrisA_msymm (R := ℝ) i.2.1]
  exact map_smul (morrisDegreeEquiv q N) _ _

theorem morrisAFlowContinuous_morrisMsymm (q N : ℕ) (t : ℝ)
    (i : MorrisDegreeIndex q N) :
    morrisAFlowContinuous q N t
        (morrisDegreeEquiv q N (morrisMsymmDegree q N i)) =
      Real.exp (-t * morrisAWeight i.2.1) •
        morrisDegreeEquiv q N (morrisMsymmDegree q N i) := by
  simp only [morrisAFlowContinuous]
  change morrisAFlowCoords q N t
      (morrisDegreeEquiv q N (morrisMsymmDegree q N i)) = _
  rw [morrisAFlowCoords, endOnMorrisDegreeCoords,
    LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply]
  change morrisDegreeEquiv q N (morrisAFlowOnDegree q N t
      ((morrisDegreeEquiv q N).symm
        (morrisDegreeEquiv q N (morrisMsymmDegree q N i)))) = _
  rw [(morrisDegreeEquiv q N).symm_apply_apply]
  rw [show morrisAFlowOnDegree q N t (morrisMsymmDegree q N i) =
      Real.exp (-t * morrisAWeight i.2.1) •
        morrisMsymmDegree q N i by
    apply Subtype.ext
    simpa [morrisAFlowOnDegree, morrisMsymmDegree, morrisMsymm] using
      morrisAFlow_msymm t i.2.1]
  exact map_smul (morrisDegreeEquiv q N) _ _

theorem exp_neg_morrisAContinuous_eq_flow (q N : ℕ) (t : ℝ) :
    NormedSpace.exp ((-t) • morrisAContinuous q N) =
      morrisAFlowContinuous q N t := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨P, rfl⟩ := (morrisDegreeEquiv q N).surjective x
  rcases P with ⟨P, hP⟩
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      let x := morrisDegreeEquiv q N (morrisMsymmDegree q N i)
      have hx : ((-t) • morrisAContinuous q N) x =
          (-t * morrisAWeight i.2.1) • x := by
        rw [smul_apply, morrisAContinuous_morrisMsymm]
        simp only [x, smul_smul]
      change NormedSpace.exp ((-t) • morrisAContinuous q N) x =
        morrisAFlowContinuous q N t x
      rw [exp_apply_of_eigenvector _ _ _ hx]
      exact morrisAFlowContinuous_morrisMsymm q N t i |>.symm
  | zero =>
      change NormedSpace.exp ((-t) • morrisAContinuous q N)
          (morrisDegreeEquiv q N (0 : MorrisDegreeSpace q N)) =
        morrisAFlowContinuous q N t
          (morrisDegreeEquiv q N (0 : MorrisDegreeSpace q N))
      simp
  | add P Q hPm hQm hP hQ =>
      change NormedSpace.exp ((-t) • morrisAContinuous q N)
          (morrisDegreeEquiv q N
            (⟨P, hPm⟩ + ⟨Q, hQm⟩ : MorrisDegreeSpace q N)) =
        morrisAFlowContinuous q N t
          (morrisDegreeEquiv q N
            (⟨P, hPm⟩ + ⟨Q, hQm⟩ : MorrisDegreeSpace q N))
      simp only [map_add]
      rw [hP, hQ]
  | smul r P hPm hP =>
      change NormedSpace.exp ((-t) • morrisAContinuous q N)
          (morrisDegreeEquiv q N (r • ⟨P, hPm⟩ : MorrisDegreeSpace q N)) =
        morrisAFlowContinuous q N t
          (morrisDegreeEquiv q N (r • ⟨P, hPm⟩ : MorrisDegreeSpace q N))
      simp only [map_smul]
      rw [hP]

private theorem isSymmetric_prod_esymm_real (q : ℕ)
    (s : Multiset ℕ) :
    ((s.map (esymm (Fin q) ℝ)).prod).IsSymmetric := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons k s ih =>
      simpa using (esymm_isSymmetric (Fin q) ℝ k).mul ih

private theorem morrisBFlow_prod_esymm (q : ℕ) (t : ℝ)
    (s : Multiset ℕ) (hspos : ∀ k ∈ s, 0 < k)
    (hsq : ∀ k ∈ s, k ≤ q) :
    morrisBFlow q t
        ⟨(s.map (esymm (Fin q) ℝ)).prod,
          isSymmetric_prod_esymm_real q s⟩ =
      Real.exp
          (t * (s.map fun k => k * (2 * q - k - 1)).sum) •
        ⟨(s.map (esymm (Fin q) ℝ)).prod,
          isSymmetric_prod_esymm_real q s⟩ := by
  induction s using Multiset.induction_on with
  | empty =>
      have hone :
          (⟨((0 : Multiset ℕ).map (esymm (Fin q) ℝ)).prod,
            isSymmetric_prod_esymm_real q 0⟩ :
              symmetricSubalgebra (Fin q) ℝ) = 1 := by
        apply Subtype.ext
        simp
      rw [hone, map_one]
      simp
  | @cons k s ih =>
      have hkpos : 0 < k := hspos k (by simp)
      have hkq : k ≤ q := hsq k (by simp)
      have hspos' : ∀ l ∈ s, 0 < l := by
        intro l hl
        exact hspos l (by simp [hl])
      have hsq' : ∀ l ∈ s, l ≤ q := by
        intro l hl
        exact hsq l (by simp [hl])
      let i : Fin q :=
        ⟨k - 1, (Nat.sub_lt hkpos Nat.zero_lt_one).trans_le hkq⟩
      have hi : (i : ℕ) + 1 = k := Nat.sub_add_cancel hkpos
      let ek : symmetricSubalgebra (Fin q) ℝ :=
        ⟨esymm (Fin q) ℝ k, esymm_isSymmetric (Fin q) ℝ k⟩
      let es : symmetricSubalgebra (Fin q) ℝ :=
        ⟨(s.map (esymm (Fin q) ℝ)).prod,
          isSymmetric_prod_esymm_real q s⟩
      have hcons :
          (⟨((k ::ₘ s).map (esymm (Fin q) ℝ)).prod,
            isSymmetric_prod_esymm_real q (k ::ₘ s)⟩ :
              symmetricSubalgebra (Fin q) ℝ) = ek * es := by
        apply Subtype.ext
        simp [ek, es]
      have hek : morrisBFlow q t ek = morrisBScale q t i • ek := by
        apply Subtype.ext
        simpa [ek, hi] using congrArg Subtype.val
          (morrisBFlow_esymm q t i)
      rw [hcons, map_mul, hek, ih hspos' hsq', smul_mul_smul]
      rw [Multiset.map_cons, Multiset.sum_cons, morrisBScale]
      rw [← Real.exp_add]
      congr 2
      rw [← hi]
      push_cast
      ring

theorem morrisBFlow_morrisElementary {n : ℕ} (q : ℕ) (t : ℝ)
    (mu : n.Partition) (hmu : mu.parts.card ≤ q) :
    morrisBFlow q t
        ⟨morrisElementary (R := ℝ) q mu,
          isSymmetric_esymmPart mu.conjugate⟩ =
      Real.exp (t * morrisBWeight q mu.conjugate) •
        ⟨morrisElementary (R := ℝ) q mu,
          isSymmetric_esymmPart mu.conjugate⟩ := by
  simpa only [morrisElementary, esymmPart, morrisBWeight] using
    morrisBFlow_prod_esymm q t mu.conjugate.parts
      (fun k hk => mu.conjugate.parts_pos hk)
      (fun k hk =>
        (mu.le_card_parts_of_mem_conjugate_parts hk).trans hmu)

/-- The inclusion of `MorrisDegreeSpace q N` into the symmetric subalgebra. -/
def morrisDegreeToSymmetric (q N : ℕ) :
    MorrisDegreeSpace q N →ₗ[ℝ] symmetricSubalgebra (Fin q) ℝ where
  toFun P := ⟨P, isSymmetric_of_mem_morrisDegreeSubmodule P.2⟩
  map_add' P Q := by ext; rfl
  map_smul' r P := by ext; rfl

/-- The `B_q` flow at time `t` on `MorrisDegreeSpace q N`, with values in the full polynomial
ring. -/
def morrisBFlowAmbient (q N : ℕ) (t : ℝ) :
    MorrisDegreeSpace q N →ₗ[ℝ] MvPolynomial (Fin q) ℝ where
  toFun P := morrisBFlow q t (morrisDegreeToSymmetric q N P)
  map_add' P Q := by
    exact congrArg Subtype.val
      (map_add (morrisBFlow q t)
        (morrisDegreeToSymmetric q N P)
        (morrisDegreeToSymmetric q N Q))
  map_smul' r P := by
    exact congrArg Subtype.val
      (map_smul (morrisBFlow q t)
        r (morrisDegreeToSymmetric q N P))

private theorem morrisBFlow_mem {q N : ℕ} (t : ℝ)
    {P : MvPolynomial (Fin q) ℝ}
    (hP0 : P ∈ morrisDegreeSubmodule q N) :
    (morrisBFlow q t
      ⟨P, isSymmetric_of_mem_morrisDegreeSubmodule hP0⟩ :
        MvPolynomial (Fin q) ℝ) ∈ morrisDegreeSubmodule q N := by
  rw [morrisDegreeSubmodule_eq_elementary] at hP0 ⊢
  induction hP0 using Submodule.span_induction with
  | mem E hE =>
      obtain ⟨i, rfl⟩ := hE
      change (morrisBFlow q t
        ⟨morrisElementaryPoly q N i,
          isSymmetric_of_mem_morrisDegreeSubmodule
            (morrisElementary_mem_morrisDegreeSubmodule i.2.1 i.2.2
              (Nat.lt_succ_iff.mp i.1.isLt))⟩ :
          MvPolynomial (Fin q) ℝ) ∈ morrisElementarySubmodule q N
      have heigen := morrisBFlow_morrisElementary q t i.2.1 i.2.2
      rw [show (morrisBFlow q t
          ⟨morrisElementaryPoly q N i,
            isSymmetric_of_mem_morrisDegreeSubmodule
              (morrisElementary_mem_morrisDegreeSubmodule i.2.1 i.2.2
                (Nat.lt_succ_iff.mp i.1.isLt))⟩ :
            MvPolynomial (Fin q) ℝ) =
          Real.exp (t * morrisBWeight q i.2.1.conjugate) •
            morrisElementaryPoly q N i by
        exact congrArg Subtype.val heigen]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i))
  | zero =>
      have hzero : (0 : MvPolynomial (Fin q) ℝ) ∈
          morrisDegreeSubmodule q N := Submodule.zero_mem _
      change (morrisBFlow q t
        ⟨0, isSymmetric_of_mem_morrisDegreeSubmodule hzero⟩ :
          MvPolynomial (Fin q) ℝ) ∈ morrisElementarySubmodule q N
      have hz : (⟨0, isSymmetric_of_mem_morrisDegreeSubmodule hzero⟩ :
          symmetricSubalgebra (Fin q) ℝ) = 0 := Subtype.ext rfl
      rw [hz, map_zero]
      exact Submodule.zero_mem _
  | add P Q hPe hQe hP hQ =>
      have hPm : P ∈ morrisDegreeSubmodule q N := by
        rw [morrisDegreeSubmodule_eq_elementary]
        exact hPe
      have hQm : Q ∈ morrisDegreeSubmodule q N := by
        rw [morrisDegreeSubmodule_eq_elementary]
        exact hQe
      have hPQ : P + Q ∈ morrisDegreeSubmodule q N :=
        Submodule.add_mem _ hPm hQm
      change (morrisBFlow q t
        ⟨P + Q, isSymmetric_of_mem_morrisDegreeSubmodule hPQ⟩ :
          MvPolynomial (Fin q) ℝ) ∈ morrisElementarySubmodule q N
      have hadd :
          (⟨P + Q, isSymmetric_of_mem_morrisDegreeSubmodule hPQ⟩ :
              symmetricSubalgebra (Fin q) ℝ) =
            ⟨P, isSymmetric_of_mem_morrisDegreeSubmodule hPm⟩ +
              ⟨Q, isSymmetric_of_mem_morrisDegreeSubmodule hQm⟩ :=
        Subtype.ext rfl
      rw [hadd, map_add]
      exact Submodule.add_mem _ (hP hPm) (hQ hQm)
  | smul r P hPe hP =>
      have hPm : P ∈ morrisDegreeSubmodule q N := by
        rw [morrisDegreeSubmodule_eq_elementary]
        exact hPe
      have hrP : r • P ∈ morrisDegreeSubmodule q N :=
        Submodule.smul_mem _ r hPm
      change (morrisBFlow q t
        ⟨r • P, isSymmetric_of_mem_morrisDegreeSubmodule hrP⟩ :
          MvPolynomial (Fin q) ℝ) ∈ morrisElementarySubmodule q N
      have hsmul :
          (⟨r • P, isSymmetric_of_mem_morrisDegreeSubmodule hrP⟩ :
              symmetricSubalgebra (Fin q) ℝ) =
            r • ⟨P, isSymmetric_of_mem_morrisDegreeSubmodule hPm⟩ :=
        Subtype.ext rfl
      rw [hsmul, map_smul]
      exact Submodule.smul_mem _ r (hP hPm)

theorem morrisBFlowAmbient_mem {q N : ℕ} (t : ℝ)
    (P : MorrisDegreeSpace q N) :
    morrisBFlowAmbient q N t P ∈ morrisDegreeSubmodule q N := by
  simpa [morrisBFlowAmbient, morrisDegreeToSymmetric] using
    morrisBFlow_mem t P.2

/-- The `B_q` flow at time `t`, restricted to `MorrisDegreeSpace q N`. -/
def morrisBFlowOnDegree (q N : ℕ) (t : ℝ) :
    MorrisDegreeSpace q N →ₗ[ℝ] MorrisDegreeSpace q N :=
  (morrisBFlowAmbient q N t).codRestrict
    (morrisDegreeSubmodule q N) (morrisBFlowAmbient_mem t)

/-- The `B_q` flow at time `t` on `MorrisDegreeSpace q N`, written in coordinates. -/
def morrisBFlowCoords (q N : ℕ) (t : ℝ) :
    MorrisDegreeCoords q N →ₗ[ℝ] MorrisDegreeCoords q N :=
  endOnMorrisDegreeCoords q N (morrisBFlowOnDegree q N t)

/-- The `B_q` flow at time `t` on `MorrisDegreeCoords q N`, as a continuous linear map. -/
def morrisBFlowContinuous (q N : ℕ) (t : ℝ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  LinearMap.toContinuousLinearMap (morrisBFlowCoords q N t)

private def morrisElementaryDegree (q N : ℕ)
    (i : MorrisDegreeIndex q N) : MorrisDegreeSpace q N :=
  ⟨morrisElementaryPoly q N i,
    morrisElementary_mem_morrisDegreeSubmodule i.2.1 i.2.2
      (Nat.lt_succ_iff.mp i.1.isLt)⟩

theorem morrisBContinuous_morrisElementary (q N : ℕ)
    (i : MorrisDegreeIndex q N) :
    morrisBContinuous q N
        (morrisDegreeEquiv q N (morrisElementaryDegree q N i)) =
      (morrisBWeight q i.2.1.conjugate : ℝ) •
        morrisDegreeEquiv q N (morrisElementaryDegree q N i) := by
  simp only [morrisBContinuous]
  change morrisBCoords q N
      (morrisDegreeEquiv q N (morrisElementaryDegree q N i)) = _
  rw [morrisBCoords, endOnMorrisDegreeCoords,
    LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply]
  change morrisDegreeEquiv q N (morrisBOnDegree q N
      ((morrisDegreeEquiv q N).symm
        (morrisDegreeEquiv q N (morrisElementaryDegree q N i)))) = _
  rw [(morrisDegreeEquiv q N).symm_apply_apply]
  rw [show morrisBOnDegree q N (morrisElementaryDegree q N i) =
      (morrisBWeight q i.2.1.conjugate : ℝ) •
        morrisElementaryDegree q N i by
    apply Subtype.ext
    simpa [morrisElementaryDegree, morrisElementaryPoly,
      morrisBOnDegree, Nat.cast_smul_eq_nsmul] using
        morrisB_morrisElementary (R := ℝ) q i.2.1 i.2.2]
  exact map_smul (morrisDegreeEquiv q N) _ _

theorem morrisBFlowContinuous_morrisElementary (q N : ℕ)
    (t : ℝ) (i : MorrisDegreeIndex q N) :
    morrisBFlowContinuous q N t
        (morrisDegreeEquiv q N (morrisElementaryDegree q N i)) =
      Real.exp (t * morrisBWeight q i.2.1.conjugate) •
        morrisDegreeEquiv q N (morrisElementaryDegree q N i) := by
  simp only [morrisBFlowContinuous]
  change morrisBFlowCoords q N t
      (morrisDegreeEquiv q N (morrisElementaryDegree q N i)) = _
  rw [morrisBFlowCoords, endOnMorrisDegreeCoords,
    LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply]
  change morrisDegreeEquiv q N (morrisBFlowOnDegree q N t
      ((morrisDegreeEquiv q N).symm
        (morrisDegreeEquiv q N (morrisElementaryDegree q N i)))) = _
  rw [(morrisDegreeEquiv q N).symm_apply_apply]
  rw [show morrisBFlowOnDegree q N t (morrisElementaryDegree q N i) =
      Real.exp (t * morrisBWeight q i.2.1.conjugate) •
        morrisElementaryDegree q N i by
    apply Subtype.ext
    exact congrArg
      (fun P : symmetricSubalgebra (Fin q) ℝ =>
        (P : MvPolynomial (Fin q) ℝ))
      (morrisBFlow_morrisElementary q t i.2.1 i.2.2)]
  exact map_smul (morrisDegreeEquiv q N) _ _

theorem exp_morrisBContinuous_eq_flow (q N : ℕ) (t : ℝ) :
    NormedSpace.exp (t • morrisBContinuous q N) =
      morrisBFlowContinuous q N t := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨P, rfl⟩ := (morrisDegreeEquiv q N).surjective x
  rcases P with ⟨P, hP⟩
  have hPe : P ∈ morrisElementarySubmodule q N := by
    rw [← morrisDegreeSubmodule_eq_elementary]
    exact hP
  revert hP
  induction hPe using Submodule.span_induction with
  | mem P hE =>
      intro hPm
      obtain ⟨i, rfl⟩ := hE
      let x := morrisDegreeEquiv q N (morrisElementaryDegree q N i)
      have hx : (t • morrisBContinuous q N) x =
          (t * morrisBWeight q i.2.1.conjugate) • x := by
        rw [smul_apply, morrisBContinuous_morrisElementary]
        simp only [x, smul_smul]
      change NormedSpace.exp (t • morrisBContinuous q N) x =
        morrisBFlowContinuous q N t x
      rw [exp_apply_of_eigenvector _ _ _ hx]
      exact morrisBFlowContinuous_morrisElementary q N t i |>.symm
  | zero =>
      intro hzero
      change NormedSpace.exp (t • morrisBContinuous q N)
          (morrisDegreeEquiv q N (0 : MorrisDegreeSpace q N)) =
        morrisBFlowContinuous q N t
          (morrisDegreeEquiv q N (0 : MorrisDegreeSpace q N))
      simp
  | add P Q hPm hQm hP hQ =>
      intro hPQ
      have hPm' : P ∈ morrisDegreeSubmodule q N := by
        rw [morrisDegreeSubmodule_eq_elementary]
        exact hPm
      have hQm' : Q ∈ morrisDegreeSubmodule q N := by
        rw [morrisDegreeSubmodule_eq_elementary]
        exact hQm
      change NormedSpace.exp (t • morrisBContinuous q N)
          (morrisDegreeEquiv q N
            (⟨P, hPm'⟩ + ⟨Q, hQm'⟩ :
                MorrisDegreeSpace q N)) =
        morrisBFlowContinuous q N t
          (morrisDegreeEquiv q N
            (⟨P, hPm'⟩ + ⟨Q, hQm'⟩ :
                MorrisDegreeSpace q N))
      simp only [map_add]
      rw [hP hPm', hQ hQm']
  | smul r P hPm hP =>
      intro hrP
      have hPm' : P ∈ morrisDegreeSubmodule q N := by
        rw [morrisDegreeSubmodule_eq_elementary]
        exact hPm
      change NormedSpace.exp (t • morrisBContinuous q N)
          (morrisDegreeEquiv q N
            (r • ⟨P, hPm'⟩ :
              MorrisDegreeSpace q N)) =
        morrisBFlowContinuous q N t
          (morrisDegreeEquiv q N
            (r • ⟨P, hPm'⟩ :
              MorrisDegreeSpace q N))
      simp only [map_smul]
      rw [hP hPm']

/-- The polynomial with coordinate vector `x` in `MorrisDegreeSpace q N`. -/
def morrisDegreePolynomial (q N : ℕ) (x : MorrisDegreeCoords q N) :
    MvPolynomial (Fin q) ℝ :=
  ((morrisDegreeEquiv q N).symm x : MorrisDegreeSpace q N)

@[simp] theorem morrisDegreePolynomial_equiv (q N : ℕ)
    (P : MorrisDegreeSpace q N) :
    morrisDegreePolynomial q N (morrisDegreeEquiv q N P) = P := by
  simp [morrisDegreePolynomial]

theorem morrisDegreePolynomial_morrisAFlow (q N : ℕ) (t : ℝ)
    (x : MorrisDegreeCoords q N) :
    morrisDegreePolynomial q N (morrisAFlowContinuous q N t x) =
      morrisAFlow q t (morrisDegreePolynomial q N x) := by
  obtain ⟨P, rfl⟩ := (morrisDegreeEquiv q N).surjective x
  simp [morrisAFlowContinuous, morrisAFlowCoords,
    endOnMorrisDegreeCoords, LinearEquiv.conj_apply,
    LinearMap.comp_apply, morrisAFlowOnDegree]

theorem morrisDegreePolynomial_morrisBFlow (q N : ℕ) (t : ℝ)
    (x : MorrisDegreeCoords q N) :
    morrisDegreePolynomial q N (morrisBFlowContinuous q N t x) =
      (morrisBFlow q t
        (morrisDegreeToSymmetric q N ((morrisDegreeEquiv q N).symm x)) :
          MvPolynomial (Fin q) ℝ) := by
  obtain ⟨P, rfl⟩ := (morrisDegreeEquiv q N).surjective x
  simp [morrisBFlowContinuous, morrisBFlowCoords,
    endOnMorrisDegreeCoords, LinearEquiv.conj_apply,
    LinearMap.comp_apply, morrisBFlowOnDegree,
    morrisBFlowAmbient]
  rfl

theorem MvRealStable.exp_neg_morrisA {q N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) {x : MorrisDegreeCoords q N}
    (hx : MvRealStable (morrisDegreePolynomial q N x)) :
    MvRealStable (morrisDegreePolynomial q N
      (NormedSpace.exp ((-t) • morrisAContinuous q N) x)) := by
  rw [exp_neg_morrisAContinuous_eq_flow,
    morrisDegreePolynomial_morrisAFlow]
  exact MvRealStable.morrisAFlow ht hx

theorem MvRealStable.exp_morrisB {q N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) {x : MorrisDegreeCoords q N}
    (hx : MvRealStable (morrisDegreePolynomial q N x)) :
    MvRealStable (morrisDegreePolynomial q N
      (NormedSpace.exp (t • morrisBContinuous q N) x)) := by
  rw [exp_morrisBContinuous_eq_flow,
    morrisDegreePolynomial_morrisBFlow]
  exact MvRealStable.morrisBFlow ht hx

theorem morrisDContinuous_eq_sub (q N : ℕ) :
    morrisDContinuous q N =
      morrisBContinuous q N - morrisAContinuous q N := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨P, rfl⟩ := (morrisDegreeEquiv q N).surjective x
  simp [morrisDContinuous, morrisBContinuous, morrisAContinuous,
    morrisDCoords, morrisBCoords, morrisACoords,
    endOnMorrisDegreeCoords, LinearEquiv.conj_apply,
    LinearMap.comp_apply, morrisDOnDegree]

/-- The Lie--Trotter step `exp (t * B_q) * exp (-(t * A_q))` on `MorrisDegreeCoords q N`. -/
def morrisTrotterStep (q N : ℕ) (t : ℝ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  NormedSpace.exp (t • morrisBContinuous q N) *
    NormedSpace.exp (t • (-morrisAContinuous q N))

/-- The `n`-th Lie--Trotter approximation `(morrisTrotterStep (t / (n + 1))) ^ (n + 1)`. -/
def morrisTrotterApprox (q N : ℕ) (t : ℝ) (n : ℕ) :
    MorrisDegreeCoords q N →L[ℝ] MorrisDegreeCoords q N :=
  morrisTrotterStep q N (t / (n + 1 : ℕ)) ^ (n + 1)

private theorem morrisTrotterStep_stable {q N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) {x : MorrisDegreeCoords q N}
    (hx : MvRealStable (morrisDegreePolynomial q N x)) :
    MvRealStable (morrisDegreePolynomial q N
      (morrisTrotterStep q N t x)) := by
  rw [RealRooted.LiuZhang.morrisTrotterStep, mul_apply_eq_comp]
  rw [show t • (-morrisAContinuous q N) =
    (-t) • morrisAContinuous q N by module]
  exact MvRealStable.exp_morrisB ht
    (MvRealStable.exp_neg_morrisA ht hx)

private theorem morrisTrotterStep_pow_stable {q N : ℕ}
    {t : ℝ} (ht : 0 ≤ t) {x : MorrisDegreeCoords q N}
    (hx : MvRealStable (morrisDegreePolynomial q N x)) (k : ℕ) :
    MvRealStable (morrisDegreePolynomial q N
      (((RealRooted.LiuZhang.morrisTrotterStep q N t) ^ k) x)) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact morrisTrotterStep_stable ht ih

theorem MvRealStable.morrisTrotterApprox {q N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) {x : MorrisDegreeCoords q N}
    (hx : MvRealStable (morrisDegreePolynomial q N x)) (n : ℕ) :
    MvRealStable (morrisDegreePolynomial q N
      (RealRooted.LiuZhang.morrisTrotterApprox q N t n x)) := by
  rw [RealRooted.LiuZhang.morrisTrotterApprox]
  exact morrisTrotterStep_pow_stable
    (div_nonneg ht (by positivity)) hx (n + 1)

theorem tendsto_morrisTrotterApprox (q N : ℕ) (t : ℝ)
    (x : MorrisDegreeCoords q N) :
    Filter.Tendsto (fun n => morrisTrotterApprox q N t n x)
      Filter.atTop
      (nhds (NormedSpace.exp (t • morrisDContinuous q N) x)) := by
  have h := ContinuousLinearMap.tendsto_exp_add_trotter_apply
    (morrisBContinuous q N) (-morrisAContinuous q N) t x
  rw [morrisDContinuous_eq_sub]
  simpa [RealRooted.LiuZhang.morrisTrotterApprox,
    RealRooted.LiuZhang.morrisTrotterStep, sub_eq_add_neg] using h

private def morrisCoeff (q N : ℕ) (m : Fin q →₀ ℕ) :
    MorrisDegreeCoords q N →ₗ[ℝ] ℝ where
  toFun x := (morrisDegreePolynomial q N x).coeff m
  map_add' x y := by
    simp [morrisDegreePolynomial]
  map_smul' r x := by
    simp [morrisDegreePolynomial]

private def morrisCoeffContinuous (q N : ℕ) (m : Fin q →₀ ℕ) :
    MorrisDegreeCoords q N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (morrisCoeff q N m)

/-- The polynomial given by applying `exp (t * (B_q - A_q))` to the coordinate vector `x`. -/
def morrisDExp (q N : ℕ) (t : ℝ) (x : MorrisDegreeCoords q N) :
    MvPolynomial (Fin q) ℝ :=
  morrisDegreePolynomial q N
    (NormedSpace.exp (t • morrisDContinuous q N) x)

/-- Liu--Zhang Theorem 4.9 on the explicit finite-dimensional space of
symmetric polynomials of total degree at most `N`. -/
theorem MvRealStable.morrisDExp {q N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {x : MorrisDegreeCoords q N}
    (hx : MvRealStable (morrisDegreePolynomial q N x)) :
    MvRealStable (morrisDExp q N t x) := by
  apply MvRealStable.of_coeff_tendsto_of_totalDegree_le
      (P := fun n => morrisDegreePolynomial q N
        (RealRooted.LiuZhang.morrisTrotterApprox q N t n x)) (N := N)
  · exact MvRealStable.morrisTrotterApprox ht hx
  · intro n
    exact totalDegree_le_of_mem_morrisDegreeSubmodule
      (((morrisDegreeEquiv q N).symm
        (RealRooted.LiuZhang.morrisTrotterApprox q N t n x)).property)
  · exact totalDegree_le_of_mem_morrisDegreeSubmodule
      (((morrisDegreeEquiv q N).symm
        (NormedSpace.exp (t • morrisDContinuous q N) x)).property)
  · intro m
    exact (morrisCoeffContinuous q N m).continuous.tendsto _ |>.comp
      (tendsto_morrisTrotterApprox q N t x)
  · intro hzero
    have hsub : (morrisDegreeEquiv q N).symm
        (NormedSpace.exp (t • morrisDContinuous q N) x) = 0 := by
      apply Subtype.ext
      exact hzero
    have hout : NormedSpace.exp (t • morrisDContinuous q N) x = 0 := by
      apply (morrisDegreeEquiv q N).symm.injective
      simpa using hsub
    have hxzero : x = 0 := by
      apply ContinuousLinearMap.injective_exp
        (t • morrisDContinuous q N)
      simpa using hout
    apply hx.ne_zero
    rw [hxzero]
    simp [morrisDegreePolynomial]

/-- Liu--Zhang Theorem 4.9, stated for a symmetric polynomial together
with an explicit total-degree bound. -/
theorem MvRealStable.morrisDExp_of_symmetric {q N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) {P : MvPolynomial (Fin q) ℝ} (hP : MvRealStable P)
    (hsym : P.IsSymmetric) (hdeg : P.totalDegree ≤ N) :
    MvRealStable (RealRooted.LiuZhang.morrisDExp q N t
      (morrisDegreeEquiv q N
        ⟨P, IsSymmetric.mem_morrisDegreeSubmodule hsym hdeg⟩)) := by
  apply MvRealStable.morrisDExp ht
  simpa using hP

end

end RealRooted.LiuZhang
