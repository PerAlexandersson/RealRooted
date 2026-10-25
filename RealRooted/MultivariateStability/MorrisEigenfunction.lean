module

public import RealRooted.MultivariateStability.MorrisDFlow
public import RealRooted.Mathlib.Analysis.Normed.Operator.TriangularExp
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Extension.Linear
public import Mathlib.LinearAlgebra.Basis.Basic
public import RealRooted.Polarization

/-!
# The Liu--Zhang stable eigenfunction flow

This file proves Liu--Zhang, arXiv:2609.15201v2, Theorem 4.12. It combines
the stable elementary seed, the finite dominance-downset triangular flow,
the strict spectral gap, and bounded-degree coefficient-limit closure.
-/

@[expose] public section

open MvPolynomial Polynomial Filter Topology

namespace RealRooted

noncomputable section

/-- Elementary symmetric polynomials that fit in the ambient variables are
real stable. This is the stability input in Liu--Zhang Lemma 4.4. -/
theorem MvRealStable.esymm {q k : ℕ} (hk : k ≤ q) :
    MvRealStable (esymm (Fin q) ℝ k) := by
  unfold MvRealStable complexifyMv
  have hpow : ∀ z : ℂ, 0 < z.im → (Polynomial.X ^ k : ℂ[X]).eval z ≠ 0 := by
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    exact fun z hz => pow_ne_zero _ fun h => by simp [h] at hz
  have hpolar := mvUpperHalfPlaneStable_polarization
    (p := (Polynomial.X ^ k : ℂ[X])) (by simpa using hk) hpow
  rw [polarization_X_pow hk] at hpolar
  intro z hz hzero
  apply hpolar z hz
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [map_esymm] at hzero
  rw [hzero, mul_zero]

namespace LiuZhang

/-- The elementary product `E_lambda` in Liu--Zhang (4.3) is real stable. -/
theorem MvRealStable.morrisElementary {q N : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    MvRealStable (RealRooted.LiuZhang.morrisElementary
      (R := ℝ) q lambda) := by
  rw [RealRooted.LiuZhang.morrisElementary, esymmPart]
  let s := lambda.conjugate.parts
  have hs : ∀ k ∈ s, k ≤ q := by
    exact fun _ hk => (lambda.le_card_parts_of_mem_conjugate_parts hk).trans hlambda
  change MvRealStable (s.map (esymm (Fin q) ℝ)).prod
  have hprod : ∀ u : Multiset ℕ, (∀ k ∈ u, k ≤ q) →
      MvRealStable (u.map (esymm (Fin q) ℝ)).prod := by
    intro u hu
    induction u using Multiset.induction_on with
    | empty => simpa using (MvRealStable.one (sigma := Fin q))
    | @cons k u ih =>
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact MvRealStable.mul (MvRealStable.esymm (hu k (by simp)))
          (ih fun l hl => hu l (by simp [hl]))
  exact hprod s hs

/-- The coordinates in `MorrisDegreeCoords q N` of the elementary product `E_lambda`. -/
def morrisElementaryPoint {q N : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    MorrisDegreeCoords q N :=
  morrisDegreeEquiv q N
    ⟨morrisElementary (R := ℝ) q lambda,
      morrisElementary_mem_morrisDegreeSubmodule lambda hlambda le_rfl⟩

/-- The normalized flow `exp(-t epsilon_lambda) exp(t D_q) E_lambda`
from Liu--Zhang equation (4.27). -/
def normalizedMorrisDExp {q N : ℕ} (lambda : N.Partition)
    (hlambda : lambda.parts.card ≤ q) (t : ℝ) :
    MvPolynomial (Fin q) ℝ :=
  MvPolynomial.C (Real.exp (-t * morrisEigenvalue q lambda)) *
    morrisDExp q N t (morrisElementaryPoint lambda hlambda)

/-- Every nonnegative-time member of the normalized Morris flow is real
stable. -/
theorem MvRealStable.normalizedMorrisDExp {q N : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    {t : ℝ} (ht : 0 ≤ t) :
    MvRealStable (normalizedMorrisDExp lambda hlambda t) := by
  apply MvRealStable.C_mul
    (MvRealStable.morrisDExp ht
      (x := morrisElementaryPoint lambda hlambda) ?_)
    (Real.exp_ne_zero _)
  rw [morrisElementaryPoint, morrisDegreePolynomial_equiv]
  exact MvRealStable.morrisElementary lambda hlambda

/-- The normalized Morris flow stays within its original total-degree
bound. -/
theorem totalDegree_normalizedMorrisDExp_le {q N : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) (t : ℝ) :
    (normalizedMorrisDExp lambda hlambda t).totalDegree ≤ N := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C]
  simp only [zero_add]
  exact totalDegree_le_of_mem_morrisDegreeSubmodule
    (((morrisDegreeEquiv q N).symm
      (NormedSpace.exp (t • morrisDContinuous q N)
        (morrisElementaryPoint lambda hlambda))).property)

/-- A nonzero coefficientwise limit of the normalized Morris flow is real
stable. This is the closure step in Liu--Zhang Theorem 4.12. -/
theorem MvRealStable.of_normalizedMorrisDExp_tendsto {q N : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    {P : MvPolynomial (Fin q) ℝ} (hPdeg : P.totalDegree ≤ N)
    (hcoeff : ∀ m : Fin q →₀ ℕ,
      Tendsto (fun n : ℕ =>
        (RealRooted.LiuZhang.normalizedMorrisDExp
          lambda hlambda n).coeff m)
        atTop (𝓝 (P.coeff m))) (hP : P ≠ 0) : MvRealStable P :=
  MvRealStable.of_coeff_tendsto_of_totalDegree_le
    (P := fun n : ℕ => RealRooted.LiuZhang.normalizedMorrisDExp lambda hlambda n)
    (N := N)
    (fun _ => MvRealStable.normalizedMorrisDExp lambda hlambda (by positivity))
    (fun n => totalDegree_normalizedMorrisDExp_le lambda hlambda n) hPdeg hcoeff hP

/-- The index type of partitions `μ` of `N` with at most `q` parts that are dominated by
`lambda`. -/
abbrev MorrisDownsetIndex {N : ℕ} (q : ℕ) (lambda : N.Partition) :=
  {mu : N.Partition // mu ≤ lambda ∧ mu.parts.card ≤ q}

noncomputable instance {N : ℕ} (q : ℕ) (lambda : N.Partition) :
    Fintype (MorrisDownsetIndex q lambda) :=
  Fintype.ofFinite _

/-- The monomial symmetric polynomial of the partition underlying a downset index `i`. -/
def morrisDownsetMsymm {N : ℕ} (q : ℕ)
    (lambda : N.Partition) (i : MorrisDownsetIndex q lambda) :
    MvPolynomial (Fin q) ℝ :=
  msymm (Fin q) ℝ i.1

private theorem sum_partition_part_fin {N q : ℕ}
    (mu : N.Partition) (hmu : mu.parts.card ≤ q) :
    ∑ i : Fin q, mu.part i = N := by
  have hp := Nat.Partition.prefixSum_eq_sum_take_sort_parts mu q
  have hlength : (mu.parts.sort (· ≥ ·)).length ≤ q := by
    simpa using hmu
  rw [List.take_of_length_le hlength] at hp
  rw [Fin.sum_univ_eq_sum_range, show ∑ i ∈ Finset.range q, mu.part i =
    mu.prefixSum q from rfl, hp, ← Multiset.sum_coe, Multiset.sort_eq, mu.parts_sum]

theorem morrisDownsetMsymm_linearIndependent {N q : ℕ}
    (lambda : N.Partition) :
    LinearIndependent ℝ (morrisDownsetMsymm q lambda) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let d : Fin q →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun j => i.1.part j)
  have hdApply (j : Fin q) : d j = i.1.part j := by simp [d]
  have hdSum : d.sum (fun _ e => e) = N := by
    rw [Finsupp.sum_fintype d (fun _ e => e) (by simp)]
    simpa only [hdApply] using sum_partition_part_fin i.1 i.2.2
  let s : Sym (Fin q) N :=
    ⟨Finsupp.toMultiset d,
      Finsupp.card_toMultiset d |>.trans hdSum⟩
  have hsCount (j : Fin q) : s.1.count j = i.1.part j := by simp [s, hdApply]
  have hsShape : Nat.Partition.ofSym s = i.1 :=
    ofSym_eq_of_count_eq_part i.1 i.2.2 s hsCount
  have hcoeff (j : MorrisDownsetIndex q lambda) :
      (morrisDownsetMsymm q lambda j).coeff d =
        if i = j then 1 else 0 := by
    rw [morrisDownsetMsymm, coeff_msymm j.1 d hdSum, hsShape]
    congr 1
    exact propext Subtype.coe_inj
  have hc := congrArg (MvPolynomial.lcoeff ℝ d) hg
  simpa only [map_sum, map_smul, map_zero, MvPolynomial.lcoeff_apply,
    hcoeff, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] using hc

/-- The submodule of `MvPolynomial (Fin q) ℝ` spanned by the monomial symmetric
polynomials indexed by partitions dominated by `lambda`. -/
def morrisDownsetSubmodule {N : ℕ} (q : ℕ)
    (lambda : N.Partition) :
    Submodule ℝ (MvPolynomial (Fin q) ℝ) :=
  Submodule.span ℝ (Set.range (morrisDownsetMsymm q lambda))

/-- The space `morrisDownsetSubmodule q lambda`, viewed as a type. -/
abbrev MorrisDownsetSpace {N : ℕ} (q : ℕ)
    (lambda : N.Partition) :=
  morrisDownsetSubmodule q lambda

/-- The basis of `MorrisDownsetSpace q lambda` given by the monomial symmetric polynomials
`morrisDownsetMsymm q lambda`. -/
noncomputable def morrisDownsetBasis {N q : ℕ}
    (lambda : N.Partition) :
    Module.Basis (MorrisDownsetIndex q lambda) ℝ
      (MorrisDownsetSpace q lambda) :=
  Module.Basis.span (morrisDownsetMsymm_linearIndependent lambda)


private theorem coe_morrisDownsetBasis {N q : ℕ}
    (lambda : N.Partition) (i : MorrisDownsetIndex q lambda) :
    ((morrisDownsetBasis lambda i :
      MorrisDownsetSpace q lambda) : MvPolynomial (Fin q) ℝ) =
      msymm (Fin q) ℝ i.1 := by
  change ((Module.Basis.span
    (morrisDownsetMsymm_linearIndependent lambda) i :
      MorrisDownsetSpace q lambda) : MvPolynomial (Fin q) ℝ) = _
  rw [Module.Basis.coe_span_apply]
  rfl

private def morrisDownsetIndexOfLt {N q : ℕ}
    {lambda : N.Partition} (i : MorrisDownsetIndex q lambda)
    (mu : {nu : N.Partition // nu.parts.card ≤ q})
    (hmu : mu < (⟨i.1, i.2.2⟩ :
      {nu : N.Partition // nu.parts.card ≤ q})) :
    MorrisDownsetIndex q lambda :=
  ⟨mu.1, (show mu.1 < i.1 from hmu).le.trans i.2.1, mu.2⟩

private theorem lowerSpan_le_morrisDownset {N q : ℕ}
    {lambda : N.Partition} (i : MorrisDownsetIndex q lambda) :
    LinearMap.lowerSpan (R := ℝ)
        (fun mu : {nu : N.Partition // nu.parts.card ≤ q} =>
          msymm (Fin q) ℝ mu.1)
        (⟨i.1, i.2.2⟩ :
          {nu : N.Partition // nu.parts.card ≤ q}) ≤
      morrisDownsetSubmodule q lambda := by
  apply Submodule.span_le.mpr
  rintro _ ⟨mu, hmu, rfl⟩
  exact Submodule.subset_span
    ⟨morrisDownsetIndexOfLt i mu hmu, rfl⟩

theorem morrisD_mem_morrisDownsetSubmodule {N q : ℕ}
    {lambda : N.Partition} {P : MvPolynomial (Fin q) ℝ}
    (hP : P ∈ morrisDownsetSubmodule q lambda) :
    morrisD q P ∈ morrisDownsetSubmodule q lambda := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      let i' : {mu : N.Partition // mu.parts.card ≤ q} :=
        ⟨i.1, i.2.2⟩
      let b := fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
        msymm (Fin q) ℝ mu.1
      let c := fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
        (morrisEigenvalue q mu.1 : ℝ)
      have htri := morrisD_isTriangularOn_msymm
        (R := ℝ) (N := N) (q := q) i'
      have hlower : LinearMap.lowerSpan (R := ℝ) b i' ≤
          morrisDownsetSubmodule q lambda :=
        lowerSpan_le_morrisDownset i
      have hrem : morrisD q (b i') - c i' • b i' ∈
          morrisDownsetSubmodule q lambda :=
        hlower htri
      have hdiag : c i' • b i' ∈
          morrisDownsetSubmodule q lambda := by
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨i, rfl⟩
      change morrisD q (b i') ∈ morrisDownsetSubmodule q lambda
      simpa only [sub_add_cancel] using
        (morrisDownsetSubmodule q lambda).add_mem hrem hdiag
  | zero => simp
  | add P Q _ _ hP hQ =>
      rw [map_add]
      exact Submodule.add_mem _ hP hQ
  | smul r P _ hP =>
      rw [map_smul]
      exact Submodule.smul_mem _ r hP

/-- The Morris operator restricted to the finite dominance downset of a
partition. -/
def morrisDOnDownset {N : ℕ} (q : ℕ)
    (lambda : N.Partition) :
    MorrisDownsetSpace q lambda →ₗ[ℝ] MorrisDownsetSpace q lambda :=
  (morrisD q).restrict fun _ hP =>
    morrisD_mem_morrisDownsetSubmodule hP

private theorem morrisDOnDownset_isTriangular {N q : ℕ}
    (lambda : N.Partition) :
    (morrisDOnDownset q lambda).IsTriangularOn
      (morrisDownsetBasis lambda)
      (fun i => (morrisEigenvalue q i.1 : ℝ)) := by
  intro i
  let i' : {mu : N.Partition // mu.parts.card ≤ q} :=
    ⟨i.1, i.2.2⟩
  let b := fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
    msymm (Fin q) ℝ mu.1
  have htri := morrisD_isTriangularOn_msymm
    (R := ℝ) (N := N) (q := q) i'
  have hlower : LinearMap.lowerSpan (R := ℝ) b i' ≤
      morrisDownsetSubmodule q lambda :=
    lowerSpan_le_morrisDownset i
  have hlift {x : MvPolynomial (Fin q) ℝ}
      (hx : x ∈ LinearMap.lowerSpan (R := ℝ) b i') :
      (⟨x, hlower hx⟩ : MorrisDownsetSpace q lambda) ∈
        LinearMap.lowerSpan (R := ℝ)
          (morrisDownsetBasis lambda) i := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨mu, hmu, rfl⟩
        let j : MorrisDownsetIndex q lambda :=
          morrisDownsetIndexOfLt i mu hmu
        apply Submodule.subset_span
        refine ⟨j, ?_, ?_⟩
        · change mu.1 < i.1
          exact hmu
        · apply Subtype.ext
          rw [coe_morrisDownsetBasis]
          rfl
    | zero =>
        exact (LinearMap.lowerSpan (R := ℝ)
          (morrisDownsetBasis lambda) i).zero_mem
    | add x y _ _ hx hy =>
        exact
          (LinearMap.lowerSpan (R := ℝ)
            (morrisDownsetBasis lambda) i).add_mem hx hy
    | smul r x _ hx =>
        exact
          (LinearMap.lowerSpan (R := ℝ)
            (morrisDownsetBasis lambda) i).smul_mem r hx
  have hl := hlift htri
  convert hl using 1
  apply Subtype.ext
  change morrisD q
      ((morrisDownsetBasis lambda i :
        MorrisDownsetSpace q lambda) : MvPolynomial (Fin q) ℝ) -
      (morrisEigenvalue q i.1 : ℝ) •
        ((morrisDownsetBasis lambda i :
          MorrisDownsetSpace q lambda) : MvPolynomial (Fin q) ℝ) = _
  rw [coe_morrisDownsetBasis]

private theorem repr_eq_zero_of_mem_lowerSpan {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Preorder ι]
    (b : Module.Basis ι ℝ E) {x : E} {i j : ι}
    (hx : x ∈ LinearMap.lowerSpan (R := ℝ) b i) (hij : i ≤ j) :
    b.repr x j = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, hki, rfl⟩
      rw [Module.Basis.repr_self,
        Finsupp.single_eq_of_ne (ne_of_gt (hki.trans_le hij))]
  | zero => simp
  | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
  | smul r x _ hx => simpa using congrArg (r • ·) hx

private theorem toMatrix_isUpperTriangular_of_isTriangularOn
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis ι ℝ E)
    (T : E →ₗ[ℝ] E) (c : ι → ℝ) (hT : T.IsTriangularOn b c) :
    (LinearMap.toMatrix b b T).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  rw [LinearMap.toMatrix_apply]
  change b.repr (T (b j)) i = 0
  let r := T (b j) - c j • b j
  have hr : r ∈ LinearMap.lowerSpan (R := ℝ) b j := hT j
  have hremCoord : b.repr r i = 0 :=
    repr_eq_zero_of_mem_lowerSpan b hr hji.le
  simpa [r, map_sub, map_smul, Module.Basis.repr_self,
    Finsupp.single_eq_of_ne (ne_of_gt hji)] using hremCoord


/-- The order isomorphism from `Fin (card - 1 + 1)` onto a linear extension of the dominance order
on `MorrisDownsetIndex q lambda`. -/
noncomputable def morrisDownsetFinOrderIso {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) ≃o
      LinearExtension (MorrisDownsetIndex q lambda) := by
  letI : Fintype (LinearExtension (MorrisDownsetIndex q lambda)) :=
    @Fintype.ofEquiv (MorrisDownsetIndex q lambda)
      (LinearExtension (MorrisDownsetIndex q lambda))
      (inferInstance : Fintype (MorrisDownsetIndex q lambda))
      (Equiv.refl _)
  exact (Fin.castOrderIso (Nat.sub_add_cancel
      (Fintype.card_pos_iff.mpr ⟨⟨lambda, le_rfl, hlambda⟩⟩))).trans
    (Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr (Equiv.refl _)))

/-- The underlying equivalence of `morrisDownsetFinOrderIso`, indexing `MorrisDownsetIndex q lambda`
by `Fin (card - 1 + 1)`. -/
noncomputable def morrisDownsetFinEquiv {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) ≃
      MorrisDownsetIndex q lambda :=
  (morrisDownsetFinOrderIso lambda hlambda).toEquiv

/-- The basis `morrisDownsetBasis lambda` of `MorrisDownsetSpace q lambda` reindexed by
`Fin (card - 1 + 1)` along `morrisDownsetFinEquiv`. -/
noncomputable def morrisDownsetFinBasis {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    Module.Basis
      (Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1))
      ℝ (MorrisDownsetSpace q lambda) :=
  (morrisDownsetBasis lambda).reindex
    (morrisDownsetFinEquiv lambda hlambda).symm

/-- The coefficient of `m_lambda` in the dominance-downset monomial basis. -/
noncomputable def morrisDownsetTopCoeff {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    (P : MorrisDownsetSpace q lambda) : ℝ :=
  (morrisDownsetFinBasis lambda hlambda).repr P
    (Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1))

private theorem finEquiv_last {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    morrisDownsetFinEquiv lambda hlambda
        (Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1)) =
      (⟨lambda, le_rfl, hlambda⟩ :
        MorrisDownsetIndex q lambda) := by
  let oldOrder : PartialOrder (MorrisDownsetIndex q lambda) := inferInstance
  let e := morrisDownsetFinOrderIso lambda hlambda
  change e (Fin.last _) =
    @toLinearExtension (MorrisDownsetIndex q lambda) oldOrder
      (⟨lambda, le_rfl, hlambda⟩ : MorrisDownsetIndex q lambda)
  apply le_antisymm
  · exact (@toLinearExtension (MorrisDownsetIndex q lambda) oldOrder).monotone
      (e (Fin.last _)).2.1
  · rw [← e.apply_symm_apply
      (@toLinearExtension (MorrisDownsetIndex q lambda) oldOrder
        (⟨lambda, le_rfl, hlambda⟩ : MorrisDownsetIndex q lambda))]
    exact e.monotone (Fin.le_last _)

private theorem finEquiv_symm_lt {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    {mu nu : MorrisDownsetIndex q lambda} (h : mu < nu) :
    (morrisDownsetFinEquiv lambda hlambda).symm mu <
      (morrisDownsetFinEquiv lambda hlambda).symm nu := by
  let oldOrder : PartialOrder (MorrisDownsetIndex q lambda) := inferInstance
  let e := morrisDownsetFinOrderIso lambda hlambda
  change e.symm (@toLinearExtension (MorrisDownsetIndex q lambda) oldOrder mu) <
    e.symm (@toLinearExtension (MorrisDownsetIndex q lambda) oldOrder nu)
  apply e.symm.lt_iff_lt.mpr
  apply lt_of_le_of_ne
    ((@toLinearExtension (MorrisDownsetIndex q lambda) oldOrder).monotone h.le)
  exact h.ne

private theorem morrisDOnDownset_isTriangular_fin {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    (morrisDOnDownset q lambda).IsTriangularOn
      (morrisDownsetFinBasis lambda hlambda)
      (fun i => (morrisEigenvalue q
        (morrisDownsetFinEquiv lambda hlambda i).1 : ℝ)) := by
  intro i
  let e := morrisDownsetFinEquiv lambda hlambda
  let j : MorrisDownsetIndex q lambda := e i
  have htri := morrisDOnDownset_isTriangular lambda j
  have hlift {x : MorrisDownsetSpace q lambda}
      (hx : x ∈ LinearMap.lowerSpan (R := ℝ)
        (morrisDownsetBasis lambda) j) :
      x ∈ LinearMap.lowerSpan (R := ℝ)
        (morrisDownsetFinBasis lambda hlambda) i := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨k, hkj, rfl⟩
        let l := e.symm k
        apply Submodule.subset_span
        refine ⟨l, ?_, ?_⟩
        · change l < i
          calc
            l < e.symm (e i) := by
              simpa [l, j, e] using finEquiv_symm_lt lambda hlambda hkj
            _ = i := e.symm_apply_apply i
        · rw [morrisDownsetFinBasis, Module.Basis.reindex_apply]
          change morrisDownsetBasis lambda (e l) =
            morrisDownsetBasis lambda k
          rw [show e l = k by exact e.apply_symm_apply k]
    | zero =>
        exact (LinearMap.lowerSpan (R := ℝ)
          (morrisDownsetFinBasis lambda hlambda) i).zero_mem
    | add x y _ _ hx hy =>
        exact (LinearMap.lowerSpan (R := ℝ)
          (morrisDownsetFinBasis lambda hlambda) i).add_mem hx hy
    | smul r x _ hx =>
        exact (LinearMap.lowerSpan (R := ℝ)
          (morrisDownsetFinBasis lambda hlambda) i).smul_mem r hx
  simpa [morrisDownsetFinBasis, j, e] using hlift htri

private theorem morrisElementary_sub_msymm_mem_downsetLower {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    morrisElementary (R := ℝ) q lambda - msymm (Fin q) ℝ lambda ∈
      LinearMap.lowerSpan (R := ℝ) (morrisDownsetMsymm q lambda)
        (⟨lambda, le_rfl, hlambda⟩ : MorrisDownsetIndex q lambda) := by
  rw [morrisElementary,
    esymmPart_conjugate_eq_msymm_add_lower lambda hlambda]
  simp only [add_sub_cancel_left]
  apply Submodule.sum_mem
  intro mu hmu
  apply Submodule.smul_mem
  by_cases hlen : mu.parts.card ≤ q
  · apply Submodule.subset_span
    refine ⟨⟨mu, ?_, hlen⟩, ?_, rfl⟩
    · exact (Nat.Partition.mem_erase_dominanceDownset.mp hmu).le
    · exact Nat.Partition.mem_erase_dominanceDownset.mp hmu
  · have hcard : Fintype.card (Fin q) < mu.parts.card := by
      simpa using Nat.lt_of_not_ge hlen
    rw [msymm_eq_zero_of_card_lt mu hcard]
    exact Submodule.zero_mem _

private theorem morrisElementary_mem_morrisDownsetSubmodule {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    morrisElementary (R := ℝ) q lambda ∈ morrisDownsetSubmodule q lambda := by
  rw [← sub_add_cancel (morrisElementary (R := ℝ) q lambda)
    (msymm (Fin q) ℝ lambda)]
  apply Submodule.add_mem
  · exact Submodule.span_mono (by
      rintro _ ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩)
      (morrisElementary_sub_msymm_mem_downsetLower lambda hlambda)
  · apply Submodule.subset_span
    exact ⟨⟨lambda, le_rfl, hlambda⟩, rfl⟩

private def morrisElementaryDownset {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    MorrisDownsetSpace q lambda :=
  ⟨morrisElementary (R := ℝ) q lambda,
    morrisElementary_mem_morrisDownsetSubmodule lambda hlambda⟩

private theorem morrisElementary_remainder_mem_finLower {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    morrisElementaryDownset lambda hlambda -
        morrisDownsetFinBasis lambda hlambda
          (Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1)) ∈
      LinearMap.lowerSpan (R := ℝ) (morrisDownsetFinBasis lambda hlambda)
        (Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1)) := by
  let top : MorrisDownsetIndex q lambda := ⟨lambda, le_rfl, hlambda⟩
  let e := morrisDownsetFinEquiv lambda hlambda
  have hrem := morrisElementary_sub_msymm_mem_downsetLower lambda hlambda
  have hlift {x : MvPolynomial (Fin q) ℝ}
      (hx : x ∈ LinearMap.lowerSpan (R := ℝ)
        (morrisDownsetMsymm q lambda) top) :
      ∃ y : MorrisDownsetSpace q lambda,
        y ∈ LinearMap.lowerSpan (R := ℝ)
          (morrisDownsetFinBasis lambda hlambda)
            (Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1)) ∧
        (y : MvPolynomial (Fin q) ℝ) = x := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨k, hktop, rfl⟩
        let l := e.symm k
        refine ⟨morrisDownsetFinBasis lambda hlambda l, ?_, ?_⟩
        · apply Submodule.subset_span
          refine ⟨l, ?_, rfl⟩
          have hlt := finEquiv_symm_lt lambda hlambda hktop
          rw [show e.symm top = Fin.last _ by
            apply e.injective
            rw [e.apply_symm_apply, finEquiv_last]] at hlt
          exact hlt
        · rw [morrisDownsetFinBasis, Module.Basis.reindex_apply,
            coe_morrisDownsetBasis]
          exact congrArg (morrisDownsetMsymm q lambda)
            (e.apply_symm_apply k)
    | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
    | add x y _ _ hx hy =>
        obtain ⟨x', hx', hxc⟩ := hx
        obtain ⟨y', hy', hyc⟩ := hy
        exact ⟨x' + y', Submodule.add_mem _ hx' hy', by simp [hxc, hyc]⟩
    | smul r x _ hx =>
        obtain ⟨x', hx', hxc⟩ := hx
        exact ⟨r • x', Submodule.smul_mem _ r hx', by simp [hxc]⟩
  obtain ⟨y, hy, hcy⟩ := hlift hrem
  rw [show morrisElementaryDownset lambda hlambda -
      morrisDownsetFinBasis lambda hlambda (Fin.last _) = y by
    apply Subtype.ext
    simpa [morrisElementaryDownset, morrisDownsetFinBasis,
      Module.Basis.reindex_apply, finEquiv_last, top,
      coe_morrisDownsetBasis] using hcy.symm]
  exact hy

private theorem morrisElementaryDownset_last_repr {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    (morrisDownsetFinBasis lambda hlambda).repr
      (morrisElementaryDownset lambda hlambda)
        (Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1)) = 1 := by
  let b := morrisDownsetFinBasis lambda hlambda
  let i := Fin.last (Fintype.card (MorrisDownsetIndex q lambda) - 1)
  have hrem := morrisElementary_remainder_mem_finLower lambda hlambda
  have hzero : b.repr (morrisElementaryDownset lambda hlambda - b i) i = 0 :=
    repr_eq_zero_of_mem_lowerSpan b hrem le_rfl
  have hsub : b.repr (morrisElementaryDownset lambda hlambda) i - 1 = 0 := by
    simpa [map_sub, Module.Basis.repr_self] using hzero
  linarith

private theorem toMatrix_diag_eq_of_isTriangularOn {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis (Fin (n + 1)) ℝ E)
    (T : E →ₗ[ℝ] E) (c : Fin (n + 1) → ℝ)
    (hT : T.IsTriangularOn b c) (i : Fin (n + 1)) :
    LinearMap.toMatrix b b T i i = c i := by
  rw [LinearMap.toMatrix_apply]
  have hzero : b.repr (T (b i) - c i • b i) i = 0 :=
    repr_eq_zero_of_mem_lowerSpan b (hT i) le_rfl
  have hsub : b.repr (T (b i)) i - c i = 0 := by
    simpa [map_sub, map_smul, Module.Basis.repr_self] using hzero
  linarith

private theorem exp_apply_of_eigenvector {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (x : E) (c : ℝ) (hx : T x = c • x) :
    NormedSpace.exp T x = Real.exp c • x := by
  have hpow : ∀ n : ℕ, (T ^ n) x = c ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx,
          pow_succ, smul_smul]
  have hs : Summable fun n : ℕ => (n.factorial : ℝ)⁻¹ • T ^ n := by
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

private theorem LinearMap.IsTriangularOn.conj_equiv {n : ℕ}
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (b : Module.Basis (Fin (n + 1)) ℝ E)
    (e : E ≃ₗ[ℝ] F) (T : E →ₗ[ℝ] E) (c : Fin (n + 1) → ℝ)
    (hT : T.IsTriangularOn b c) :
    (e.conj T).IsTriangularOn (b.map e) c := by
  intro i
  have hi := hT i
  have hlift {x : E} (hx : x ∈ LinearMap.lowerSpan (R := ℝ) b i) :
      e x ∈ LinearMap.lowerSpan (R := ℝ) (b.map e) i := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨j, hji, rfl⟩
        exact Submodule.subset_span ⟨j, hji, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul r x _ hx => simpa using Submodule.smul_mem _ r hx
  convert hlift hi using 1
  simp [LinearEquiv.conj_apply, LinearMap.comp_apply]

private theorem ContinuousLinearMap.map_exp_apply_of_intertwines
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (T : E →L[ℝ] E) (S : F →L[ℝ] F)
    (J : E →L[ℝ] F) (hJ : ∀ x, J (T x) = S (J x)) (x : E) :
    J (NormedSpace.exp T x) = NormedSpace.exp S (J x) := by
  have hpow : ∀ (n : ℕ) (z : E), J ((T ^ n) z) = (S ^ n) (J z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
        intro z
        rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp,
          ih, hJ]
  rw [NormedSpace.exp_eq_tsum ℝ, NormedSpace.exp_eq_tsum ℝ]
  have hTsum := NormedSpace.expSeries_summable' (𝕂 := ℝ) T
  have hTapply := hTsum.map (ContinuousLinearMap.apply ℝ E x)
    (ContinuousLinearMap.apply ℝ E x).continuous
  change J ((∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) x) =
    (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • S ^ n) (J x)
  have hTeval : (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) x =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • T ^ n) x := by
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ E x).map_tsum hTsum
  have hSeval : (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • S ^ n) (J x) =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • S ^ n) (J x) := by
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ F (J x)).map_tsum
        (NormedSpace.expSeries_summable' (𝕂 := ℝ) S)
  have hJsum : J (∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • T ^ n) x) =
      ∑' n : ℕ, J (((n.factorial : ℝ)⁻¹ • T ^ n) x) := by
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using
      J.map_tsum hTapply
  rw [hTeval, hJsum, hSeval]
  apply tsum_congr
  intro n
  change J ((n.factorial : ℝ)⁻¹ • (T ^ n) x) =
    (n.factorial : ℝ)⁻¹ • (S ^ n) (J x)
  rw [map_smul, hpow]

private theorem morrisDownset_le_degree {N q : ℕ}
    (lambda : N.Partition) :
    morrisDownsetSubmodule q lambda ≤ morrisDegreeSubmodule q N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact msymm_mem_morrisDegreeSubmodule i.1 i.2.2 le_rfl

private def morrisDownsetToDegree {N : ℕ} (q : ℕ)
    (lambda : N.Partition) :
    MorrisDownsetSpace q lambda →ₗ[ℝ] MorrisDegreeSpace q N where
  toFun P := ⟨P, morrisDownset_le_degree lambda P.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def morrisDownsetCoordsToDegree {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    (Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) →ₗ[ℝ]
      MorrisDegreeCoords q N :=
  (morrisDegreeEquiv q N).toLinearMap.comp
    ((morrisDownsetToDegree q lambda).comp
      (morrisDownsetFinBasis lambda hlambda).equivFun.symm.toLinearMap)

private theorem morrisDownsetCoords_intertwines {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) (z :
      Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) :
    morrisDownsetCoordsToDegree lambda hlambda
        ((morrisDownsetFinBasis lambda hlambda).equivFun.conj
          (morrisDOnDownset q lambda) z) =
      morrisDContinuous q N
        (morrisDownsetCoordsToDegree lambda hlambda z) := by
  let e := (morrisDownsetFinBasis lambda hlambda).equivFun
  change morrisDegreeEquiv q N
      (morrisDownsetToDegree q lambda
        (e.symm (e (morrisDOnDownset q lambda (e.symm z))))) =
    morrisDCoords q N (morrisDegreeEquiv q N
      (morrisDownsetToDegree q lambda (e.symm z)))
  rw [e.symm_apply_apply]
  simp only [morrisDCoords, endOnMorrisDegreeCoords,
    LinearEquiv.conj_apply, LinearMap.comp_apply]
  let d := morrisDegreeEquiv q N
  let w := morrisDownsetToDegree q lambda (e.symm z)
  change d (morrisDownsetToDegree q lambda
      (morrisDOnDownset q lambda (e.symm z))) =
    d (morrisDOnDegree q N (d.symm (d w)))
  rw [d.symm_apply_apply]
  congr 1

private theorem morrisDownsetCoords_polynomial {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) (z :
      Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) :
    morrisDegreePolynomial q N
        (morrisDownsetCoordsToDegree lambda hlambda z) =
      ((morrisDownsetFinBasis lambda hlambda).equivFun.symm z :
        MorrisDownsetSpace q lambda) := by
  simp [morrisDownsetCoordsToDegree, morrisDownsetToDegree,
    morrisDegreePolynomial, LinearMap.comp_apply]

private theorem morrisDownsetCoords_elementary {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q) :
    morrisDownsetCoordsToDegree lambda hlambda
        ((morrisDownsetFinBasis lambda hlambda).equivFun
          (morrisElementaryDownset lambda hlambda)) =
      morrisElementaryPoint lambda hlambda := by
  apply (morrisDegreeEquiv q N).symm.injective
  simp [morrisDownsetCoordsToDegree, morrisDownsetToDegree,
    morrisElementaryPoint, morrisElementaryDownset, LinearMap.comp_apply]

private theorem exists_unique_stable_morrisEigenfunction {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    (hadj : ∀ i, i + 1 < q →
      lambda.part i - lambda.part (i + 1) ≤ 1) :
    ∃ P : MorrisDownsetSpace q lambda,
      (morrisD q (P : MvPolynomial (Fin q) ℝ) =
            (morrisEigenvalue q lambda : ℝ) •
              (P : MvPolynomial (Fin q) ℝ) ∧
        morrisDownsetTopCoeff lambda hlambda P = 1) ∧
      MvRealStable (P : MvPolynomial (Fin q) ℝ) ∧
      ∀ Q : MorrisDownsetSpace q lambda,
        (morrisD q (Q : MvPolynomial (Fin q) ℝ) =
              (morrisEigenvalue q lambda : ℝ) •
                (Q : MvPolynomial (Fin q) ℝ) ∧
          morrisDownsetTopCoeff lambda hlambda Q = 1) →
        Q = P := by
  let b := morrisDownsetFinBasis lambda hlambda
  let e := b.equivFun
  let b' := b.map e
  let Tlin := e.conj (morrisDOnDownset q lambda)
  let T : (Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) →L[ℝ]
      (Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap Tlin
  let c : Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ :=
    fun i => morrisEigenvalue q (morrisDownsetFinEquiv lambda hlambda i).1
  have htri := morrisDOnDownset_isTriangular_fin lambda hlambda
  have htri' : Tlin.IsTriangularOn b' c := by
    exact LinearMap.IsTriangularOn.conj_equiv b e
      (morrisDOnDownset q lambda) c htri
  have hupper : (LinearMap.toMatrix b' b' T.toLinearMap).IsUpperTriangular := by
    apply toMatrix_isUpperTriangular_of_isTriangularOn b' T.toLinearMap c
    simpa [T] using htri'
  have hdiag (i : Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1)) :
      LinearMap.toMatrix b' b' T.toLinearMap i i = c i :=
    toMatrix_diag_eq_of_isTriangularOn b' T.toLinearMap c (by
      simpa [T] using htri') i
  have hgap (i : Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1)) :
      LinearMap.toMatrix b' b' T.toLinearMap i.castSucc i.castSucc <
        LinearMap.toMatrix b' b' T.toLinearMap (Fin.last _) (Fin.last _) := by
    rw [hdiag, hdiag]
    have hne : morrisDownsetFinEquiv lambda hlambda i.castSucc ≠
        (⟨lambda, le_rfl, hlambda⟩ : MorrisDownsetIndex q lambda) := by
      intro heq
      have heq' : i.castSucc = Fin.last _ := by
        apply (morrisDownsetFinEquiv lambda hlambda).injective
        simpa [finEquiv_last] using heq
      exact (Fin.castSucc_lt_last i).ne heq'
    have hdom : (morrisDownsetFinEquiv lambda hlambda i.castSucc).1 <
        lambda := lt_of_le_of_ne
          (morrisDownsetFinEquiv lambda hlambda i.castSucc).2.1
          (fun heq => hne (Subtype.ext heq))
    change (morrisEigenvalue q
      (morrisDownsetFinEquiv lambda hlambda i.castSucc).1 : ℝ) <
        (morrisEigenvalue q
          (morrisDownsetFinEquiv lambda hlambda (Fin.last _)).1 : ℝ)
    rw [finEquiv_last lambda hlambda]
    exact_mod_cast morrisEigenvalue_lt_of_lt_of_adjacent_drop
      (morrisDownsetFinEquiv lambda hlambda i.castSucc).2.2
        hlambda hadj hdom
  have htop : LinearMap.toMatrix b' b' T.toLinearMap (Fin.last _) (Fin.last _) =
      (morrisEigenvalue q lambda : ℝ) := by
    rw [hdiag]
    change (morrisEigenvalue q
      (morrisDownsetFinEquiv lambda hlambda (Fin.last _)).1 : ℝ) = _
    rw [finEquiv_last lambda hlambda]
  obtain ⟨y, hyeigen, hynorm, hlim⟩ :=
    ContinuousLinearMap.exists_eigenvector_tendsto_of_isUpperTriangular
      b' T hupper hgap
  rw [htop] at hyeigen hlim
  let P := e.symm y
  let Jlin := morrisDownsetCoordsToDegree lambda hlambda
  let J : (Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) →L[ℝ]
      MorrisDegreeCoords q N := LinearMap.toContinuousLinearMap Jlin
  have hJ (z) : J (T z) = morrisDContinuous q N (J z) := by
    simpa [J, Jlin, T, Tlin, e] using
      morrisDownsetCoords_intertwines lambda hlambda z
  let x := e (morrisElementaryDownset lambda hlambda)
  have hx : b'.repr x (Fin.last _) = 1 := by
    change b'.equivFun x (Fin.last _) = 1
    simpa [b', x, e] using
      morrisElementaryDownset_last_repr lambda hlambda
  have hflow (t : ℝ) :
      morrisDegreePolynomial q N
          (J (Real.exp (-t * morrisEigenvalue q lambda) •
            NormedSpace.exp (t • T) x)) =
        normalizedMorrisDExp lambda hlambda t := by
    rw [map_smul]
    have hexp := ContinuousLinearMap.map_exp_apply_of_intertwines
      (t • T) (t • morrisDContinuous q N) J (fun z => by
        simp only [smul_apply, map_smul]
        exact congrArg (t • ·) (hJ z)) x
    rw [hexp]
    have hseed : J x = morrisElementaryPoint lambda hlambda := by
      simpa [J, Jlin, x, e] using
        morrisDownsetCoords_elementary lambda hlambda
    rw [hseed]
    simp only [normalizedMorrisDExp, morrisDExp,
      morrisDegreePolynomial, map_smul]
    exact MvPolynomial.smul_eq_C_mul _ _
  have hPdeg : (P : MvPolynomial (Fin q) ℝ).totalDegree ≤ N := by
    exact totalDegree_le_of_mem_morrisDegreeSubmodule
      (morrisDownset_le_degree lambda P.property)
  have hPne : (P : MvPolynomial (Fin q) ℝ) ≠ 0 := by
    intro hzero
    have hPzero : P = 0 := Subtype.ext hzero
    have hyzero : y = 0 := by
      apply e.symm.injective
      simpa [P] using hPzero
    subst y
    simp at hynorm
  have hPstable : MvRealStable (P : MvPolynomial (Fin q) ℝ) := by
    apply MvRealStable.of_normalizedMorrisDExp_tendsto
      lambda hlambda hPdeg _ hPne
    intro m
    let Llin :
        (Fin (Fintype.card (MorrisDownsetIndex q lambda) - 1 + 1) → ℝ) →ₗ[ℝ] ℝ :=
      (MvPolynomial.lcoeff ℝ m).comp
        ((morrisDegreeSubmodule q N).subtype.comp
          ((morrisDegreeEquiv q N).symm.toLinearMap.comp Jlin))
    let L := LinearMap.toContinuousLinearMap Llin
    have hreal := (L.continuous.tendsto y).comp (hlim x hx)
    have hreal' : Tendsto (fun t : ℝ =>
        (normalizedMorrisDExp lambda hlambda t).coeff m)
        atTop (𝓝 ((P : MvPolynomial (Fin q) ℝ).coeff m)) := by
      have hlimit : L y = (P : MvPolynomial (Fin q) ℝ).coeff m := by
        change (morrisDegreePolynomial q N
          (morrisDownsetCoordsToDegree lambda hlambda y)).coeff m = _
        rw [morrisDownsetCoords_polynomial lambda hlambda]
      rw [← hlimit]
      apply hreal.congr
      intro t
      change (morrisDegreePolynomial q N
        (J (Real.exp (-t * morrisEigenvalue q lambda) •
          NormedSpace.exp (t • T) x))).coeff m =
        (normalizedMorrisDExp lambda hlambda t).coeff m
      exact congrArg (fun Q : MvPolynomial (Fin q) ℝ => Q.coeff m) (hflow t)
    exact hreal'.comp tendsto_natCast_atTop_atTop
  refine ⟨P, ⟨?_, ?_⟩, hPstable, ?_⟩
  · have hPeigen : morrisDOnDownset q lambda P =
        (morrisEigenvalue q lambda : ℝ) • P := by
      apply e.injective
      simpa [P, T, Tlin, LinearEquiv.conj_apply, LinearMap.comp_apply,
        htop] using hyeigen
    exact congrArg Subtype.val hPeigen
  · have hynorm' : y (Fin.last _) = 1 := by
      change b'.equivFun y (Fin.last _) = 1 at hynorm
      simpa [b', e] using hynorm
    change e (e.symm y) (Fin.last _) = 1
    rw [e.apply_symm_apply]
    exact hynorm'
  · intro Q hQ
    have hQnorm : b'.repr (e Q) (Fin.last _) = 1 := by
      change b'.equivFun (e Q) (Fin.last _) = 1
      simpa [b', e, b, morrisDownsetTopCoeff] using hQ.2
    have hQlim := hlim (e Q) hQnorm
    have hQflow : ∀ t : ℝ,
        Real.exp (-t * morrisEigenvalue q lambda) •
            NormedSpace.exp (t • T) (e Q) = e Q := by
      intro t
      have hQrestrict : morrisDOnDownset q lambda Q =
          (morrisEigenvalue q lambda : ℝ) • Q := by
        apply Subtype.ext
        exact hQ.1
      have hQeigen : T (e Q) =
          (morrisEigenvalue q lambda : ℝ) • e Q := by
        simpa [T, Tlin, e, LinearEquiv.conj_apply,
          LinearMap.comp_apply] using congrArg e hQrestrict
      rw [show NormedSpace.exp (t • T) (e Q) =
          Real.exp (t * morrisEigenvalue q lambda) • e Q by
        apply exp_apply_of_eigenvector
        simpa [smul_apply, smul_smul] using congrArg (t • ·) hQeigen]
      rw [smul_smul, ← Real.exp_add]
      ring_nf
      simp
    have hconst : Tendsto (fun _ : ℝ => e Q) atTop (𝓝 y) :=
      hQlim.congr hQflow
    have heq : e Q = y := tendsto_nhds_unique
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => e Q) atTop (𝓝 (e Q)))
      hconst
    exact e.injective (by simpa [P] using heq)

/-- Liu--Zhang Theorem 4.12, uniqueness part: under the adjacent-drop
condition, there is a unique normalized eigenfunction of `D_q` in the
dominance downset of `lambda`. -/
theorem existsUnique_morrisEigenfunction {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    (hadj : ∀ i, i + 1 < q →
      lambda.part i - lambda.part (i + 1) ≤ 1) :
    ∃! P : MorrisDownsetSpace q lambda,
      morrisD q (P : MvPolynomial (Fin q) ℝ) =
          (morrisEigenvalue q lambda : ℝ) •
            (P : MvPolynomial (Fin q) ℝ) ∧
      morrisDownsetTopCoeff lambda hlambda P = 1 := by
  obtain ⟨P, hP, _, hunique⟩ :=
    exists_unique_stable_morrisEigenfunction lambda hlambda hadj
  exact ⟨P, hP, hunique⟩

/-- Liu--Zhang Theorem 4.12, stability part: every normalized
`lambda`-eigenfunction of `D_q` in the dominance downset is real stable. -/
theorem MvRealStable.morrisEigenfunction {N q : ℕ}
    (lambda : N.Partition) (hlambda : lambda.parts.card ≤ q)
    (hadj : ∀ i, i + 1 < q →
      lambda.part i - lambda.part (i + 1) ≤ 1)
    (P : MorrisDownsetSpace q lambda)
    (hP : morrisD q (P : MvPolynomial (Fin q) ℝ) =
          (morrisEigenvalue q lambda : ℝ) •
            (P : MvPolynomial (Fin q) ℝ) ∧
      morrisDownsetTopCoeff lambda hlambda P = 1) :
    MvRealStable (P : MvPolynomial (Fin q) ℝ) := by
  obtain ⟨Q, _, hQstable, hunique⟩ :=
    exists_unique_stable_morrisEigenfunction lambda hlambda hadj
  rw [hunique P hP]
  exact hQstable

end LiuZhang

end

end RealRooted
