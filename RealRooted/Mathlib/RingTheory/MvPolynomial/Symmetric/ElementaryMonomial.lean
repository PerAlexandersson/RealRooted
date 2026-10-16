module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import RealRooted.Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.Monomial

/-!
# Elementary products in the monomial symmetric basis

This file proves the dominance support bound for the expansion of a
product of elementary symmetric polynomials in the monomial symmetric
basis.
-/

@[expose] public section

namespace MvPolynomial

open Finset Multiset Sym
open AddMonoidAlgebra

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

noncomputable section

/-- The multiplicity of each elementary factor degree, indexed from zero. -/
def esymmColumnMultiplicity (q : ℕ) (s : Multiset ℕ) :
    Fin q →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => s.count (i.val + 1)

@[simp]
theorem esymmColumnMultiplicity_apply (q : ℕ) (s : Multiset ℕ)
    (i : Fin q) :
    esymmColumnMultiplicity q s i = s.count (i.val + 1) := by
  simp [esymmColumnMultiplicity]

private theorem esymmColumnMultiplicity_cons (q k : ℕ)
    (s : Multiset ℕ) (hkpos : 0 < k) (hkq : k ≤ q) :
    esymmColumnMultiplicity q (k ::ₘ s) =
      Finsupp.single ⟨k - 1,
        (Nat.sub_lt hkpos Nat.zero_lt_one).trans_le hkq⟩ 1 +
        esymmColumnMultiplicity q s := by
  ext i
  simp only [esymmColumnMultiplicity_apply, Multiset.count_cons,
    Finsupp.add_apply, Finsupp.single_apply]
  have hindex : (⟨k - 1,
      (Nat.sub_lt hkpos Nat.zero_lt_one).trans_le hkq⟩ : Fin q).val + 1 = k := by
    simp [Nat.sub_add_cancel hkpos]
  by_cases hi : i = ⟨k - 1,
      (Nat.sub_lt hkpos Nat.zero_lt_one).trans_le hkq⟩
  · subst i
    simp [hindex, Nat.add_comm]
  · have hik : k ≠ i.val + 1 := by
      intro h
      apply hi
      apply Fin.ext
      lia
    have hi' : (⟨k - 1,
        (Nat.sub_lt hkpos Nat.zero_lt_one).trans_le hkq⟩ : Fin q) ≠ i :=
      Ne.symm hi
    have hik' : i.val + 1 ≠ k := Ne.symm hik
    simp [hi', hik']

private theorem esymmAlgHomMonomial_esymmColumnMultiplicity
    (q : ℕ) (s : Multiset ℕ)
    (hspos : ∀ k ∈ s, 0 < k) (hsq : ∀ k ∈ s, k ≤ q) :
    esymmAlgHomMonomial (Fin q) (esymmColumnMultiplicity q s) (1 : R) =
      (s.map (esymm (Fin q) R)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      have hz : esymmColumnMultiplicity q 0 = 0 := by
        ext i
        simp
      rw [hz, esymmAlgHom_zero]
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
      rw [esymmColumnMultiplicity_cons q k s hkpos hkq,
        esymmAlgHomMonomial_add,
        esymmAlgHomMonomial_single_one, ih hspos' hsq']
      have hi : i.val + 1 = k := by
        dsimp [i]
        exact Nat.sub_add_cancel hkpos
      simp [i, hi]

private theorem accumulate_esymmColumnMultiplicity
    (q : ℕ) (s : Multiset ℕ)
    (hspos : ∀ k ∈ s, 0 < k) (hsq : ∀ k ∈ s, k ≤ q)
    (j : Fin q) :
    Fin.accumulate q q (esymmColumnMultiplicity q s) j =
      (s.filter (j.val < ·)).card := by
  induction s using Multiset.induction_on with
  | empty => simp [esymmColumnMultiplicity, Fin.accumulate_apply]
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
      rw [esymmColumnMultiplicity_cons q k s hkpos hkq,
        Fin.accumulate_apply]
      simp only [Finsupp.add_apply, Finset.sum_add_distrib]
      have ih' := ih hspos' hsq'
      rw [Fin.accumulate_apply] at ih'
      rw [ih', Multiset.filter_cons]
      by_cases hjk : j.val < k
      · rw [ite_eq_left hjk, Multiset.card_add,
          Multiset.card_singleton]
        have hji : j ≤ i := by
          rw [Fin.le_def]
          lia
        have hsum : ∑ x with j ≤ x,
            (Finsupp.single i 1 : Fin q →₀ ℕ) x = 1 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro x _ hxi
            simp [Ne.symm hxi]
          · simp [hji]
        simpa [i] using congrArg
          (fun z => z + (s.filter (j.val < ·)).card) hsum
      · rw [ite_eq_right hjk]
        have hij : ¬j ≤ i := by
          rw [Fin.le_def]
          lia
        have hsum : ∑ x with j ≤ x,
            (Finsupp.single i 1 : Fin q →₀ ℕ) x = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hjx : j ≤ x := (Finset.mem_filter.mp hx).2
          simp only [Finsupp.single_apply]
          split
          · rename_i hix
            subst x
            exact (hij hjx).elim
          · rfl
        simpa [i] using congrArg
          (fun z => z + (s.filter (j.val < ·)).card) hsum

private theorem accumulate_esymmColumnMultiplicity_conjugate_parts
    {n q : ℕ} (lambda : n.Partition)
    (hlambda : lambda.parts.card ≤ q) (j : Fin q) :
    Fin.accumulate q q
        (esymmColumnMultiplicity q lambda.conjugate.parts) j =
      lambda.part j := by
  calc
    Fin.accumulate q q
        (esymmColumnMultiplicity q lambda.conjugate.parts) j =
        (lambda.conjugate.parts.filter (j.val < ·)).card := by
      apply accumulate_esymmColumnMultiplicity
      · exact fun k hk => lambda.conjugate.parts_pos hk
      · intro k hk
        exact (lambda.le_card_parts_of_mem_conjugate_parts hk).trans hlambda
    _ = lambda.part j := by
      have h := Nat.Partition.conjugate_part_eq_card_filter_gt
        lambda.conjugate j
      simpa using h.symm

private def esymmList (cs : List ℕ) : MvPolynomial σ R :=
  (cs.map (esymm σ R)).prod

private theorem isHomogeneous_esymmList (cs : List ℕ) :
    IsHomogeneous (esymmList (R := R) (σ := σ) cs) cs.sum := by
  induction cs with
  | nil =>
      simpa [esymmList] using (isHomogeneous_one (σ := σ) (R := R))
  | cons c cs ih =>
      simpa [esymmList] using (isHomogeneous_esymm c).mul ih

private theorem degreeOf_esymm_le_one [Nontrivial R]
    (i : σ) (n : ℕ) : degreeOf i (esymm σ R n) ≤ 1 := by
  classical
  rw [degreeOf_le_iff]
  intro d hd
  rw [support_esymm] at hd
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
  by_cases hi : i ∈ t
  · simp [Finsupp.single_apply, hi]
  · simp [Finsupp.single_apply, hi]

private theorem degreeOf_esymmList_le_length [Nontrivial R]
    (i : σ) (cs : List ℕ) :
    degreeOf i (esymmList (R := R) (σ := σ) cs) ≤ cs.length := by
  classical
  induction cs with
  | nil => simp [esymmList]
  | cons c cs ih =>
      apply (degreeOf_mul_le i (esymm σ R c)
        (esymmList (R := R) (σ := σ) cs)).trans
      simpa [esymmList, Nat.add_comm] using Nat.add_le_add
        (degreeOf_esymm_le_one (R := R) i c) ih

private theorem take_sum_le_sum_min_of_mem_support_esymmList
    [Nontrivial R] (cs : List ℕ) (d : σ →₀ ℕ)
    (hd : d ∈ (esymmList (R := R) (σ := σ) cs).support)
    (k : ℕ) :
    (cs.take k).sum ≤ ∑ i : σ, min k (d i) := by
  classical
  have hprod : esymmList (R := R) (σ := σ) cs =
      esymmList (R := R) (σ := σ) (cs.take k) *
        esymmList (R := R) (σ := σ) (cs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k cs]
    simp [esymmList]
  rw [hprod] at hd
  have hsum := MvPolynomial.support_mul
    (esymmList (R := R) (σ := σ) (cs.take k))
    (esymmList (R := R) (σ := σ) (cs.drop k)) hd
  obtain ⟨a, ha, b, _, hab⟩ := Finset.mem_add.mp hsum
  have hab' : d = a + b := hab.symm
  have haBound (i : σ) : a i ≤ k := by
    calc
      a i ≤ degreeOf i
          (esymmList (R := R) (σ := σ) (cs.take k)) :=
        monomial_le_degreeOf i ha
      _ ≤ (cs.take k).length := degreeOf_esymmList_le_length i _
      _ ≤ k := List.length_take_le k cs
  have had (i : σ) : a i ≤ d i := by
    rw [hab']
    simp
  have haDegree : a.sum (fun _ e => e) = (cs.take k).sum := by
    have hhom := isHomogeneous_esymmList
      (R := R) (σ := σ) (cs.take k)
    have hdegree := hhom (mem_support_iff.mp ha)
    rw [Finsupp.weight_apply] at hdegree
    simpa using hdegree
  calc
    (cs.take k).sum = a.sum (fun _ e => e) := haDegree.symm
    _ = ∑ i : σ, a i := Finsupp.sum_fintype _ _ (by simp)
    _ ≤ ∑ i : σ, min k (d i) := by
      apply Finset.sum_le_sum
      intro i _
      exact le_min (haBound i) (had i)

private theorem esymmPart_eq_esymmList_sort_parts {N : ℕ}
    (mu : N.Partition) :
    esymmPart σ R mu =
      esymmList (R := R) (σ := σ) (mu.parts.sort (· ≥ ·)) := by
  rw [esymmPart, esymmList, ← Multiset.prod_coe,
    ← Multiset.map_coe, Multiset.sort_eq]

/-- Every monomial in `esymmPart mu.conjugate` has partition shape
dominated by `mu`. -/
theorem ofSym_le_of_mem_support_esymmPart {N : ℕ}
    [Nontrivial R] [DecidableEq σ] (mu : N.Partition) (s : Sym σ N)
    (hs : s.1.toFinsupp ∈ (esymmPart σ R mu.conjugate).support) :
    Nat.Partition.ofSym s ≤ mu := by
  classical
  rw [← Nat.Partition.conjugate_le_conjugate_iff]
  intro k
  rw [Nat.Partition.prefixSum_eq_sum_take_sort_parts,
    conjugate_prefixSum_ofSym_eq_sum_min]
  apply take_sum_le_sum_min_of_mem_support_esymmList
    (R := R) (cs := mu.conjugate.parts.sort (· ≥ ·))
      (d := s.1.toFinsupp)
  rw [← esymmPart_eq_esymmList_sort_parts]
  exact hs

private theorem isSymmetric_prod_esymm (s : Multiset ℕ) :
    ((s.map (esymm σ R)).prod).IsSymmetric := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons k s ih =>
      simpa using (esymm_isSymmetric σ R k).mul ih

/-- A product of elementary symmetric polynomials is symmetric. -/
theorem isSymmetric_esymmPart {N : ℕ} (mu : N.Partition) :
    (esymmPart σ R mu).IsSymmetric := by
  simpa only [esymmPart] using
    isSymmetric_prod_esymm (R := R) (σ := σ) mu.parts

private theorem isHomogeneous_prod_esymm (s : Multiset ℕ) :
    IsHomogeneous (s.map (esymm σ R)).prod s.sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa using (isHomogeneous_one (σ := σ) (R := R))
  | @cons k s ih =>
      simpa using (isHomogeneous_esymm k).mul ih

/-- The elementary product indexed by a partition is homogeneous of the
size of the partition. -/
theorem isHomogeneous_esymmPart {N : ℕ} (mu : N.Partition) :
    IsHomogeneous (esymmPart σ R mu) N := by
  simpa only [esymmPart, mu.parts_sum] using
    isHomogeneous_prod_esymm (R := R) (σ := σ) mu.parts

/-- The coefficient of the diagonal monomial-symmetric term in the
elementary product is one, provided the partition fits in the variables. -/
theorem msymmCoeff_esymmPart_conjugate_self
    [Nontrivial R] {n q : ℕ} (lambda : n.Partition)
    (hlambda : lambda.parts.card ≤ q) :
    msymmCoeff (esymmPart (Fin q) R lambda.conjugate) lambda = 1 := by
  let t := esymmColumnMultiplicity q lambda.conjugate.parts
  let E := esymmPart (Fin q) R lambda.conjugate
  have hprod : esymmAlgHomMonomial (Fin q) t (1 : R) = E := by
    apply esymmAlgHomMonomial_esymmColumnMultiplicity
    · exact fun k hk => lambda.conjugate.parts_pos hk
    · intro k hk
      exact (lambda.le_card_parts_of_mem_conjugate_parts hk).trans hlambda
  have hlead : leadingCoeff toLex E = 1 := by
    rw [← hprod]
    exact leadingCoeff_esymmAlgHomMonomial t le_rfl
  let d : Fin q →₀ ℕ := ofLex (supDegree toLex E)
  have hdeg : ∀ i : Fin q, d i = lambda.part i := by
    have hd := supDegree_esymmAlgHomMonomial
      (m := q) (n := q) (r := (1 : R)) one_ne_zero t le_rfl
    rw [hprod] at hd
    intro i
    change (ofLex (supDegree toLex E)) i = lambda.part i
    exact congrFun hd i |>.trans
      (accumulate_esymmColumnMultiplicity_conjugate_parts
        lambda hlambda i)
  have hsumPart : ∑ i : Fin q, lambda.part i = n := by
    have hp := Nat.Partition.prefixSum_eq_sum_take_sort_parts lambda q
    have hlength : (lambda.parts.sort (· ≥ ·)).length ≤ q := by
      simpa using hlambda
    rw [List.take_of_length_le hlength] at hp
    calc
      ∑ i : Fin q, lambda.part i =
          ∑ i ∈ Finset.range q, lambda.part i :=
        Fin.sum_univ_eq_sum_range (fun i => lambda.part i) q
      _ = lambda.prefixSum q := rfl
      _ = (lambda.parts.sort (· ≥ ·)).sum := hp
      _ = n := by
        rw [← Multiset.sum_coe, Multiset.sort_eq, lambda.parts_sum]
  have hdSum : d.sum (fun _ e => e) = n := by
    rw [Finsupp.sum_fintype d (fun _ e => e) (by simp)]
    calc
      ∑ i : Fin q, d i = ∑ i : Fin q, lambda.part i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdeg]
      _ = n := hsumPart
  let s : Sym (Fin q) n :=
    ⟨Finsupp.toMultiset d,
      Finsupp.card_toMultiset d |>.trans hdSum⟩
  have hsCount (i : Fin q) : s.1.count i = lambda.part i := by
    change (Finsupp.toMultiset d).count i = lambda.part i
    rw [Finsupp.count_toMultiset, hdeg]
  have hsShape : Nat.Partition.ofSym s = lambda :=
    ofSym_eq_of_count_eq_part lambda hlambda s hsCount
  have hcoeff := msymmCoeff_eq_coeff
    (isSymmetric_esymmPart (R := R) (σ := Fin q) lambda.conjugate) s
  rw [hsShape] at hcoeff
  calc
    msymmCoeff E lambda = E.coeff s.1.toFinsupp := hcoeff
    _ = E.coeff d := by
      rw [show s.1.toFinsupp = d by
        simp [s]]
    _ = leadingCoeff toLex E := by
      rw [leadingCoeff_toLex]
    _ = 1 := hlead

/-- The monomial-symmetric coefficient of an elementary product vanishes
outside its dominance downset. -/
theorem msymmCoeff_esymmPart_conjugate_eq_zero_of_not_le
    [Nontrivial R] [DecidableEq σ] {N : ℕ}
    {mu lambda : N.Partition} (hmu : ¬mu ≤ lambda) :
    msymmCoeff (esymmPart σ R lambda.conjugate) mu = 0 := by
  rw [msymmCoeff]
  split
  case isFalse => rfl
  case isTrue h =>
    let s : Sym σ N := (Classical.choice h).1
    have hs : Nat.Partition.ofSym s = mu := (Classical.choice h).2
    by_contra hcoeff
    have hsupp : s.1.toFinsupp ∈
        (esymmPart σ R lambda.conjugate).support :=
      mem_support_iff.mpr hcoeff
    exact hmu (hs ▸ ofSym_le_of_mem_support_esymmPart lambda s hsupp)

/-- The elementary product only involves monomial symmetric polynomials
whose indices are dominated by its partition index. -/
theorem esymmPart_conjugate_eq_sum_msymm_downset
    [Nontrivial R] [DecidableEq σ] {N : ℕ} (lambda : N.Partition) :
    esymmPart σ R lambda.conjugate =
      ∑ mu ∈ Nat.Partition.dominanceDownset lambda,
        msymmCoeff (esymmPart σ R lambda.conjugate) mu •
          msymm σ R mu := by
  have hhom : IsHomogeneous
      (esymmPart σ R lambda.conjugate) N := by
    simpa using isHomogeneous_esymmPart
      (R := R) (σ := σ) lambda.conjugate
  calc
    esymmPart σ R lambda.conjugate =
        ∑ mu : N.Partition,
          msymmCoeff (esymmPart σ R lambda.conjugate) mu •
            msymm σ R mu :=
      eq_sum_msymm (isSymmetric_esymmPart lambda.conjugate) hhom
    _ = ∑ mu ∈ Nat.Partition.dominanceDownset lambda,
          msymmCoeff (esymmPart σ R lambda.conjugate) mu •
            msymm σ R mu := by
      symm
      apply Finset.sum_subset
        (Nat.Partition.dominanceDownset lambda).subset_univ
      intro mu _ hmu
      rw [Nat.Partition.mem_dominanceDownset] at hmu
      rw [msymmCoeff_esymmPart_conjugate_eq_zero_of_not_le hmu,
        zero_smul]

/-- The elementary product has a unitriangular expansion in monomial
symmetric polynomials under dominance order.  This is equation (4.3) and
the triangular expansion following it in Liu--Zhang,
arXiv:2609.15201v2. -/
theorem esymmPart_conjugate_eq_msymm_add_lower
    [Nontrivial R] {N q : ℕ} (lambda : N.Partition)
    (hlambda : lambda.parts.card ≤ q) :
    esymmPart (Fin q) R lambda.conjugate =
      msymm (Fin q) R lambda +
        ∑ mu ∈ (Nat.Partition.dominanceDownset lambda).erase lambda,
          msymmCoeff (esymmPart (Fin q) R lambda.conjugate) mu •
            msymm (Fin q) R mu := by
  let f := fun mu : N.Partition =>
    msymmCoeff (esymmPart (Fin q) R lambda.conjugate) mu •
      msymm (Fin q) R mu
  have hlmem : lambda ∈ Nat.Partition.dominanceDownset lambda := by
    simp
  calc
    esymmPart (Fin q) R lambda.conjugate =
        ∑ mu ∈ Nat.Partition.dominanceDownset lambda, f mu := by
      exact esymmPart_conjugate_eq_sum_msymm_downset lambda
    _ = f lambda +
        ∑ mu ∈ (Nat.Partition.dominanceDownset lambda).erase lambda,
          f mu := by
      exact (Finset.add_sum_erase _ f hlmem).symm
    _ = msymm (Fin q) R lambda +
        ∑ mu ∈ (Nat.Partition.dominanceDownset lambda).erase lambda,
          f mu := by
      change
        msymmCoeff (esymmPart (Fin q) R lambda.conjugate) lambda •
            msymm (Fin q) R lambda + _ = _
      rw [msymmCoeff_esymmPart_conjugate_self lambda hlambda,
        one_smul]

/-- Partitions strictly below `lambda` that still fit in `q` variables. -/
def strictDominanceDownset (q : ℕ) {N : ℕ}
    (lambda : N.Partition) : Finset N.Partition :=
  ((Nat.Partition.dominanceDownset lambda).erase lambda).filter
    fun mu => mu.parts.card ≤ q

@[simp]
theorem mem_strictDominanceDownset {q N : ℕ}
    {mu lambda : N.Partition} :
    mu ∈ strictDominanceDownset q lambda ↔
      mu < lambda ∧ mu.parts.card ≤ q := by
  classical
  simp only [strictDominanceDownset, Finset.mem_filter,
    Nat.Partition.mem_erase_dominanceDownset]

private theorem elementarySpan_mono {K : Type*} [CommRing K]
    {N q : ℕ} {mu lambda : N.Partition} (hmu : mu < lambda) :
    Submodule.span K
        ((fun eta => esymmPart (Fin q) K eta.conjugate) ''
          (strictDominanceDownset q mu : Set N.Partition)) ≤
      Submodule.span K
        ((fun eta => esymmPart (Fin q) K eta.conjugate) ''
          (strictDominanceDownset q lambda : Set N.Partition)) := by
  apply Submodule.span_mono
  rintro _ ⟨eta, heta, rfl⟩
  refine ⟨eta, ?_, rfl⟩
  change eta ∈ strictDominanceDownset q mu at heta
  change eta ∈ strictDominanceDownset q lambda
  rw [mem_strictDominanceDownset] at heta ⊢
  exact ⟨heta.1.trans hmu, heta.2⟩

/-- The inverse triangular remainder belongs to the span of strictly
lower elementary products. -/
theorem msymm_sub_esymmPart_conjugate_mem_span_lower
    {K : Type*} [CommRing K] [Nontrivial K] {N q : ℕ}
    (lambda : N.Partition)
    (hlambda : lambda.parts.card ≤ q) :
    msymm (Fin q) K lambda - esymmPart (Fin q) K lambda.conjugate ∈
      Submodule.span K
        ((fun mu => esymmPart (Fin q) K mu.conjugate) ''
          (strictDominanceDownset q lambda : Set N.Partition)) := by
  induction lambda using WellFoundedLT.induction with
  | ind lambda ih =>
      let S := strictDominanceDownset q lambda
      let V := Submodule.span K
        ((fun mu => esymmPart (Fin q) K mu.conjugate) ''
          (S : Set N.Partition))
      let a := fun mu : N.Partition =>
        msymmCoeff (esymmPart (Fin q) K lambda.conjugate) mu
      have hforward := esymmPart_conjugate_eq_msymm_add_lower
        (R := K) lambda hlambda
      have hmu_mem (mu : N.Partition)
          (hmu : mu ∈ (Nat.Partition.dominanceDownset lambda).erase lambda) :
          msymm (Fin q) K mu ∈ V := by
        have hmulambda : mu < lambda :=
          Nat.Partition.mem_erase_dominanceDownset.mp hmu
        by_cases hlen : mu.parts.card ≤ q
        · have hrem := ih mu hmulambda hlen
          have hpromote :
              msymm (Fin q) K mu -
                  esymmPart (Fin q) K mu.conjugate ∈ V :=
            elementarySpan_mono (K := K) (q := q) hmulambda hrem
          have hgen : esymmPart (Fin q) K mu.conjugate ∈ V := by
            apply Submodule.subset_span
            refine ⟨mu, ?_, rfl⟩
            change mu ∈ S
            simp [S, hmulambda, hlen]
          simpa only [sub_add_cancel] using V.add_mem hpromote hgen
        · have hcard : Fintype.card (Fin q) < mu.parts.card := by
            simpa using Nat.lt_of_not_ge hlen
          rw [msymm_eq_zero_of_card_lt mu hcard]
          exact V.zero_mem
      have hsum :
          ∑ mu ∈ (Nat.Partition.dominanceDownset lambda).erase lambda,
              a mu • msymm (Fin q) K mu ∈ V := by
        apply Submodule.sum_mem
        intro mu hmu
        exact V.smul_mem (a mu) (hmu_mem mu hmu)
      have hneg : -∑ mu ∈
          (Nat.Partition.dominanceDownset lambda).erase lambda,
            a mu • msymm (Fin q) K mu ∈ V := V.neg_mem hsum
      convert hneg using 1
      rw [hforward]
      dsimp only [a]
      abel

/-- Inverse unitriangular expansion on the finite dominance downset. -/
theorem msymm_eq_esymmPart_conjugate_add_lower
    {K : Type*} [CommRing K] [Nontrivial K] {N q : ℕ}
    (lambda : N.Partition)
    (hlambda : lambda.parts.card ≤ q) :
    ∃ b : N.Partition → K,
      msymm (Fin q) K lambda =
        esymmPart (Fin q) K lambda.conjugate +
          ∑ mu ∈ strictDominanceDownset q lambda,
            b mu • esymmPart (Fin q) K mu.conjugate := by
  have hmem := msymm_sub_esymmPart_conjugate_mem_span_lower
    (K := K) lambda hlambda
  rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_⟩
  rw [hb]
  abel

end

end MvPolynomial
