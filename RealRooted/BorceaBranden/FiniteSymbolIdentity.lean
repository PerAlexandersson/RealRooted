import RealRooted.BorceaBranden.FiniteSymbolBasis
import RealRooted.BorceaBranden.FiniteSymbolLinearity
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
import RealRooted.MultiaffineReciprocal

/-!
# The finite-symbol coefficient identity

This module proves the coefficient identity in Borcea--Branden,
arXiv:0809.0401, Lemma 2.2, for coordinate-wise degree-one boxes.  It expands
the input and output in their squarefree monomial bases, applies the signed
reciprocal and the negative differential action term by term, and uses the
zero-boundary Kronecker calculation to reconstruct the value of the operator.
-/

namespace RealRooted.BorceaBranden

noncomputable section

open BigOperators
open MvPolynomial

private def sumInlEmbedding (sigma tau : Type*) : sigma ↪ Sum sigma tau :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def sumInrEmbedding (sigma tau : Type*) : tau ↪ Sum sigma tau :=
  ⟨Sum.inr, Sum.inr_injective⟩

private theorem indicator_totalDegree
    {sigma : Type*} [DecidableEq sigma] (s : Finset sigma) :
    (Finsupp.indicator s (fun _ _ => 1)).sum (fun _ n => n) = s.card := by
  rw [Finsupp.sum_indicator_index (fun _ => 1) (by simp)]
  simp

private theorem boxChoose_one
    {sigma : Type*} [Fintype sigma]
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    boxChoose (fun _ : sigma => 1) m.1 = 1 := by
  unfold boxChoose
  apply Finset.prod_eq_one
  intro i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (m.2 i) with hzero | hone
  · simp [hzero]
  · simp [hone]

private theorem mapDomain_indicator_sumInl
    {sigma tau : Type*} [DecidableEq sigma] [DecidableEq tau]
    (s : Finset sigma) :
    (Finsupp.indicator s (fun _ _ => 1)).mapDomain
        (Sum.inl : sigma → Sum sigma tau) =
      Finsupp.indicator
        (s.map (sumInlEmbedding sigma tau)) (fun _ _ => 1) := by
  ext x
  cases x with
  | inl i =>
      rw [Finsupp.mapDomain_apply Sum.inl_injective]
      simp [sumInlEmbedding]
  | inr j =>
      rw [Finsupp.mapDomain_notin_range _ _ (by simp)]
      simp [sumInlEmbedding]

private theorem mapDomain_indicator_sumInr
    {sigma tau : Type*} [DecidableEq sigma] [DecidableEq tau]
    (s : Finset tau) :
    (Finsupp.indicator s (fun _ _ => 1)).mapDomain
        (Sum.inr : tau → Sum sigma tau) =
      Finsupp.indicator
        (s.map (sumInrEmbedding sigma tau)) (fun _ _ => 1) := by
  ext x
  cases x with
  | inl i =>
      rw [Finsupp.mapDomain_notin_range _ _ (by simp)]
      simp [sumInrEmbedding]
  | inr j =>
      rw [Finsupp.mapDomain_apply Sum.inr_injective]
      simp [sumInrEmbedding]

private theorem indicator_disjoint_union
    {sigma tau : Type*} [DecidableEq sigma] [DecidableEq tau]
    (s : Finset sigma) (t : Finset tau) :
    Finsupp.indicator (s.map (sumInlEmbedding sigma tau)) (fun _ _ => 1) +
        Finsupp.indicator (t.map (sumInrEmbedding sigma tau)) (fun _ _ => 1) =
      Finsupp.indicator
        (s.map (sumInlEmbedding sigma tau) ∪
          t.map (sumInrEmbedding sigma tau)) (fun _ _ => 1) := by
  ext x
  cases x <;> simp [sumInlEmbedding, sumInrEmbedding]

private theorem prod_X_eq_monomial_indicator_map
    {R sigma tau : Type*} [CommSemiring R]
    (e : sigma ↪ tau) (s : Finset sigma) :
    ∏ i ∈ s, (X (e i) : MvPolynomial tau R) =
      monomial (Finsupp.indicator (s.map e) (fun _ _ => 1)) 1 := by
  classical
  simpa [Finset.prod_map] using
    (MvPolynomial.prod_X_pow (R := R) (fun _ : tau => 1) (s.map e))

private theorem rightComplementMonomial_one
    {R sigma tau : Type*} [CommSemiring R]
    [Fintype sigma] [DecidableEq sigma]
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    (rightComplementMonomial (R := R) (τ := tau)
        (fun _ : sigma => 1) m.1) =
      monomial
        (Finsupp.indicator
          ((Finset.univ \ m.1.support).map
            (sumInrEmbedding tau sigma)) (fun _ _ => 1)) 1 := by
  classical
  unfold rightComplementMonomial
  have hone (i : sigma) (hi : i ∈ m.1.support) : m.1 i = 1 := by
    have hne : m.1 i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle := m.2 i
    cases hdi : m.1 i with
    | zero => exact (hne hdi).elim
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            rw [hdi] at hle
            exact (Nat.not_succ_le_zero n
              (Nat.le_of_succ_le_succ hle)).elim
  calc
    ∏ i, X (Sum.inr i) ^
          (1 - m.1 i) =
        ∏ i ∈ Finset.univ \ m.1.support,
          (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) := by
      calc
        (∏ i, (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) ^
            (1 - m.1 i)) =
            ∏ i ∈ Finset.univ \ m.1.support,
              (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) ^
                (1 - m.1 i) := by
          symm
          apply Finset.prod_subset Finset.sdiff_subset
          intro i hi_univ hi_diff
          have hi_support : i ∈ m.1.support := by
            by_contra hi
            exact hi_diff (Finset.mem_sdiff.mpr ⟨hi_univ, hi⟩)
          simp [hone i hi_support]
        _ = ∏ i ∈ Finset.univ \ m.1.support,
              (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hzero : m.1 i = 0 :=
            Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hi).2
          simp [hzero]
    _ = monomial
          (Finsupp.indicator
            ((Finset.univ \ m.1.support).map
              (sumInrEmbedding tau sigma)) (fun _ _ => 1)) 1 := by
      exact prod_X_eq_monomial_indicator_map
        (sumInrEmbedding tau sigma) (Finset.univ \ m.1.support)

private theorem coe_box_eq_sum_support_monomials
    {R sigma : Type*} [CommSemiring R]
    [Fintype sigma]
    (p : degreeOfLE sigma R (fun _ => 1)) :
    p.1 = ∑ m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1},
      monomial
        (Finsupp.indicator m.1.support (fun _ _ => 1))
        ((basisDegreeOfLE (fun _ : sigma => 1)).repr p m) := by
  classical
  conv_lhs =>
    rw [← (basisDegreeOfLE (R := R) (fun _ : sigma => 1)).sum_repr p]
  simp only [Submodule.coe_sum, Submodule.coe_smul, coe_basisDegreeOfLE,
    smul_eq_C_mul, C_mul_monomial, mul_one]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← finsupp_eq_indicator_support_of_le_one m.1 m.2]

private theorem algebraicSymbol_one_eq_doubleSum
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (T : degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      degreeOfLE tau ℂ (fun _ => 1)) :
    algebraicSymbol (fun _ : sigma => 1)
        ((degreeOfLE tau ℂ (fun _ => 1)).subtype.comp T) =
      ∑ m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1},
        ∑ a : {a : tau →₀ ℕ // ∀ i, a i ≤ 1},
          monomial
            (Finsupp.indicator
              (a.1.support.map (sumInlEmbedding tau sigma) ∪
                (Finset.univ \ m.1.support).map
                  (sumInrEmbedding tau sigma)) (fun _ _ => 1))
            ((basisDegreeOfLE (fun _ : tau => 1)).repr
              (T (basisDegreeOfLE (fun _ : sigma => 1) m)) a) := by
  classical
  rw [algebraicSymbol]
  apply Finset.sum_congr rfl
  intro m hm
  rw [boxChoose_one m, Nat.cast_one, map_one, one_mul,
    coe_box_eq_sum_support_monomials
      (T (basisDegreeOfLE (fun _ : sigma => 1) m)), map_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [rename_monomial, rightComplementMonomial_one, monomial_mul,
    mapDomain_indicator_sumInl, indicator_disjoint_union, mul_one]

private theorem full_left_mul_rename_box_eq_sum
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (p : degreeOfLE sigma ℂ (fun _ => 1)) :
    rename Sum.inl (∏ i : tau, X i) * rename Sum.inr p.1 =
      ∑ n : {n : sigma →₀ ℕ // ∀ i, n i ≤ 1},
        monomial
          (Finsupp.indicator
            (Finset.univ.map (sumInlEmbedding tau sigma) ∪
              n.1.support.map (sumInrEmbedding tau sigma))
            (fun _ _ => 1))
          ((basisDegreeOfLE (fun _ : sigma => 1)).repr p n) := by
  classical
  rw [coe_box_eq_sum_support_monomials p, map_sum, Finset.mul_sum]
  have hleft :
      rename (R := ℂ) Sum.inl (∏ i : tau, X i) =
        monomial
          (Finsupp.indicator
            (Finset.univ.map (sumInlEmbedding tau sigma))
            (fun _ _ => 1)) 1 := by
    rw [map_prod]
    simpa only [rename_X] using
      prod_X_eq_monomial_indicator_map
        (R := ℂ) (sumInlEmbedding tau sigma) Finset.univ
  rw [hleft]
  apply Finset.sum_congr rfl
  intro n hn
  rw [rename_monomial, mapDomain_indicator_sumInr, monomial_mul,
    indicator_disjoint_union, one_mul]

private theorem complement_indicator_blocks
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (a : Finset tau) (m : Finset sigma) :
    complementExponent
        (Finsupp.indicator
          (a.map (sumInlEmbedding tau sigma) ∪
            (Finset.univ \ m).map (sumInrEmbedding tau sigma))
          (fun _ _ => 1)) =
      Finsupp.indicator
        ((Finset.univ \ a).map (sumInlEmbedding tau sigma) ∪
          m.map (sumInrEmbedding tau sigma)) (fun _ _ => 1) := by
  ext x
  cases x <;> simp [complementExponent_apply, sumInlEmbedding,
    sumInrEmbedding]

private theorem card_indicator_blocks
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (a : Finset tau) (m : Finset sigma) :
    (a.map (sumInlEmbedding tau sigma) ∪
        (Finset.univ \ m).map (sumInrEmbedding tau sigma)).card +
      ((Finset.univ \ a).map (sumInlEmbedding tau sigma) ∪
        m.map (sumInrEmbedding tau sigma)).card =
      Fintype.card tau + Fintype.card sigma := by
  simp [Finset.card_union_of_disjoint, Finset.card_sdiff,
    sumInlEmbedding, sumInrEmbedding]

private theorem signed_reciprocal_differential_basis_term
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (a : Finset tau) (m n : Finset sigma) (c b : ℂ) :
    specializeRight (fun _ : sigma => 0)
        (applyNegDifferential
          (C ((-1 : ℂ) ^ (Fintype.card tau + Fintype.card sigma)) *
            signedMultiaffineReciprocal
              (monomial
                (Finsupp.indicator
                  (a.map (sumInlEmbedding tau sigma) ∪
                    (Finset.univ \ m).map
                      (sumInrEmbedding tau sigma)) (fun _ _ => 1)) c))
          (monomial
            (Finsupp.indicator
              (Finset.univ.map (sumInlEmbedding tau sigma) ∪
                n.map (sumInrEmbedding tau sigma)) (fun _ _ => 1)) b)) =
      if m = n then
        monomial (Finsupp.indicator a (fun _ _ => 1)) (c * b)
      else 0 := by
  classical
  let d := Finsupp.indicator
    (a.map (sumInlEmbedding tau sigma) ∪
      (Finset.univ \ m).map (sumInrEmbedding tau sigma)) (fun _ _ => 1)
  let e := Finsupp.indicator
    ((Finset.univ \ a).map (sumInlEmbedding tau sigma) ∪
      m.map (sumInrEmbedding tau sigma)) (fun _ _ => 1)
  have hde : complementExponent d = e := by
    exact complement_indicator_blocks a m
  have hsum : d.sum (fun _ k => k) + e.sum (fun _ k => k) =
      Fintype.card tau + Fintype.card sigma := by
    rw [show d.sum (fun _ k => k) =
        (a.map (sumInlEmbedding tau sigma) ∪
          (Finset.univ \ m).map (sumInrEmbedding tau sigma)).card by
          exact indicator_totalDegree _]
    rw [show e.sum (fun _ k => k) =
        ((Finset.univ \ a).map (sumInlEmbedding tau sigma) ∪
          m.map (sumInrEmbedding tau sigma)).card by
          exact indicator_totalDegree _]
    exact card_indicator_blocks a m
  rw [signedMultiaffineReciprocal_monomial, hde,
    applyNegDifferential_C_mul_left, applyNegDifferential_monomial]
  simp only [map_mul, map_C]
  rw [specializeRight_zero_applyMonomialDifferential_indicator_monomial]
  by_cases hmn : m = n
  · rw [if_pos hmn, if_pos hmn, C_mul_monomial, C_mul_monomial]
    congr 1
    rw [← pow_add, hsum]
    ring
  · rw [if_neg hmn, if_neg hmn]
    simp

/-- The coefficient identity in Borcea--Branden, arXiv:0809.0401,
Lemma 2.2, for finite coordinate-wise degree-one source and target boxes. -/
theorem finiteSymbolIdentity
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (T : degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      degreeOfLE tau ℂ (fun _ => 1))
    (p : degreeOfLE sigma ℂ (fun _ => 1)) :
    specializeRight (fun _ : sigma => 0)
        (applyNegDifferential
          (C ((-1 : ℂ) ^ (Fintype.card tau + Fintype.card sigma)) *
            signedMultiaffineReciprocal
              (algebraicSymbol (fun _ : sigma => 1)
                ((degreeOfLE tau ℂ (fun _ => 1)).subtype.comp T)))
          (rename Sum.inl (∏ i : tau, X i) * rename Sum.inr p.1)) =
      (T p).1 := by
  classical
  rw [algebraicSymbol_one_eq_doubleSum T,
    signedMultiaffineReciprocal_sum]
  simp_rw [signedMultiaffineReciprocal_sum]
  rw [full_left_mul_rename_box_eq_sum p,
    applyNegDifferential_finsetSum_left]
  simp_rw [applyNegDifferential_C_mul_left,
    applyNegDifferential_finsetSum_left,
    applyNegDifferential_finsetSum_right]
  simp only [map_sum]
  simp_rw [signed_reciprocal_differential_basis_term]
  have hsupport (m n : {d : sigma →₀ ℕ // ∀ i, d i ≤ 1}) :
      m.1.support = n.1.support ↔ m = n := by
    rw [← finsupp_eq_iff_support_eq_of_le_one m.1 n.1 m.2 n.2]
    exact Subtype.coe_inj.symm
  simp_rw [hsupport]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    ∑ m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1},
        ∑ a : {a : tau →₀ ℕ // ∀ i, a i ≤ 1},
          monomial (Finsupp.indicator a.1.support (fun _ _ => 1))
            ((basisDegreeOfLE (fun _ : tau => 1)).repr
                (T (basisDegreeOfLE (fun _ : sigma => 1) m)) a *
              (basisDegreeOfLE (fun _ : sigma => 1)).repr p m) =
      ∑ m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1},
        C ((basisDegreeOfLE (fun _ : sigma => 1)).repr p m) *
          (T (basisDegreeOfLE (fun _ : sigma => 1) m)).1 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [coe_box_eq_sum_support_monomials
        (T (basisDegreeOfLE (fun _ : sigma => 1) m)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [C_mul_monomial]
      congr 1
      ring
    _ = (T p).1 := by
      rw [← (basisDegreeOfLE (R := ℂ) (fun _ : sigma => 1)).sum_repr p]
      simp only [map_sum, LinearMap.map_smul, Submodule.coe_sum,
        Submodule.coe_smul, smul_eq_C_mul]

end

end RealRooted.BorceaBranden
