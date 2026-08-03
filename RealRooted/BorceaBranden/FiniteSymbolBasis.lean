import Mathlib.Data.Finsupp.Weight
import RealRooted.BorceaBranden.FiniteSymbolCoefficient
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol

/-!
# Degree-one exponent coordinates for finite symbols

This module identifies coordinate-wise degree-one exponent vectors with their
supports. It supplies the basis normalization used in the coefficient
calculation of Borcea--Branden, arXiv:0809.0401, Lemma 2.2.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- A natural-valued finitely supported function bounded coordinate-wise by
one is the indicator of its support. -/
theorem finsupp_eq_indicator_support_of_le_one
    {sigma : Type*} (d : sigma →₀ ℕ)
    (hd : ∀ i, d i ≤ 1) :
    d = Finsupp.indicator d.support (fun _ _ => 1) := by
  classical
  ext i
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd i) with h | h <;>
    simp [Finsupp.indicator, h]

/-- Coordinate-wise degree-one exponent vectors are equal exactly when their
supports are equal. -/
theorem finsupp_eq_iff_support_eq_of_le_one
    {sigma : Type*} (d e : sigma →₀ ℕ)
    (hd : ∀ i, d i ≤ 1) (he : ∀ i, e i ≤ 1) :
    d = e ↔ d.support = e.support := by
  classical
  constructor
  · exact fun h => congrArg Finsupp.support h
  · intro hsupport
    rw [finsupp_eq_indicator_support_of_le_one d hd,
      finsupp_eq_indicator_support_of_le_one e he, hsupport]

/-- Natural-valued exponent vectors bounded by one are equivalent to finite
subsets, via their supports. -/
noncomputable def degreeOneExponentEquivFinset (sigma : Type*) :
    {d : sigma →₀ ℕ // ∀ i, d i ≤ 1} ≃ Finset sigma := by
  classical
  exact
    { toFun := fun d => d.1.support
      invFun := fun s =>
        ⟨Finsupp.indicator s (fun _ _ => 1), fun i => by
          by_cases hi : i ∈ s <;> simp [Finsupp.indicator, hi]⟩
      left_inv := fun d =>
        Subtype.ext (finsupp_eq_indicator_support_of_le_one d.1 d.2).symm
      right_inv := fun s => by
        ext i
        simp [Finsupp.indicator] }

/-- The total degree of a zero-one exponent vector is the cardinality of its
support. -/
theorem card_support_eq_degree_of_le_one
    {sigma : Type*} (d : sigma →₀ ℕ) (hd : ∀ i, d i ≤ 1) :
    d.support.card = d.degree := by
  classical
  rw [Finsupp.degree_apply]
  calc
    d.support.card = ∑ i ∈ d.support, 1 := by simp
    _ = ∑ i ∈ d.support, d i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpos : 0 < d i := Finsupp.mem_support_iff.mp hi |>.bot_lt
      have hone : d i = 1 := Nat.le_antisymm (hd i) hpos
      simp [hone]

@[simp]
theorem degree_degreeOneExponentEquivFinset_symm
    {sigma : Type*} (s : Finset sigma) :
    ((degreeOneExponentEquivFinset sigma).symm s).1.degree = s.card := by
  let d := (degreeOneExponentEquivFinset sigma).symm s
  have hsupp : d.1.support = s :=
    (degreeOneExponentEquivFinset sigma).apply_symm_apply s
  calc
    d.1.degree = d.1.support.card :=
      (card_support_eq_degree_of_le_one d.1 d.2).symm
    _ = s.card := congrArg Finset.card hsupp

end

end RealRooted.BorceaBranden

namespace Finsupp

/-- A one-variable exponent vector is the singleton at its total degree. -/
@[simp] theorem single_default_degree_fin_one (m : Fin 1 →₀ ℕ) :
    single default m.degree = m := by
  have hdegree : m.degree = ∑ i, m i := by
    rw [degree_apply]
    apply Finset.sum_subset (Finset.subset_univ m.support)
    intro i _ hi
    simpa [mem_support_iff] using hi
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rw [hdegree]
  simp

/-- The complement of a zero-one exponent has total degree equal to the
cardinality of the variable set minus the original total degree. -/
theorem sum_one_sub_eq_card_sub_degree
    {σ : Type*} [Fintype σ] (m : σ →₀ ℕ)
    (hm : ∀ i, m i ≤ 1) :
    ∑ i, (1 - m i) = Fintype.card σ - m.degree := by
  rw [Finset.sum_tsub_distrib Finset.univ (by
    intro i _
    exact hm i)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.mul_one]
  congr 1
  rw [degree_apply]
  exact (sum_fintype m (fun _ e => e) (fun _ => rfl)).symm

end Finsupp

namespace RealRooted.BorceaBranden

/-- Bounded exponent vectors in one variable are indexed by `Fin (d + 1)`. -/
noncomputable def degreeOfLEFinOneEquiv (d : ℕ) :
    {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ d} ≃ Fin (d + 1) :=
  (MvPolynomial.degreeOfLEIndexEquiv (fun _ : Fin 1 => d)).trans
    (Equiv.piUnique _)

lemma degreeOfLEFinOneEquiv_val (d : ℕ)
    (m : {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ d}) :
    (degreeOfLEFinOneEquiv d m : ℕ) = m.1 0 := by
  rfl

end RealRooted.BorceaBranden

namespace RealRooted.BorceaBranden

noncomputable section

open MvPolynomial

/-- The canonical one-variable degree-box index associated with a natural
number. The truncation is inactive on `Fin (n + 1)`. -/
noncomputable def finOneDegreeIndex (n k : ℕ) :
    {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ n} :=
  (degreeOfLEFinOneEquiv n).symm
    ⟨min k n, Nat.lt_succ_iff.mpr (Nat.min_le_right k n)⟩

@[simp] lemma finOneDegreeIndex_equiv_apply (n : ℕ)
    (m : {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ n}) :
    finOneDegreeIndex n (degreeOfLEFinOneEquiv n m) = m := by
  apply (degreeOfLEFinOneEquiv n).injective
  apply Fin.ext
  simp [finOneDegreeIndex, degreeOfLEFinOneEquiv_val, m.2 0]

/-- Expand a one-variable algebraic symbol over its canonical `Fin (n + 1)`
indexing. -/
theorem algebraicSymbol_finOne_eq_sum_fin
    {τ R : Type*} [CommSemiring R] (n : ℕ)
    (T : degreeOfLE (Fin 1) R (fun _ => n) →ₗ[R] MvPolynomial τ R) :
    algebraicSymbol (fun _ : Fin 1 => n) T =
      ∑ k : Fin (n + 1),
        C (n.choose k : R) *
          rename (Sum.inl : τ → τ ⊕ Fin 1)
            (T (basisDegreeOfLE (R := R) (fun _ : Fin 1 => n)
              (finOneDegreeIndex n k))) *
          X (Sum.inr default) ^ (n - k) := by
  classical
  rw [algebraicSymbol]
  apply Fintype.sum_equiv (degreeOfLEFinOneEquiv n)
  intro m
  have hindex : finOneDegreeIndex n (m.1 0) = m := by
    apply (degreeOfLEFinOneEquiv n).injective
    apply Fin.ext
    simp [finOneDegreeIndex, degreeOfLEFinOneEquiv_val,
      Nat.min_eq_left (m.2 0)]
  simp [hindex, boxChoose,
    rightComplementMonomial, degreeOfLEFinOneEquiv_val]

/-- Expand a one-variable algebraic symbol over the natural-number range
`0, ..., n`. -/
theorem algebraicSymbol_finOne_eq_sum_range
    {τ R : Type*} [CommSemiring R] (n : ℕ)
    (T : degreeOfLE (Fin 1) R (fun _ => n) →ₗ[R] MvPolynomial τ R) :
    algebraicSymbol (fun _ : Fin 1 => n) T =
      ∑ k ∈ Finset.range (n + 1),
        C (n.choose k : R) *
          rename (Sum.inl : τ → τ ⊕ Fin 1)
            (T (basisDegreeOfLE (R := R) (fun _ : Fin 1 => n)
              (finOneDegreeIndex n k))) *
          X (Sum.inr default) ^ (n - k) := by
  classical
  let g : ℕ → MvPolynomial (τ ⊕ Fin 1) R := fun k =>
    C (n.choose k : R) *
      rename (Sum.inl : τ → τ ⊕ Fin 1)
        (T (basisDegreeOfLE (R := R) (fun _ : Fin 1 => n)
          (finOneDegreeIndex n k))) *
      X (Sum.inr default) ^ (n - k)
  rw [algebraicSymbol_finOne_eq_sum_fin (n := n) (T := T)]
  simpa [g] using Fin.sum_univ_eq_sum_range g (n + 1)

end

end RealRooted.BorceaBranden
