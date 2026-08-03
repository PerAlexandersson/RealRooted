import RealRooted.BorceaBranden.FiniteSymbolCoefficient

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
  have hle := hd i
  interval_cases h : d i <;> simp [Finsupp.indicator, h]

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

namespace MvPolynomial

/-- The complement of a zero-one exponent has total degree equal to the
cardinality of the variable set minus the original total degree. -/
theorem sum_one_sub_eq_card_sub_degree
    {σ : Type*} [Fintype σ] (m : σ →₀ ℕ)
    (hm : ∀ i, m i ≤ 1) :
    ∑ i, (1 - m i) = Fintype.card σ - m.degree := by
  rw [Finset.sum_tsub_distrib Finset.univ (by
    intro i hi
    exact hm i)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.mul_one]
  congr 1
  rw [Finsupp.degree_apply]
  exact (Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl)).symm

end MvPolynomial
