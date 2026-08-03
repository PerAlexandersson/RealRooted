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
  by_cases hi : i ∈ d.support
  · rw [Finsupp.indicator_of_mem hi]
    have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle := hd i
    cases hdi : d i with
    | zero => exact (hne hdi).elim
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            rw [hdi] at hle
            exact (Nat.not_succ_le_zero n (Nat.le_of_succ_le_succ hle)).elim
  · rw [Finsupp.indicator_of_notMem hi]
    simpa [Finsupp.mem_support_iff] using hi

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
    {d : sigma →₀ ℕ // ∀ i, d i ≤ 1} ≃ Finset sigma where
  toFun d := d.1.support
  invFun s :=
    ⟨Finsupp.indicator s (fun _ _ => 1), fun i => by
      by_cases hi : i ∈ s <;> simp [Finsupp.indicator, hi]⟩
  left_inv d :=
    Subtype.ext (finsupp_eq_indicator_support_of_le_one d.1 d.2).symm
  right_inv s := by
    ext i
    simp [Finsupp.indicator]

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

end

end RealRooted.BorceaBranden
