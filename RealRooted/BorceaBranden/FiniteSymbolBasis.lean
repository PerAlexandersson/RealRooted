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
    {sigma : Type*} [DecidableEq sigma] (d : sigma →₀ ℕ)
    (hd : ∀ i, d i ≤ 1) :
    d = Finsupp.indicator d.support (fun _ _ => 1) := by
  ext i
  by_cases hi : i ∈ d.support
  · rw [Finsupp.indicator_of_mem hi]
    have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    lia
  · rw [Finsupp.indicator_of_notMem hi]
    exact Finsupp.not_mem_support_iff.mp hi

/-- Coordinate-wise degree-one exponent vectors are equal exactly when their
supports are equal. -/
theorem finsupp_eq_iff_support_eq_of_le_one
    {sigma : Type*} [DecidableEq sigma] (d e : sigma →₀ ℕ)
    (hd : ∀ i, d i ≤ 1) (he : ∀ i, e i ≤ 1) :
    d = e ↔ d.support = e.support := by
  constructor
  · exact fun h => congrArg Finsupp.support h
  · intro hsupport
    rw [finsupp_eq_indicator_support_of_le_one d hd,
      finsupp_eq_indicator_support_of_le_one e he, hsupport]

end

end RealRooted.BorceaBranden
