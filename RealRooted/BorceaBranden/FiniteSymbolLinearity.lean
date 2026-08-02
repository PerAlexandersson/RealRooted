import RealRooted.LiebSokalOperator

/-!
# Finite-sum linearity for the finite-symbol argument

This module exposes the finite-sum consequences of the additive laws for
`applyNegDifferential`. They are used to distribute the two basis expansions
in Borcea--Branden, arXiv:0809.0401, Lemma 2.2.
-/

namespace RealRooted

noncomputable section

open BigOperators

/-- `applyNegDifferential` distributes over a finite sum in its first
argument. -/
theorem applyNegDifferential_finsetSum_left
    {R sigma I : Type*} [CommRing R] [Fintype sigma]
    (s : Finset I) (F : I → MvPolynomial sigma R)
    (G : MvPolynomial sigma R) :
    applyNegDifferential (∑ x ∈ s, F x) G =
      ∑ x ∈ s, applyNegDifferential (F x) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      rw [Finset.sum_insert hxs, applyNegDifferential_add_left,
        ih, Finset.sum_insert hxs]

/-- `applyNegDifferential` distributes over a finite sum in its second
argument. -/
theorem applyNegDifferential_finsetSum_right
    {R sigma I : Type*} [CommRing R] [Fintype sigma]
    (F : MvPolynomial sigma R) (s : Finset I)
    (G : I → MvPolynomial sigma R) :
    applyNegDifferential F (∑ x ∈ s, G x) =
      ∑ x ∈ s, applyNegDifferential F (G x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      rw [Finset.sum_insert hxs, applyNegDifferential_add_right,
        ih, Finset.sum_insert hxs]

/-- `applyNegDifferential` distributes over finite sums in both arguments. -/
theorem applyNegDifferential_doubleSum
    {R sigma I J : Type*} [CommRing R] [Fintype sigma]
    (s : Finset I) (t : Finset J)
    (F : I → MvPolynomial sigma R) (G : J → MvPolynomial sigma R) :
    applyNegDifferential (∑ i ∈ s, F i) (∑ j ∈ t, G j) =
      ∑ i ∈ s, ∑ j ∈ t, applyNegDifferential (F i) (G j) := by
  rw [applyNegDifferential_finsetSum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact applyNegDifferential_finsetSum_right (F i) t G

end

end RealRooted
