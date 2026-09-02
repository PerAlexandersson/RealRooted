import RealRooted.LiebSokalOperator

/-!
# Linearity of negative differential evaluation

This module packages `applyNegDifferential` as a linear map in either argument
and exposes the resulting finite-sum identities. The API is independent of the
applications that consume it.
-/

namespace RealRooted

noncomputable section

open BigOperators

/-- Negative differential evaluation as a linear map in its first argument. -/
def applyNegDifferentialLeftLinearMap
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (G : MvPolynomial sigma R) :
    MvPolynomial sigma R →ₗ[R] MvPolynomial sigma R where
  toFun F := applyNegDifferential F G
  map_add' F H := applyNegDifferential_add_left F H G
  map_smul' c F := by
    simp [MvPolynomial.smul_eq_C_mul, applyNegDifferential_C_mul_left]

/-- Negative differential evaluation as a linear map in its second argument. -/
def applyNegDifferentialRightLinearMap
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F : MvPolynomial sigma R) :
    MvPolynomial sigma R →ₗ[R] MvPolynomial sigma R where
  toFun G := applyNegDifferential F G
  map_add' := applyNegDifferential_add_right F
  map_smul' c G := by
    simp [MvPolynomial.smul_eq_C_mul, applyNegDifferential_C_mul_right]

/-- `applyNegDifferential` distributes over a finite sum in its first
argument. -/
theorem applyNegDifferential_finsetSum_left
    {R sigma I : Type*} [CommRing R] [Fintype sigma]
    (s : Finset I) (F : I → MvPolynomial sigma R)
    (G : MvPolynomial sigma R) :
    applyNegDifferential (∑ x ∈ s, F x) G =
      ∑ x ∈ s, applyNegDifferential (F x) G := by
  exact map_sum (applyNegDifferentialLeftLinearMap G) F s

/-- `applyNegDifferential` distributes over a finite sum in its second
argument. -/
theorem applyNegDifferential_finsetSum_right
    {R sigma I : Type*} [CommRing R] [Fintype sigma]
    (F : MvPolynomial sigma R) (s : Finset I)
    (G : I → MvPolynomial sigma R) :
    applyNegDifferential F (∑ x ∈ s, G x) =
      ∑ x ∈ s, applyNegDifferential F (G x) := by
  exact map_sum (applyNegDifferentialRightLinearMap F) G s

/-- `applyNegDifferential` distributes over finite sums in both arguments. -/
theorem applyNegDifferential_doubleSum
    {R sigma I J : Type*} [CommRing R] [Fintype sigma]
    (s : Finset I) (t : Finset J)
    (F : I → MvPolynomial sigma R) (G : J → MvPolynomial sigma R) :
    applyNegDifferential (∑ i ∈ s, F i) (∑ j ∈ t, G j) =
      ∑ i ∈ s, ∑ j ∈ t, applyNegDifferential (F i) (G j) := by
  rw [applyNegDifferential_finsetSum_left]
  simp_rw [applyNegDifferential_finsetSum_right]

end

end RealRooted
