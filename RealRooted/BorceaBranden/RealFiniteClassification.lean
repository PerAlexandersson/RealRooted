import RealRooted.BorceaBranden.MultivariateHKO
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.DegreeBox

/-!
# Real finite stability preservers: the low-rank branch

This file formalizes the complete sufficiency proof for the rank-at-most-two
alternative in the real finite Borcea--Branden classification.  It uses the
source-faithful all-real-combinations formulation of the exceptional range.

The necessity direction and the two finite-symbol alternatives remain open.
The missing HKO part is the converse orientation dichotomy for an arbitrary
stable two-dimensional real span.
-/

namespace RealRooted
namespace BorceaBranden

noncomputable section

/-- A real linear operator on a coordinate-wise degree box preserves real
stability, allowing the zero output. -/
def PreservesRealStabilityOnDegreeBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) : Prop :=
  ∀ f, MvRealStable f.1 → MvRealStableOrZero (T f)

/-- The rank-at-most-two exceptional representation from the real finite
classification, phrased invariantly by requiring the real span of `P,Q` to
be stable or zero. -/
def HasStableRankTwoRepresentation
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) : Prop :=
  ∃ (α β : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] ℝ)
      (P Q : MvPolynomial σ ℝ),
    AllComboMvRealStableOrZero P Q ∧
      ∀ f, T f = (α f) • P + (β f) • Q

/-- Every operator with the stable rank-at-most-two representation preserves
real stability.  In fact, the proof shows that every output is stable or
zero, independently of the input. -/
theorem HasStableRankTwoRepresentation.preservesRealStabilityOnDegreeBox
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (h : HasStableRankTwoRepresentation κ T) :
    PreservesRealStabilityOnDegreeBox κ T := by
  intro f _hf
  obtain ⟨α, β, P, Q, hall, hT⟩ := h
  rw [hT, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  exact hall (α f) (β f)

/-- A representation whose two spanning polynomials form a stable affine
pencil is an instance of the rank-at-most-two exceptional representation. -/
theorem hasStableRankTwoRepresentation_of_stablePencil
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    {α β : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] ℝ}
    {P Q : MvPolynomial σ ℝ}
    (hpencil : MvStablePencil P Q)
    (hT : ∀ f, T f = (α f) • P + (β f) • Q) :
    HasStableRankTwoRepresentation κ T := by
  exact ⟨α, β, P, Q, hpencil.allComboMvRealStableOrZero, hT⟩

/-- The proper-position formulation in Borcea--Branden Theorem 1.2(a)
implies the invariant stable-span rank-at-most-two representation. -/
theorem hasStableRankTwoRepresentation_of_properPosition
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    {α β : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] ℝ}
    {P Q : MvPolynomial σ ℝ}
    (hproper : MvProperPosition P Q)
    (hT : ∀ f, T f = (α f) • P + (β f) • Q) :
    HasStableRankTwoRepresentation κ T := by
  exact ⟨α, β, P, Q, hproper.allComboMvRealStableOrZero, hT⟩

/-- The zero operator belongs to the stable rank-at-most-two exceptional
branch. -/
theorem hasStableRankTwoRepresentation_zero
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) :
    HasStableRankTwoRepresentation κ
      (0 : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) := by
  refine ⟨0, 0, 0, 0, ?_, ?_⟩
  · intro α β
    simp only [mul_zero, add_zero]
    exact MvRealStableOrZero.zero
  · intro f
    simp

end

end BorceaBranden
end RealRooted
