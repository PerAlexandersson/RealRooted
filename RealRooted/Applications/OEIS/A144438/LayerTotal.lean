import RealRooted.Applications.OEIS.A144438.ExactLayer

/-!
# The recurrence-defined total of the exact Deco layers

This file first defines the total polynomial by its two-step layer recurrence.
It separately sums the stable exact-history layers and proves that this
combinatorial sum realizes the recurrence-defined total.  No stability claim
is made for the total: multivariate real stability is not closed under
arbitrary addition.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- The homogenized Deco total, defined directly by the normal and exceptional
layer operators. -/
def decoLayerTotal : (n : Nat) → MvPolynomial (DecoLayerCoord n) Real
  | 0 => MvPolynomial.X none
  | 1 => decoNormalLayerStep (MvPolynomial.X none)
  | n + 2 =>
      decoNormalLayerStep (decoLayerTotal (n + 1)) +
        decoExceptionalLayerStep (decoLayerTotal n)

@[simp] theorem decoLayerTotal_zero :
    decoLayerTotal 0 =
      (MvPolynomial.X none : MvPolynomial (DecoLayerCoord 0) Real) := rfl

@[simp] theorem decoLayerTotal_one :
    decoLayerTotal 1 = decoNormalLayerStep
      (MvPolynomial.X none : MvPolynomial (DecoLayerCoord 0) Real) := rfl

/-- The defining normal-plus-exceptional two-step recurrence. -/
theorem decoLayerTotal_recurrence (n : Nat) :
    decoLayerTotal (n + 2) =
      decoNormalLayerStep (decoLayerTotal (n + 1)) +
        decoExceptionalLayerStep (decoLayerTotal n) := rfl

/-- The recurrence-defined total has the homogeneous degree expected at each
rank. -/
theorem decoLayerTotal_isHomogeneous :
    ∀ n : Nat, (decoLayerTotal n).IsHomogeneous (n + 1) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa using
        (MvPolynomial.isHomogeneous_X Real
          (none : DecoLayerCoord 0))
  | one =>
      exact decoNormalLayerStep_isHomogeneous
        (MvPolynomial.isHomogeneous_X Real
          (none : DecoLayerCoord 0))
  | more n ih0 ih1 =>
      rw [decoLayerTotal_recurrence]
      exact (decoNormalLayerStep_isHomogeneous ih1).add
        (decoExceptionalLayerStep_isHomogeneous ih0)

/-- The recurrence-defined total has nonnegative coefficients at every
rank. -/
theorem decoLayerTotal_hasNonnegCoeffs :
    ∀ n : Nat, MvPolynomial.HasNonnegCoeffs (decoLayerTotal n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa using
        (MvPolynomial.HasNonnegCoeffs.X (none : DecoLayerCoord 0))
  | one =>
      exact decoNormalLayerStep_hasNonnegCoeffs
        (MvPolynomial.HasNonnegCoeffs.X (none : DecoLayerCoord 0))
  | more n ih0 ih1 =>
      rw [decoLayerTotal_recurrence]
      exact (decoNormalLayerStep_hasNonnegCoeffs ih1).add
        (decoExceptionalLayerStep_hasNonnegCoeffs ih0)

/-- The sum of the operator-defined polynomials over exact histories. -/
def decoExactLayerSum (n : Nat) : MvPolynomial (DecoLayerCoord n) Real :=
  ∑ H : DecoExceptionalHistory (n + 2), decoExactLayer H

/-- The normal layer operator commutes with finite sums. -/
theorem sum_decoNormalLayerStep {R ι : Type*} [CommSemiring R] [Fintype ι]
    {n : Nat} (P : ι → MvPolynomial (DecoLayerCoord n) R) :
    (∑ i, decoNormalLayerStep (P i)) =
      decoNormalLayerStep (∑ i, P i) := by
  classical
  unfold decoNormalLayerStep
  simp only [map_sum]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_comm]

/-- The exceptional layer operator commutes with finite sums. -/
theorem sum_decoExceptionalLayerStep {R ι : Type*} [CommSemiring R]
    [Fintype ι] {n : Nat} (P : ι → MvPolynomial (DecoLayerCoord n) R) :
    (∑ i, decoExceptionalLayerStep (P i)) =
      decoExceptionalLayerStep (∑ i, P i) := by
  classical
  simp [decoExceptionalLayerStep, map_sum, ← Finset.mul_sum]

@[simp] theorem decoExactLayerSum_zero :
    decoExactLayerSum 0 =
      (MvPolynomial.X none : MvPolynomial (DecoLayerCoord 0) Real) := by
  unfold decoExactLayerSum
  rw [Fintype.sum_eq_single DecoExceptionalHistory.seed]
  · exact decoExactLayer_seed
  · intro H hH
    exact (hH (H.eq_seed)).elim

@[simp] theorem decoExactLayerSum_one :
    decoExactLayerSum 1 = decoNormalLayerStep
      (MvPolynomial.X none : MvPolynomial (DecoLayerCoord 0) Real) := by
  unfold decoExactLayerSum
  rw [Fintype.sum_eq_single
    (DecoExceptionalHistory.normal DecoExceptionalHistory.seed)]
  · rw [decoExactLayer_normal, decoExactLayer_seed]
  · intro H hH
    exact (hH (H.eq_normal_seed)).elim

/-- The total exact-layer polynomial obeys the normal-plus-exceptional
two-step operator recurrence. -/
theorem decoExactLayerSum_recurrence (n : Nat) :
    decoExactLayerSum (n + 2) =
      decoNormalLayerStep (decoExactLayerSum (n + 1)) +
        decoExceptionalLayerStep (decoExactLayerSum n) := by
  unfold decoExactLayerSum
  rw [← (DecoExceptionalHistory.lastStepEquiv (n + 1)).sum_comp]
  simp only [Fintype.sum_sum_type,
    DecoExceptionalHistory.lastStepEquiv_inl,
    DecoExceptionalHistory.lastStepEquiv_inr,
    decoExactLayer_normal, decoExactLayer_exceptional]
  rw [sum_decoNormalLayerStep, sum_decoExceptionalLayerStep]

/-- The exact-history layer sum realizes the recurrence-defined total. -/
theorem decoExactLayerSum_eq_decoLayerTotal :
    ∀ n : Nat, decoExactLayerSum n = decoLayerTotal n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [decoExactLayerSum_recurrence, decoLayerTotal_recurrence, ih0, ih1]

end

end RealRooted.Applications.OEIS
