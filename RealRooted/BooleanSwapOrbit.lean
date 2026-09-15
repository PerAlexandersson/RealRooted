import RealRooted.Mathlib.RingTheory.MvPolynomial.BooleanSwapOrbit
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative
import RealRooted.MultivariateStability.LinearForm
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Powerset

/-!
# Stable Boolean variable-choice orbits

The active part of a Boolean orbit under disjoint variable swaps chooses one
endpoint from every pair.  Its subset sum factors as a fixed squarefree
monomial times a product of linear forms `X x + X y`.  The weighted API also
retains the scalar weight sums contributed by inactive pairs.
-/

namespace RealRooted

open scoped BigOperators

noncomputable section

/-- The subset expansion choosing a left or right variable from every pair. -/
def booleanVariableChoiceSum {σ ι R : Type*} [CommSemiring R]
    [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ) :
    MvPolynomial σ R :=
  ∑ t ∈ s.powerset,
    MvPolynomial.finsetMonomial fixed *
      ((∏ i ∈ t, MvPolynomial.X (left i)) *
        ∏ i ∈ s \ t, MvPolynomial.X (right i))

/-- The Boolean variable-choice sum factors into independent linear forms. -/
theorem booleanVariableChoiceSum_eq {σ ι R : Type*} [CommSemiring R]
    [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ) :
    booleanVariableChoiceSum fixed s left right =
      MvPolynomial.finsetMonomial fixed *
        ∏ i ∈ s,
          (MvPolynomial.X (left i) + MvPolynomial.X (right i) :
            MvPolynomial σ R) := by
  rw [booleanVariableChoiceSum, ← Finset.mul_sum, ← Finset.prod_add]

/-- Every real squarefree finite-set monomial is multivariate real stable. -/
theorem mvRealStable_finsetMonomial {σ : Type*} (A : Finset σ) :
    MvRealStable
      (MvPolynomial.finsetMonomial A : MvPolynomial σ ℝ) := by
  unfold MvPolynomial.finsetMonomial
  apply MvRealStable.finset_prod
  intro i hi
  exact MvRealStable.X i

/-- Every Boolean variable-choice sum is multivariate real stable. -/
theorem booleanVariableChoiceSum_mvRealStable {σ ι : Type*}
    [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ) :
    MvRealStable (booleanVariableChoiceSum fixed s left right :
      MvPolynomial σ ℝ) := by
  rw [booleanVariableChoiceSum_eq]
  apply (mvRealStable_finsetMonomial fixed).mul
  apply MvRealStable.finset_prod
  intro i hi
  exact MvRealStable.X_add_X (left i) (right i)

/-- Every real Boolean variable-choice sum has nonnegative coefficients. -/
theorem booleanVariableChoiceSum_hasNonnegCoeffs {σ ι : Type*}
    [DecidableEq ι] (fixed : Finset σ) (s : Finset ι)
    (left right : ι → σ) :
    MvPolynomial.HasNonnegCoeffs
      (booleanVariableChoiceSum fixed s left right : MvPolynomial σ ℝ) := by
  rw [booleanVariableChoiceSum_eq]
  apply MvPolynomial.HasNonnegCoeffs.mul
  · unfold MvPolynomial.finsetMonomial
    apply MvPolynomial.HasNonnegCoeffs.prod
    intro i hi
    exact MvPolynomial.HasNonnegCoeffs.X i
  · apply MvPolynomial.HasNonnegCoeffs.prod
    intro i hi
    exact (MvPolynomial.HasNonnegCoeffs.X (left i)).add
      (MvPolynomial.HasNonnegCoeffs.X (right i))

/-- The independently weighted subset expansion choosing a left or right
variable from every pair. -/
def weightedBooleanVariableChoiceSum {σ ι R : Type*} [CommSemiring R]
    [DecidableEq ι] (fixed : Finset σ) (s : Finset ι)
    (left right : ι → σ) (leftWeight rightWeight : ι → R) :
    MvPolynomial σ R :=
  ∑ t ∈ s.powerset,
    MvPolynomial.finsetMonomial fixed *
      ((∏ i ∈ t,
          MvPolynomial.C (leftWeight i) * MvPolynomial.X (left i)) *
        ∏ i ∈ s \ t,
          MvPolynomial.C (rightWeight i) * MvPolynomial.X (right i))

/-- The weighted Boolean choice sum factors into independently weighted
homogeneous linear forms. -/
theorem weightedBooleanVariableChoiceSum_eq
    {σ ι R : Type*} [CommSemiring R] [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ)
    (leftWeight rightWeight : ι → R) :
    weightedBooleanVariableChoiceSum fixed s left right
        leftWeight rightWeight =
      MvPolynomial.finsetMonomial fixed *
        ∏ i ∈ s,
          (MvPolynomial.C (leftWeight i) * MvPolynomial.X (left i) +
            MvPolynomial.C (rightWeight i) * MvPolynomial.X (right i)) := by
  rw [weightedBooleanVariableChoiceSum, ← Finset.mul_sum,
    ← Finset.prod_add]

/-- Unit weights recover the unweighted Boolean choice sum. -/
theorem weightedBooleanVariableChoiceSum_one
    {σ ι R : Type*} [CommSemiring R] [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ) :
    weightedBooleanVariableChoiceSum fixed s left right
        (fun _ => 1) (fun _ => 1) =
      booleanVariableChoiceSum (R := R) fixed s left right := by
  simp [weightedBooleanVariableChoiceSum, booleanVariableChoiceSum]

/-- Nonnegative independent weights give the weighted Boolean choice sum
nonnegative coefficients. -/
theorem weightedBooleanVariableChoiceSum_hasNonnegCoeffs
    {σ ι : Type*} [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ)
    (leftWeight rightWeight : ι → Real)
    (hleft : ∀ i ∈ s, 0 ≤ leftWeight i)
    (hright : ∀ i ∈ s, 0 ≤ rightWeight i) :
    MvPolynomial.HasNonnegCoeffs
      (weightedBooleanVariableChoiceSum fixed s left right
        leftWeight rightWeight) := by
  rw [weightedBooleanVariableChoiceSum_eq]
  apply MvPolynomial.HasNonnegCoeffs.mul
  · unfold MvPolynomial.finsetMonomial
    apply MvPolynomial.HasNonnegCoeffs.prod
    intro i hi
    exact MvPolynomial.HasNonnegCoeffs.X i
  · apply MvPolynomial.HasNonnegCoeffs.prod
    intro i hi
    exact ((MvPolynomial.HasNonnegCoeffs.C (hleft i hi)).mul
      (MvPolynomial.HasNonnegCoeffs.X (left i))).add
        ((MvPolynomial.HasNonnegCoeffs.C (hright i hi)).mul
          (MvPolynomial.HasNonnegCoeffs.X (right i)))

/-- Nonnegative, nontrivial independent weights preserve multivariate real
stability of the Boolean variable-choice sum. -/
theorem weightedBooleanVariableChoiceSum_mvRealStable
    {σ ι : Type*} [DecidableEq ι]
    (fixed : Finset σ) (s : Finset ι) (left right : ι → σ)
    (leftWeight rightWeight : ι → Real)
    (hleft : ∀ i ∈ s, 0 ≤ leftWeight i)
    (hright : ∀ i ∈ s, 0 ≤ rightWeight i)
    (hpos : ∀ i ∈ s, 0 < leftWeight i ∨ 0 < rightWeight i) :
    MvRealStable (weightedBooleanVariableChoiceSum fixed s left right
      leftWeight rightWeight) := by
  rw [weightedBooleanVariableChoiceSum_eq]
  apply (mvRealStable_finsetMonomial fixed).mul
  apply MvRealStable.finset_prod
  intro i hi
  exact MvRealStable.C_mul_X_add_C_mul_X (left i) (right i)
    (hleft i hi) (hright i hi) (hpos i hi)

/-- The standard normal form for a Boolean swap orbit: inactive swaps
contribute a power of two and active swaps contribute independent choices. -/
def booleanSwapOrbitNormalForm {σ ι R : Type*} [CommSemiring R]
    [DecidableEq ι] (inactive : ℕ) (fixed : Finset σ) (s : Finset ι)
    (left right : ι → σ) : MvPolynomial σ R :=
  MvPolynomial.C ((2 : R) ^ inactive) *
    booleanVariableChoiceSum fixed s left right

/-- The Boolean swap-orbit normal form is a monomial, a power of two, and a
product of the active linear factors. -/
theorem booleanSwapOrbitNormalForm_eq {σ ι R : Type*} [CommSemiring R]
    [DecidableEq ι] (inactive : ℕ) (fixed : Finset σ) (s : Finset ι)
    (left right : ι → σ) :
    booleanSwapOrbitNormalForm inactive fixed s left right =
      MvPolynomial.C ((2 : R) ^ inactive) *
        MvPolynomial.finsetMonomial fixed *
          ∏ i ∈ s,
            (MvPolynomial.X (left i) + MvPolynomial.X (right i) :
              MvPolynomial σ R) := by
  rw [booleanSwapOrbitNormalForm, booleanVariableChoiceSum_eq, mul_assoc]

/-- Every real Boolean swap-orbit normal form is multivariate real stable. -/
theorem booleanSwapOrbitNormalForm_mvRealStable {σ ι : Type*}
    [DecidableEq ι] (inactive : ℕ) (fixed : Finset σ) (s : Finset ι)
    (left right : ι → σ) :
    MvRealStable (booleanSwapOrbitNormalForm inactive fixed s left right :
      MvPolynomial σ ℝ) := by
  apply (booleanVariableChoiceSum_mvRealStable fixed s left right).C_mul
  exact pow_ne_zero inactive (by norm_num)

/-- Every real Boolean swap-orbit normal form has nonnegative
coefficients. -/
theorem booleanSwapOrbitNormalForm_hasNonnegCoeffs {σ ι : Type*}
    [DecidableEq ι] (inactive : ℕ) (fixed : Finset σ) (s : Finset ι)
    (left right : ι → σ) :
    MvPolynomial.HasNonnegCoeffs
      (booleanSwapOrbitNormalForm inactive fixed s left right :
        MvPolynomial σ ℝ) := by
  unfold booleanSwapOrbitNormalForm
  exact (MvPolynomial.HasNonnegCoeffs.C (by positivity)).mul
    (booleanVariableChoiceSum_hasNonnegCoeffs fixed s left right)

/-- A Boolean swap-orbit normal form with independent weights on the two
choices at every pair.  An inactive pair contributes the sum of its weights,
while an active pair contributes the corresponding weighted linear form. -/
def weightedBooleanSwapOrbitNormalForm
    {σ ι R : Type*} [CommSemiring R] [DecidableEq ι]
    (inactive : Finset ι) (fixed : Finset σ) (active : Finset ι)
    (left right : ι → σ) (leftWeight rightWeight : ι → R) :
    MvPolynomial σ R :=
  MvPolynomial.C (∏ i ∈ inactive, (leftWeight i + rightWeight i)) *
    weightedBooleanVariableChoiceSum fixed active left right
      leftWeight rightWeight

/-- The weighted orbit normal form factors into its inactive scalar factors,
fixed monomial, and weighted active linear factors. -/
theorem weightedBooleanSwapOrbitNormalForm_eq
    {σ ι R : Type*} [CommSemiring R] [DecidableEq ι]
    (inactive : Finset ι) (fixed : Finset σ) (active : Finset ι)
    (left right : ι → σ) (leftWeight rightWeight : ι → R) :
    weightedBooleanSwapOrbitNormalForm inactive fixed active left right
        leftWeight rightWeight =
      MvPolynomial.C (∏ i ∈ inactive, (leftWeight i + rightWeight i)) *
        MvPolynomial.finsetMonomial fixed *
          ∏ i ∈ active,
            (MvPolynomial.C (leftWeight i) * MvPolynomial.X (left i) +
              MvPolynomial.C (rightWeight i) * MvPolynomial.X (right i)) := by
  rw [weightedBooleanSwapOrbitNormalForm,
    weightedBooleanVariableChoiceSum_eq, mul_assoc]

/-- Unit pair weights recover the ordinary Boolean swap-orbit normal form. -/
theorem weightedBooleanSwapOrbitNormalForm_one
    {σ ι R : Type*} [CommSemiring R] [DecidableEq ι]
    (inactive : Finset ι) (fixed : Finset σ) (active : Finset ι)
    (left right : ι → σ) :
    weightedBooleanSwapOrbitNormalForm inactive fixed active left right
        (fun _ => 1) (fun _ => 1) =
      booleanSwapOrbitNormalForm (R := R) inactive.card fixed active
        left right := by
  rw [weightedBooleanSwapOrbitNormalForm, booleanSwapOrbitNormalForm,
    weightedBooleanVariableChoiceSum_one]
  apply congrArg (fun q : MvPolynomial σ R =>
    q * booleanVariableChoiceSum fixed active left right)
  apply congrArg MvPolynomial.C
  norm_num

/-- Nonnegative independent pair weights give the weighted Boolean orbit
normal form nonnegative coefficients. -/
theorem weightedBooleanSwapOrbitNormalForm_hasNonnegCoeffs
    {σ ι : Type*} [DecidableEq ι]
    (inactive : Finset ι) (fixed : Finset σ) (active : Finset ι)
    (left right : ι → σ) (leftWeight rightWeight : ι → Real)
    (hleft : ∀ i ∈ inactive ∪ active, 0 ≤ leftWeight i)
    (hright : ∀ i ∈ inactive ∪ active, 0 ≤ rightWeight i) :
    MvPolynomial.HasNonnegCoeffs
      (weightedBooleanSwapOrbitNormalForm inactive fixed active
        left right leftWeight rightWeight) := by
  unfold weightedBooleanSwapOrbitNormalForm
  apply MvPolynomial.HasNonnegCoeffs.mul
  · apply MvPolynomial.HasNonnegCoeffs.C
    apply Finset.prod_nonneg
    intro i hi
    exact add_nonneg (hleft i (by simp [hi])) (hright i (by simp [hi]))
  · apply weightedBooleanVariableChoiceSum_hasNonnegCoeffs
    · intro i hi
      exact hleft i (by simp [hi])
    · intro i hi
      exact hright i (by simp [hi])

/-- The weighted Boolean orbit is stable when every inactive scalar factor is
nonzero and every active linear factor has nonnegative, nontrivial weights. -/
theorem weightedBooleanSwapOrbitNormalForm_mvRealStable
    {σ ι : Type*} [DecidableEq ι]
    (inactive : Finset ι) (fixed : Finset σ) (active : Finset ι)
    (left right : ι → σ) (leftWeight rightWeight : ι → Real)
    (hinactive : ∀ i ∈ inactive, leftWeight i + rightWeight i ≠ 0)
    (hleft : ∀ i ∈ active, 0 ≤ leftWeight i)
    (hright : ∀ i ∈ active, 0 ≤ rightWeight i)
    (hpos : ∀ i ∈ active,
      0 < leftWeight i ∨ 0 < rightWeight i) :
    MvRealStable (weightedBooleanSwapOrbitNormalForm inactive fixed active
      left right leftWeight rightWeight) := by
  apply (weightedBooleanVariableChoiceSum_mvRealStable fixed active left right
    leftWeight rightWeight hleft hright hpos).C_mul
  exact Finset.prod_ne_zero_iff.mpr hinactive

/-- Nonnegative, nontrivial weights at every pair satisfy the precise
hypotheses of weighted Boolean-orbit stability. -/
theorem weightedBooleanSwapOrbitNormalForm_mvRealStable_of_nonneg
    {σ ι : Type*} [DecidableEq ι]
    (inactive : Finset ι) (fixed : Finset σ) (active : Finset ι)
    (left right : ι → σ) (leftWeight rightWeight : ι → Real)
    (hleft : ∀ i ∈ inactive ∪ active, 0 ≤ leftWeight i)
    (hright : ∀ i ∈ inactive ∪ active, 0 ≤ rightWeight i)
    (hpos : ∀ i ∈ inactive ∪ active,
      0 < leftWeight i ∨ 0 < rightWeight i) :
    MvRealStable (weightedBooleanSwapOrbitNormalForm inactive fixed active
      left right leftWeight rightWeight) := by
  apply weightedBooleanSwapOrbitNormalForm_mvRealStable inactive fixed active
    left right leftWeight rightWeight
  · intro i hi
    have hiunion : i ∈ inactive ∪ active := by simp [hi]
    rcases hpos i hiunion with hli | hri
    · exact ne_of_gt (add_pos_of_pos_of_nonneg hli (hright i hiunion))
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (hleft i hiunion) hri)
  · intro i hi
    exact hleft i (by simp [hi])
  · intro i hi
    exact hright i (by simp [hi])
  · intro i hi
    exact hpos i (by simp [hi])

end

end RealRooted
