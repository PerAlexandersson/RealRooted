import RealRooted.GammaRealRoots
import RealRooted.InterlacingSequenceBasic
import RealRooted.WeightedSum

open Polynomial Finset
open scoped BigOperators

/-!
# Hoster--Stump Chow polynomial challenge entry point

Human statement:
https://arxiv.org/abs/2508.15538

Original publication: E. Hoster and C. Stump, "Chow polynomials of
simplicial posets with positive h-vector are real-rooted", arXiv:2508.15538.

This module records the Lean-facing target statements for issue #99.  It is a
strategy surface rather than a full simplicial-poset formalization: the final
Chow, dual Chow, and augmented Chow polynomials are supplied by an abstract
model, while the Section 3 refined polynomial family is supplied as a
four-parameter family `p n k S T`.

Section 2 backend map:

* interlacing sequences: `IsInterlacingSeq`, `IsInterlacingSeq0Nonneg`;
* nonnegative finite sums under a common right bound: `prec_weightedSum_right`,
  `prec_sum_right`, and `isRealRooted_sum_of_commonInterleaver`;
* common-left finite sums under compatibility data: `prec_weightedSum_left`;
* the `f << g -> g << X * f` shift: `prec_mul_X_of_prec_of_nonneg` and
  `prec0_mul_X_of_prec0`;
* gamma real-rootedness transfer: `gammaRealRootedIffPolynomialRealRootedNonpos`;
* missing backend lemma for this route: adjacent-degree gamma interlacing
  transfer, recorded below as `GammaAdjacentInterlacingTransferStatement`;
* missing convenience lemmas for this route: lower, upper, moving-window, and
  `X`-shifted split partial sums of an interlacing sequence, recorded below as
  statement interfaces.

The finite checker `scripts/check_hoster_stump_chow.py` verifies the
permutation definition against the Section 3 recurrence and checks the
Theorem 3.3 diagram for small `n`.
-/

noncomputable section

namespace RealRooted
namespace Challenges
namespace HosterStump

/-- A finite set of descent positions is isolated when it has no consecutive
positions. -/
def IsIsolated (S : Finset ℕ) : Prop :=
  ∀ i : ℕ, i ∈ S → i + 1 ∉ S

/-- `S` and `T` are valid descent-set bounds for rank `n`. -/
def RefinedBounds (n : ℕ) (S T : Finset ℕ) : Prop :=
  S ⊆ T ∧ T ⊆ Finset.Icc 1 n

/-- Shift descent positions down by one after deleting the first comparison. -/
def shiftDown (S : Finset ℕ) : Finset ℕ :=
  (S.image fun i => i - 1).erase 0

/-- The refined Hoster--Stump polynomial family
`p_{n,k}^{S subset T}`. -/
abbrev RefinedChowFamily :=
  ℕ → ℕ → Finset ℕ → Finset ℕ → ℝ[X]

/-- The recursive right-hand side for the refined polynomial family. -/
def refinedRecurrenceRHS
    (p : RefinedChowFamily) (n k : ℕ) (S T : Finset ℕ) : ℝ[X] :=
  (if 1 ∈ T then
      X * ∑ j ∈ Finset.range k,
        p (n - 1) j (shiftDown S) ((shiftDown T).erase 1)
    else 0) +
    (if 1 ∉ S then
      ∑ j ∈ Finset.Icc k (n - 1),
        p (n - 1) j (shiftDown S) (shiftDown T)
    else 0)

/-- Base row of the Hoster--Stump refined recurrence. -/
def RefinedBaseRowStatement (p : RefinedChowFamily) : Prop :=
  ∀ {k : ℕ} {S T : Finset ℕ}, RefinedBounds 1 S T → IsIsolated S →
    p 1 k S T =
      if k = 0 ∧ S = ∅ then 1
      else if k = 1 ∧ T = ({1} : Finset ℕ) then X
      else 0

/-- Recursive split of `p_{n,k}^{S subset T}` into lower `X`-weighted and
upper unweighted partial sums. -/
def RefinedRecurrenceStatement (p : RefinedChowFamily) : Prop :=
  ∀ {n k : ℕ} {S T : Finset ℕ}, 2 ≤ n → k ≤ n →
    RefinedBounds n S T → IsIsolated S →
      p n k S T = refinedRecurrenceRHS p n k S T

/-- Deletion/relaxation identity
`p^{S \\ {s} subset T} = p^{S subset T} + p^{S \\ {s} subset T \\ {s}}`. -/
def RefinedDeletionRelaxationStatement (p : RefinedChowFamily) : Prop :=
  ∀ {n k s : ℕ} {S T : Finset ℕ}, s ∈ S → RefinedBounds n S T →
    p n k (S.erase s) T =
      p n k S T + p n k (S.erase s) (T.erase s)

/-- The row of refined polynomials indexed by `k = 0, ..., n`. -/
def refinedRow
    (p : RefinedChowFamily) (n : ℕ) (S T : Finset ℕ) : List ℝ[X] :=
  (List.range (n + 1)).map fun k => p n k S T

/-- Hoster--Stump Theorem 3.3, stated as the five checked families of
interlacing relations from the induction-step criterion, using the project's
zero-aware `Prec0` convention for the two zero corners. -/
def Theorem33DiagramStatement (p : RefinedChowFamily) : Prop :=
  ∀ {n : ℕ} {T : Finset ℕ}, 2 ≤ n →
    (T = Finset.Icc 1 n ∨ T = Finset.Icc 1 (n - 1)) →
      IsInterlacingSeq0Nonneg (refinedRow p n ∅ (T.erase 1)) ∧
      IsInterlacingSeq0Nonneg (refinedRow p n ∅ T) ∧
      IsInterlacingSeq0Nonneg (refinedRow p n ({1} : Finset ℕ) T) ∧
      (∀ k : ℕ, k ≤ n →
        IsInterlacingSeq0Nonneg
          [p n k ∅ (T.erase 1), p n k ∅ T,
            p n k ({1} : Finset ℕ) T]) ∧
      Prec0 (p n (n - 1) ∅ (T.erase 1))
        (p n 1 ({1} : Finset ℕ) T)

/-- Lower partial sums `[f_0, f_0 + f_1, ...]`. -/
def lowerPartialSums : List ℝ[X] → List ℝ[X]
  | [] => []
  | f :: fs => f :: (lowerPartialSums fs).map fun g => f + g

/-- Upper partial sums `[f_0 + ... + f_m, f_1 + ... + f_m, ...]`. -/
def upperPartialSums (fs : List ℝ[X]) : List ℝ[X] :=
  (lowerPartialSums fs.reverse).reverse

/-- Legacy translation of Hoster--Stump Lemma 2.3(2) to finite lists.

The source requires every sequence member to be real-rooted and uses a special
degree-at-most-one convention. `IsInterlacingSeq0Nonneg` records neither
condition, so this interface is false as stated; issue #326 tracks the
source-faithful predicate. -/
def LowerPartialSumsPreserveInterlacingStatement : Prop :=
  ∀ {fs : List ℝ[X]}, IsInterlacingSeq0Nonneg fs →
    IsInterlacingSeq0Nonneg (lowerPartialSums fs)

/-- Legacy translation of Hoster--Stump Lemma 2.3(3) to finite lists.

It has the same missing source hypotheses as the lower-partial-sum interface
and must not be used as a theorem backend. -/
def UpperPartialSumsPreserveInterlacingStatement : Prop :=
  ∀ {fs : List ℝ[X]}, IsInterlacingSeq0Nonneg fs →
    IsInterlacingSeq0Nonneg (upperPartialSums fs)

/-- Sliding sums of width `width + 1`, as in Hoster--Stump Lemma 2.3(4). -/
def movingWindowSums (width : ℕ) (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length - width)).map fun k => (fs.drop k |>.take (width + 1)).sum

/-- Legacy translation of Hoster--Stump Lemma 2.3(4), with `width` equal to
the paper's `ell`.

Each output is the sum of `width + 1` consecutive entries, and the Lean length
matches the displayed source range. The source tuple has an inconsistent final
subscript. The input predicate remains too weak for the source theorem. -/
def MovingWindowSumsPreserveInterlacingStatement : Prop :=
  ∀ {width : ℕ} {fs : List ℝ[X]}, width < fs.length →
    IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (movingWindowSums width fs)

/-- The split sums `X * (f_0 + ... + f_{k-1}) + (f_k + ... + f_m)`. -/
def xShiftedSplitSums (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length + 1)).map fun k =>
    X * (fs.take k).sum + (fs.drop k).sum

/-- Legacy translation of Hoster--Stump Lemma 2.3(5) to zero-based list
splits.

The formula and endpoint indexing match the paper, but the input predicate
omits source-required elementwise real-rootedness and the low-degree
interlacing convention. -/
def XShiftedSplitSumsPreserveInterlacingStatement : Prop :=
  ∀ {fs : List ℝ[X]}, IsInterlacingSeq0Nonneg fs →
    IsInterlacingSeq0Nonneg (xShiftedSplitSums fs)

/-- Legacy interface for Hoster--Stump Proposition 2.5 in the project
gamma-transform API.

The source assumes nonnegative coefficients for both polynomials and both
gamma polynomials, together with nonzero exact degrees. Those conditions must
be explicit because local `Prec` is defined on arbitrary real polynomials and
Lean has `natDegree 0 = 0`; issue #315 tracks the corrected statement. -/
def GammaAdjacentInterlacingTransferStatement : Prop :=
  ∀ {d : ℕ} {f g γ δ : ℝ[X]},
    γ.natDegree ≤ d / 2 →
    δ.natDegree ≤ (d + 1) / 2 →
    f.natDegree = d →
    g.natDegree = d + 1 →
    IdTransform d f = f →
    IdTransform (d + 1) g = g →
    IsGammaExpansion d f γ →
    IsGammaExpansion (d + 1) g δ →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
      (Prec f g ↔ Prec γ δ)

/-- Abstract Chow-polynomial data attached to a finite graded simplicial poset. -/
structure ChowPolynomialModel where
  rank : ℕ
  hVector : ℕ → ℝ
  chow : ℝ[X]
  dualChow : ℝ[X]
  augmentedChow : ℝ[X]
  chowGamma : ℝ[X]
  dualChowGamma : ℝ[X]
  augmentedChowGamma : ℝ[X]

/-- Positive `h`-vector hypothesis for the abstract model. -/
def PositiveHVector (M : ChowPolynomialModel) : Prop :=
  ∀ k : ℕ, k ≤ M.rank → 0 ≤ M.hVector k

/-- Nonnegative `h`-linear collapse of the refined row indexed by `T`. -/
def refinedHVectorSum
    (p : RefinedChowFamily) (n : ℕ) (T : Finset ℕ) (h : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (h k) * p n k ∅ T

/-- Hoster--Stump Lemma 3.1, isolating the three gamma-polynomial expansions. -/
def Lemma31GammaExpansionStatement
    (p : RefinedChowFamily) (M : ChowPolynomialModel) : Prop :=
  2 ≤ M.rank →
    IsGammaExpansion M.rank M.chow M.chowGamma ∧
    M.chowGamma =
      refinedHVectorSum p M.rank (Finset.Icc 1 (M.rank - 1)) M.hVector ∧
    IsGammaExpansion M.rank M.dualChow M.dualChowGamma ∧
    M.dualChowGamma =
      refinedHVectorSum p M.rank (Finset.Icc 2 M.rank) M.hVector ∧
    IsGammaExpansion (M.rank + 1) M.augmentedChow M.augmentedChowGamma ∧
    M.augmentedChowGamma =
      refinedHVectorSum p M.rank (Finset.Icc 1 M.rank) M.hVector

/-- Hoster--Stump Theorem 1.1 in the abstract model. -/
def Theorem11Statement (M : ChowPolynomialModel) : Prop :=
  PositiveHVector M →
    (M.chow ≠ 0 ∧ M.chow.Splits) ∧
      (M.augmentedChow ≠ 0 ∧ M.augmentedChow.Splits)

/-- Hoster--Stump Theorem 1.2 in the abstract model. -/
def Theorem12Statement (M : ChowPolynomialModel) : Prop :=
  PositiveHVector M →
    (M.dualChow ≠ 0 ∧ M.dualChow.Splits) ∧
      Interlaces M.dualChow M.augmentedChow

/-- Combined final challenge target for Hoster--Stump Theorems 1.1 and 1.2. -/
def MainTheoremStatement (M : ChowPolynomialModel) : Prop :=
  Theorem11Statement M ∧ Theorem12Statement M

/-- Bundle of the route ingredients which should imply the final abstract
Chow-polynomial target. -/
structure StrategyInputs
    (p : RefinedChowFamily) (M : ChowPolynomialModel) : Prop where
  baseRow : RefinedBaseRowStatement p
  recurrence : RefinedRecurrenceStatement p
  deletionRelaxation : RefinedDeletionRelaxationStatement p
  theorem33 : Theorem33DiagramStatement p
  gammaExpansions : Lemma31GammaExpansionStatement p M
  lowerPartialSums : LowerPartialSumsPreserveInterlacingStatement
  upperPartialSums : UpperPartialSumsPreserveInterlacingStatement
  movingWindowSums : MovingWindowSumsPreserveInterlacingStatement
  xShiftedSplitSums : XShiftedSplitSumsPreserveInterlacingStatement
  gammaAdjacentInterlacing : GammaAdjacentInterlacingTransferStatement

/-- Proof-template-facing statement: once the Section 2/3 route ingredients are
available for a model, the Hoster--Stump final theorem follows. -/
def StrategyImpliesMainTheoremStatement
    (p : RefinedChowFamily) (M : ChowPolynomialModel) : Prop :=
  StrategyInputs p M → MainTheoremStatement M

end HosterStump
end Challenges
end RealRooted
