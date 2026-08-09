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
* adjacent-degree gamma interlacing transfer:
  `GammaAdjacentInterlacingTransferStatement`;
* the lower, upper, moving-window, and `X`-shifted split formulas below.

The formerly proposed preservation interfaces for those four formulas are
false for `IsInterlacingSeq0Nonneg`.  Checked counterexamples and the separate
source-faithful relation live in `RealRooted.HosterStumpInterlacing`; this
challenge module does not expose the false propositions as theorem backends.

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

/-- Sliding sums of width `width + 1`, as in Hoster--Stump Lemma 2.3(4). -/
def movingWindowSums (width : ℕ) (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length - width)).map fun k => (fs.drop k |>.take (width + 1)).sum

/-- The split sums `X * (f_0 + ... + f_{k-1}) + (f_k + ... + f_m)`. -/
def xShiftedSplitSums (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length + 1)).map fun k =>
    X * (fs.take k).sum + (fs.drop k).sum

/-- Hoster--Stump Proposition 2.5 in the project gamma-transform API.

The source assumes nonnegative coefficients for both polynomials and both
gamma polynomials, together with nonzero exact degrees. These conditions must
be explicit because local `Prec` is defined for arbitrary real polynomials and
Lean has `natDegree 0 = 0`. Without the gamma coefficient hypotheses the
statement is false: for `d = 2` and `γ = δ = 1 - X`, the gamma transforms have
nonnegative coefficients and the required symmetry and degrees, and `Prec γ δ`
holds, but `gammaTransform 2 γ = X ^ 2 + X + 1` does not split over `ℝ`.

The separate nonzero hypotheses exclude the spurious `d = 0`, `f = 0` case
allowed by Lean's `natDegree 0 = 0`. -/
theorem GammaAdjacentInterlacingTransferStatement
    {d : ℕ} {f g γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2)
    (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfdeg : f.natDegree = d)
    (hgdeg : g.natDegree = d + 1)
    (_hfFix : IdTransform d f = f)
    (_hgFix : IdTransform (d + 1) g = g)
    (hfGamma : IsGammaExpansion d f γ)
    (hgGamma : IsGammaExpansion (d + 1) g δ)
    (_hfnn : HasNonnegCoeffs f)
    (_hgnn : HasNonnegCoeffs g)
    (hγnn : HasNonnegCoeffs γ)
    (hδnn : HasNonnegCoeffs δ) :
    Prec f g ↔ Prec γ δ := by
  change f = gammaTransform d γ at hfGamma
  change g = gammaTransform (d + 1) δ at hgGamma
  have hγ0 : γ.coeff 0 ≠ 0 := by
    rw [← coeff_ambient_gammaTransform d γ, ← hfGamma, ← hfdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hδ0 : δ.coeff 0 ≠ 0 := by
    rw [← coeff_ambient_gammaTransform (d + 1) δ, ← hgGamma, ← hgdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hg0
  rw [hfGamma, hgGamma]
  exact prec_gammaTransform_succ_iff hγdeg hδdeg hγnn hδnn hγ0 hδ0

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

end HosterStump
end Challenges
end RealRooted
