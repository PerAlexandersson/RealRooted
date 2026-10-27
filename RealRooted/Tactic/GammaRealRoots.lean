module

public import RealRooted.GammaRealRoots

/-!
# Gamma-real-rootedness family lemmas

This module remains an import shim for downstream users and provides pointwise
lifts of the gamma-polynomial real-rootedness and nonpositive-root bridges.
-/

public section

open Polynomial

namespace RealRooted

/-- A pointwise nonzero, split, nonnegative gamma-polynomial family within its
ambient degree bounds has pointwise nonzero split gamma transforms. -/
theorem isRealRooted_gammaTransform_sequence_of_nonneg
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hne : ∀ i : Nat, Γ i ≠ 0)
    (hsplits : ∀ i : Nat, (Γ i).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (Γ i)) :
    ∀ i : Nat, gammaTransform (d i) (Γ i) ≠ 0 ∧
      (gammaTransform (d i) (Γ i)).Splits := fun i =>
  isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (hdeg i) (hne i) (hsplits i) (hnn i)

/-- Gamma transforms of a pointwise nonnegative polynomial family have only
nonpositive roots. -/
theorem hasRootsNonpos_gammaTransform_sequence_of_nonneg
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hnn : ∀ i : Nat, HasNonnegCoeffs (Γ i)) :
    ∀ i : Nat, HasRootsNonpos (gammaTransform (d i) (Γ i)) := fun i =>
  hasRootsNonpos_gammaTransform_of_hasNonnegCoeffs (hnn i)

/-- A pointwise nonzero split gamma-polynomial family with nonpositive roots,
within its ambient degree bounds, has gamma transforms with the same
properties. -/
theorem gammaTransform_sequence_realrooted_and_roots_nonpos_of_roots_nonpos
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hne : ∀ i : Nat, Γ i ≠ 0)
    (hsplits : ∀ i : Nat, (Γ i).Splits)
    (hnp : ∀ i : Nat, HasRootsNonpos (Γ i)) :
    ∀ i : Nat,
      (gammaTransform (d i) (Γ i) ≠ 0 ∧
        (gammaTransform (d i) (Γ i)).Splits) ∧
        HasRootsNonpos (gammaTransform (d i) (Γ i)) := fun i =>
  isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
    (hdeg i) (hne i) (hsplits i) (hnp i)

/-- Within the pointwise ambient degree bounds, nonzero split gamma transforms
with nonpositive roots come from gamma polynomials with the same properties. -/
theorem gammaTransform_sequence_backward_of_natDegree_le
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hne : ∀ i : Nat, gammaTransform (d i) (Γ i) ≠ 0)
    (hsplits : ∀ i : Nat, (gammaTransform (d i) (Γ i)).Splits)
    (hnp : ∀ i : Nat, HasRootsNonpos (gammaTransform (d i) (Γ i))) :
    ∀ i : Nat, (Γ i ≠ 0 ∧ (Γ i).Splits) ∧ HasRootsNonpos (Γ i) := fun i =>
  isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    (hdeg i) (hne i) (hsplits i) (hnp i)

/-- At the minimal pointwise ambient degrees, nonzero split gamma transforms
with nonpositive roots come from gamma polynomials with the same properties. -/
theorem gammaTransform_sequence_backward_minimal
    {Γ : Nat → ℝ[X]}
    (hne : ∀ i : Nat, gammaTransform (2 * (Γ i).natDegree) (Γ i) ≠ 0)
    (hsplits : ∀ i : Nat, (gammaTransform (2 * (Γ i).natDegree) (Γ i)).Splits)
    (hnp : ∀ i : Nat,
      HasRootsNonpos (gammaTransform (2 * (Γ i).natDegree) (Γ i))) :
    ∀ i : Nat, (Γ i ≠ 0 ∧ (Γ i).Splits) ∧ HasRootsNonpos (Γ i) := fun i =>
  isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    (hne i) (hsplits i) (hnp i)

/-- For a pointwise gamma expansion within its ambient degree bounds, the
expanded family is nonzero, split, and nonpositive-rooted exactly when the
gamma-polynomial family is. -/
theorem IsGammaExpansion.isRealRooted_and_hasRootsNonpos_iff_sequence
    {d : Nat → Nat} {P Γ : Nat → ℝ[X]}
    (hγdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hexp : ∀ i : Nat, IsGammaExpansion (d i) (P i) (Γ i)) :
    ∀ i : Nat,
      (((Γ i ≠ 0 ∧ (Γ i).Splits) ∧ HasRootsNonpos (Γ i)) ↔
        ((P i ≠ 0 ∧ (P i).Splits) ∧ HasRootsNonpos (P i))) := fun i =>
  (hexp i).isRealRooted_and_hasRootsNonpos_iff (hγdeg i)

namespace Tactic

end Tactic
end RealRooted

