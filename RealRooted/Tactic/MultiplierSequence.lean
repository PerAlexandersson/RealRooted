module

public import RealRooted.MultiplierSequence

/-!
# Multiplier-sequence family lemmas

Pointwise lifts of Jensen-polynomial and finite multiplier-sequence facts to
families indexed by natural numbers.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Pointwise nonnegative sequences have Jensen polynomials with nonnegative
coefficients. -/
theorem jensenPolynomial_sequence_nonneg
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hGamma : ∀ i k, 0 ≤ Gamma i k) :
    ∀ i : Nat, HasNonnegCoeffs (jensenPolynomial (N i) (Gamma i)) := fun i =>
  hasNonnegCoeffs_jensenPolynomial (hGamma i)

/-- Every Jensen polynomial in the family has degree at most its level. -/
theorem jensenPolynomial_sequence_natDegree_le
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ) :
    ∀ i : Nat, (jensenPolynomial (N i) (Gamma i)).natDegree ≤ N i := fun i =>
  natDegree_jensenPolynomial_le (N i) (Gamma i)

/-- Pointwise nonnegative finite multiplier sequences have PF Jensen
polynomials. -/
theorem jensenPolynomial_sequence_pf_of_finite_multiplier
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i)) := fun i =>
  isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
    (hGamma i) (hmult i)

/-- Pointwise finite PF multiplier sequences have PF Jensen polynomials. -/
theorem jensenPolynomial_sequence_pf_of_finite_pf_multiplier
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hmult : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i)) := fun i =>
  isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence (hmult i)

/-- Finite multiplier sequences remain so after pointwise lowering the degree
bound. -/
theorem finiteMultiplierSequence_sequence_mono
    {M N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hMN : ∀ i : Nat, M i ≤ N i)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFiniteMultiplierSequence (M i) (Gamma i) := fun i =>
  IsFiniteMultiplierSequence.mono (hMN i) (hmult i)

/-- Finite PF multiplier sequences remain so after pointwise lowering the
degree bound. -/
theorem finitePFMultiplierSequence_sequence_mono
    {M N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hMN : ∀ i : Nat, M i ≤ N i)
    (hmult : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (M i) (Gamma i) := fun i =>
  IsFinitePFMultiplierSequence.mono (hMN i) (hmult i)

/-- Pointwise products of finite multiplier-sequence families preserve the
same degree bounds. -/
theorem finiteMultiplierSequence_sequence_mul
    {N : Nat → ℕ} {Gamma Delta : Nat → ℕ → ℝ}
    (hGamma : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i))
    (hDelta : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Delta i)) :
    ∀ i : Nat, IsFiniteMultiplierSequence (N i)
      (fun k => Gamma i k * Delta i k) := fun i =>
  IsFiniteMultiplierSequence.mul (hGamma i) (hDelta i)

/-- Pointwise products of finite PF multiplier-sequence families preserve the
same degree bounds. -/
theorem finitePFMultiplierSequence_sequence_mul
    {N : Nat → ℕ} {Gamma Delta : Nat → ℕ → ℝ}
    (hGamma : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i))
    (hDelta : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Delta i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i)
      (fun k => Gamma i k * Delta i k) := fun i =>
  IsFinitePFMultiplierSequence.mul (hGamma i) (hDelta i)

/-- A pointwise nonnegative finite multiplier-sequence family preserves the PF
cone at the same levels. -/
theorem finitePFMultiplierSequence_sequence_of_finite_multiplier
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i) := fun i =>
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence
    (hGamma i) (hmult i)

/-- At levels at most two, pointwise nonnegative sequences with PF Jensen
polynomials are finite multiplier sequences. -/
theorem finiteMultiplierSequence_sequence_le_two_of_jensen_pf
    {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hN : ∀ i : Nat, N i ≤ 2)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hjensen : ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))) :
    ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i) := fun i =>
  isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    (hN i) (hGamma i) (hjensen i)

/-- At levels at most two, pointwise nonnegative sequences with PF Jensen
polynomials are finite PF multiplier sequences. -/
theorem finitePFMultiplierSequence_sequence_le_two_of_jensen_pf
    {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hN : ∀ i : Nat, N i ≤ 2)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hjensen : ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i) := fun i =>
  isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    (hN i) (hGamma i) (hjensen i)

end Tactic
end RealRooted

