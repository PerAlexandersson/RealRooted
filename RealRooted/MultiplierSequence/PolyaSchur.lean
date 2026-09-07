import RealRooted.Hadamard.Grace
import RealRooted.MultiplierSequence.Infinite

/-!
# Infinite Pólya--Schur consequences

This leaf module combines the algebraic infinite multiplier-sequence API with
the checked finite Pólya--Schur theorem. It characterizes nonnegative
multiplier sequences and PF multiplier sequences by all of their Jensen
polynomials.

The classical entire-function and Laguerre--Pólya classification requires
analytic infrastructure not present here and is intentionally left to a
separate follow-up project, tracked by GitHub issue #563; no analytic statement
scaffold is introduced.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A nonnegative sequence is a multiplier sequence exactly when all of its
Jensen polynomials are PF. -/
theorem isMultiplierSequence_iff_jensenPolynomial_isPF
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsMultiplierSequence gamma ↔
      ∀ n : ℕ, IsPFPolynomial (jensenPolynomial n gamma) := by
  constructor
  · intro hmult n
    exact (finitePolyaSchur_nonneg hgamma).1 (hmult.finite n)
  · intro hjensen n
    exact (finitePolyaSchur_nonneg hgamma).2 (hjensen n)

/-- The PF and real-rootedness-preserving conventions agree precisely for
pointwise nonnegative infinite sequences. -/
theorem isPFMultiplierSequence_iff_multiplierSequence_and_nonneg
    {gamma : ℕ → ℝ} :
    IsPFMultiplierSequence gamma ↔
      IsMultiplierSequence gamma ∧ ∀ k, 0 ≤ gamma k := by
  constructor
  · intro hgamma
    have hnonneg : ∀ k, 0 ≤ gamma k := hgamma.nonneg
    refine ⟨(isMultiplierSequence_iff_jensenPolynomial_isPF hnonneg).2 ?_,
      hnonneg⟩
    exact isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hgamma
  · rintro ⟨hgamma, hnonneg⟩
    exact hgamma.toPF hnonneg

/-- A sequence preserves the polynomial PF cone in every degree exactly when
all of its Jensen polynomials are PF. -/
theorem isPFMultiplierSequence_iff_jensenPolynomial_isPF
    {gamma : ℕ → ℝ} :
    IsPFMultiplierSequence gamma ↔
      ∀ n : ℕ, IsPFPolynomial (jensenPolynomial n gamma) := by
  constructor
  · exact isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
  · intro hjensen
    have hnonneg : ∀ k, 0 ≤ gamma k := by
      intro k
      have hk := (hjensen k).hasNonnegCoeffs k
      simpa [coeff_jensenPolynomial] using hk
    exact ((isMultiplierSequence_iff_jensenPolynomial_isPF hnonneg).2
      hjensen).toPF hnonneg

/-- Forward shifts also preserve the PF multiplier-sequence convention. -/
theorem IsPFMultiplierSequence.shift {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (r : ℕ) :
    IsPFMultiplierSequence (fun k => gamma (k + r)) := by
  rw [isPFMultiplierSequence_iff_multiplierSequence_and_nonneg] at hgamma ⊢
  exact ⟨hgamma.1.shift r, fun k => hgamma.2 (k + r)⟩

/-- PF multiplier sequences are log-concave at every adjacent triple. -/
theorem IsPFMultiplierSequence.logConcave {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (k : ℕ) :
    gamma k * gamma (k + 2) ≤ gamma (k + 1) ^ 2 := by
  have hshift := hgamma.shift k
  have hlog :=
    (finitePFMultiplierSequence_three_logConcave (hshift.finite 3)).1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlog

end RealRooted
