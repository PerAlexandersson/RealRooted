import RealRooted.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-!
# Aissen--Schoenberg--Whitney interfaces

This file records the Toeplitz total-nonnegativity formulation of
Pólya-frequency sequences and statement-level interfaces for the classical
Aissen--Schoenberg--Whitney theorem.

Reference: M. Aissen, I. J. Schoenberg, and A. M. Whitney, *On the generating
functions of totally positive sequences. I*, J. Analyse Math. 2 (1952),
93--103.
-/

variable {a : ℕ → ℝ}

/-- Entry of the Toeplitz matrix attached to a sequence `a₀, a₁, ...`. -/
def toeplitz (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ if j ≤ i then a (i - j) else 0

@[simp]
lemma toeplitz_apply (a : ℕ → ℝ) (i j : ℕ) :
    toeplitz a i j = if j ≤ i then a (i - j) else 0 :=
  rfl

@[to_fun (attr := simp)]
lemma toeplitz_zero : toeplitz 0 = 0 := by
  ext
  simp [toeplitz]

/-- A sequence is a Polya-frequency sequence. -/
def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop :=
  (toeplitz a).IsTotallyNonneg

/-- Backward-compatible spelling for Toeplitz total nonnegativity. -/
abbrev ToeplitzTotallyNonnegative (a : ℕ → ℝ) : Prop :=
  IsPolyaFreqSeq a

/-- Backward-compatible spelling for `IsPolyaFreqSeq`. -/
abbrev IsPolyaFrequencySequence (a : ℕ → ℝ) : Prop :=
  IsPolyaFreqSeq a

/-- The zero sequence is Polya-frequency. -/
theorem isPolyaFrequencySequence_zero :
    IsPolyaFrequencySequence (fun _ : ℕ => (0 : ℝ)) := by
  simp [IsPolyaFrequencySequence, IsPolyaFreqSeq]

/-- The zero sequence is Polya-frequency, with the shorter name. -/
theorem IsPolyaFreqSeq_zero :
    IsPolyaFreqSeq (fun _ : ℕ => (0 : ℝ)) :=
  isPolyaFrequencySequence_zero

/-- A Polya-frequency sequence has nonnegative entries, by its `1 × 1`
Toeplitz minors. -/
protected nonrec theorem IsPolyaFreqSeq.nonneg
    (ha : IsPolyaFreqSeq a) (k : ℕ) :
    0 ≤ a k := by
  simpa [IsPolyaFreqSeq] using ha.nonneg k 0

/-- Compatibility spelling for nonnegativity of PF sequences. -/
theorem nonneg_of_isPolyaFrequencySequence
    {a : ℕ → ℝ}
    (hpf : IsPolyaFrequencySequence a)
    (k : ℕ) :
    0 ≤ a k :=
  IsPolyaFreqSeq.nonneg hpf k

/-- Toeplitz total nonnegativity of the coefficient sequence already implies
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff
    {p : ℝ[X]}
    (hpf : IsPolyaFrequencySequence (fun n => p.coeff n)) :
    HasNonnegCoeffs p := by
  intro k
  exact nonneg_of_isPolyaFrequencySequence hpf k

/-- Planning stub for the forward Aissen--Schoenberg--Whitney theorem:
Toeplitz total nonnegativity of the coefficient sequence of a nonzero
polynomial should imply that the polynomial has only real nonpositive roots. -/
def aissenSchoenbergWhitneyForwardStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Zero-aware forward ASW interface.  This is often the most convenient
closure form: a PF coefficient sequence gives either the zero polynomial or a
strictly real-rooted polynomial with nonpositive roots. -/
def aissenSchoenbergWhitneyForwardOrZeroStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Equivalent forward ASW statement with the redundant nonnegative-coefficient
hypothesis removed. -/
def aissenSchoenbergWhitneyForwardNoNonnegStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    p ≠ 0 →
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0

/-- The current forward ASW statement implies the no-extra-nonnegativity
formulation, since PF coefficients are already nonnegative. -/
theorem aissenSchoenbergWhitneyForwardNoNonneg_of_forward
    (hASW : aissenSchoenbergWhitneyForwardStatement) :
    aissenSchoenbergWhitneyForwardNoNonnegStatement := by
  intro p hp0 hpf
  exact ⟨⟨hp0, (hASW hpf).1⟩, (hASW hpf).2⟩

/-- The no-extra-nonnegativity formulation implies the current forward ASW
statement. -/
theorem aissenSchoenbergWhitneyForward_of_noNonneg
    (hASW : aissenSchoenbergWhitneyForwardNoNonnegStatement) :
    aissenSchoenbergWhitneyForwardStatement := by
  intro p hpf
  by_cases hp0 : p = 0
  · subst p
    simp
  · exact ⟨(hASW hp0 hpf).1.2, (hASW hp0 hpf).2⟩

/-- The two forward ASW interfaces are equivalent. -/
theorem aissenSchoenbergWhitneyForward_iff_noNonneg :
    aissenSchoenbergWhitneyForwardStatement ↔
      aissenSchoenbergWhitneyForwardNoNonnegStatement := by
  constructor
  · exact aissenSchoenbergWhitneyForwardNoNonneg_of_forward
  · exact aissenSchoenbergWhitneyForward_of_noNonneg

/-- The strict nonzero forward ASW interface implies the zero-aware one. -/
theorem aissenSchoenbergWhitneyForwardOrZero_of_forward
    (hASW : aissenSchoenbergWhitneyForwardStatement) :
    aissenSchoenbergWhitneyForwardOrZeroStatement := by
  intro p hnn hpf
  exact ⟨Or.inr (hASW hpf).1, (hASW hpf).2⟩

/-- The zero-aware forward ASW interface implies the strict nonzero one by
discarding the zero case. -/
theorem aissenSchoenbergWhitneyForward_of_orZero
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement) :
    aissenSchoenbergWhitneyForwardStatement := by
  intro p hpf
  have hnn : HasNonnegCoeffs p :=
    hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff hpf
  have h := hASW hnn hpf
  rcases h with ⟨hzero | hsplits, hroots⟩
  · subst p
    simp
  · exact ⟨hsplits, hroots⟩

/-- The strict and zero-aware forward ASW interfaces are equivalent. -/
theorem aissenSchoenbergWhitneyForward_iff_orZero :
    aissenSchoenbergWhitneyForwardStatement ↔
      aissenSchoenbergWhitneyForwardOrZeroStatement := by
  constructor
  · exact aissenSchoenbergWhitneyForwardOrZero_of_forward
  · exact aissenSchoenbergWhitneyForward_of_orZero

/-- Without a nonzero hypothesis, the forward ASW interface would force the
zero polynomial to be real-rooted, contrary to the strict local definition of
`p ≠ 0 ∧ p.Splits`. -/
theorem not_aissenSchoenbergWhitneyForward_without_nonzero :
    ¬ (∀ ⦃p : ℝ[X]⦄,
      HasNonnegCoeffs p →
      IsPolyaFrequencySequence (fun n => p.coeff n) →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) := by
  intro h
  have hnn : HasNonnegCoeffs (0 : ℝ[X]) := by
    intro n
    simp
  have hpf : IsPolyaFrequencySequence (fun n => (0 : ℝ[X]).coeff n) := by
    simpa using isPolyaFrequencySequence_zero
  have hbad := h hnn hpf
  exact hbad.1.1 rfl

/-- Planning stub for the reverse Aissen--Schoenberg--Whitney theorem.

TODO T10: formalize this statement in RealRooted.  This is the most useful ASW
direction for converting real-rooted, nonnegative-coefficient polynomials with
nonpositive roots back into Pólya-frequency coefficient sequences.
-/
def aissenSchoenbergWhitneyReverseStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    p.Splits →
    (∀ r ∈ p.roots, r ≤ 0) →
    IsPolyaFrequencySequence (fun n => p.coeff n)

end RealRooted
