import RealRooted.Basic
import Mathlib.LinearAlgebra.Determinant

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-- Entry of the Toeplitz matrix attached to a sequence `a₀, a₁, ...`. -/
def toeplitzEntry (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j ≤ i then a (i - j) else 0

/-- A finite minor of the Toeplitz matrix attached to `a`. The row and column
selectors are packaged as strictly monotone maps from `Fin n`. -/
def toeplitzMinor (a : ℕ → ℝ) {n : ℕ}
    (rows cols : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => toeplitzEntry a (rows i) (cols j)

/-- Total nonnegativity of the infinite Toeplitz matrix attached to `a`,
packaged through all finite minors. This is the Polya-frequency side of the
Aissen--Schoenberg--Whitney theorem. -/
def ToeplitzTotallyNonnegative (a : ℕ → ℝ) : Prop :=
  ∀ {n : ℕ} (rows cols : Fin n → ℕ),
    StrictMono rows →
    StrictMono cols →
    0 ≤ Matrix.det (toeplitzMinor a rows cols)

/-- The coefficient sequence of `p` is a Polya frequency sequence. -/
def IsPolyaFrequencySequence (a : ℕ → ℝ) : Prop :=
  ToeplitzTotallyNonnegative a

/-- A Polya-frequency sequence has nonnegative entries, by its `1 × 1`
Toeplitz minors. -/
theorem nonneg_of_isPolyaFrequencySequence
    {a : ℕ → ℝ}
    (hpf : IsPolyaFrequencySequence a)
    (k : ℕ) :
    0 ≤ a k := by
  have hminor :
      0 ≤ Matrix.det
        (toeplitzMinor a (n := 1)
          (fun _ : Fin 1 => k) (fun _ : Fin 1 => 0)) := by
    exact hpf
      (fun _ : Fin 1 => k)
      (fun _ : Fin 1 => 0)
      (by
        intro i j hij
        fin_cases i
        fin_cases j
        simp at hij)
      (by
        intro i j hij
        fin_cases i
        fin_cases j
        simp at hij)
  simpa [toeplitzMinor, toeplitzEntry] using hminor

/-- Toeplitz total nonnegativity of the coefficient sequence already implies
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff
    {p : ℝ[X]}
    (hpf : IsPolyaFrequencySequence (fun n => p.coeff n)) :
    HasNonnegCoeffs p := by
  intro k
  exact nonneg_of_isPolyaFrequencySequence hpf k

/-- Planning stub for the forward Aissen--Schoenberg--Whitney theorem:
Toeplitz total nonnegativity of the coefficient sequence should imply that the
polynomial has only real nonpositive roots. -/
def aissenSchoenbergWhitneyForwardStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    IsRealRooted p ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Equivalent forward ASW statement with the redundant nonnegative-coefficient
hypothesis removed. -/
def aissenSchoenbergWhitneyForwardNoNonnegStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    IsRealRooted p ∧ ∀ r ∈ p.roots, r ≤ 0

/-- The current forward ASW statement implies the no-extra-nonnegativity
formulation, since PF coefficients are already nonnegative. -/
theorem aissenSchoenbergWhitneyForwardNoNonneg_of_forward
    (hASW : aissenSchoenbergWhitneyForwardStatement) :
    aissenSchoenbergWhitneyForwardNoNonnegStatement := by
  intro p hpf
  exact hASW (hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff hpf) hpf

/-- The no-extra-nonnegativity formulation implies the current forward ASW
statement. -/
theorem aissenSchoenbergWhitneyForward_of_noNonneg
    (hASW : aissenSchoenbergWhitneyForwardNoNonnegStatement) :
    aissenSchoenbergWhitneyForwardStatement := by
  intro p _ hpf
  exact hASW hpf

/-- The two forward ASW interfaces are equivalent. -/
theorem aissenSchoenbergWhitneyForward_iff_noNonneg :
    aissenSchoenbergWhitneyForwardStatement ↔
      aissenSchoenbergWhitneyForwardNoNonnegStatement := by
  constructor
  · exact aissenSchoenbergWhitneyForwardNoNonneg_of_forward
  · exact aissenSchoenbergWhitneyForward_of_noNonneg

/-- Planning stub for the reverse Aissen--Schoenberg--Whitney theorem. -/
def aissenSchoenbergWhitneyReverseStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    IsRealRooted p →
    (∀ r ∈ p.roots, r ≤ 0) →
    IsPolyaFrequencySequence (fun n => p.coeff n)

end RealRooted
