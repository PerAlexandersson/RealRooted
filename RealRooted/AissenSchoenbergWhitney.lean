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

/-- The zero sequence is Toeplitz totally nonnegative.  This is harmless for
PF sequences, but it means the strict real-rootedness conclusion in ASW must
exclude the zero polynomial. -/
theorem toeplitzTotallyNonnegative_zero :
    ToeplitzTotallyNonnegative (fun _ : ℕ => (0 : ℝ)) := by
  intro n rows cols hrows hcols
  by_cases hn : n = 0
  · subst n
    norm_num [toeplitzMinor]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmatrix :
        toeplitzMinor (fun _ : ℕ => (0 : ℝ)) rows cols = 0 := by
      ext i j
      simp [toeplitzMinor, toeplitzEntry]
    rw [hmatrix]
    have hne : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    rw [Matrix.det_zero hne]

theorem isPolyaFrequencySequence_zero :
    IsPolyaFrequencySequence (fun _ : ℕ => (0 : ℝ)) :=
  toeplitzTotallyNonnegative_zero

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
Toeplitz total nonnegativity of the coefficient sequence of a nonzero
polynomial should imply that the polynomial has only real nonpositive roots. -/
def aissenSchoenbergWhitneyForwardStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    p ≠ 0 →
    HasNonnegCoeffs p →
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    IsRealRooted p ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Equivalent forward ASW statement with the redundant nonnegative-coefficient
hypothesis removed. -/
def aissenSchoenbergWhitneyForwardNoNonnegStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    p ≠ 0 →
    IsPolyaFrequencySequence (fun n => p.coeff n) →
    IsRealRooted p ∧ ∀ r ∈ p.roots, r ≤ 0

/-- The current forward ASW statement implies the no-extra-nonnegativity
formulation, since PF coefficients are already nonnegative. -/
theorem aissenSchoenbergWhitneyForwardNoNonneg_of_forward
    (hASW : aissenSchoenbergWhitneyForwardStatement) :
    aissenSchoenbergWhitneyForwardNoNonnegStatement := by
  intro p hp0 hpf
  exact hASW hp0 (hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff hpf) hpf

/-- The no-extra-nonnegativity formulation implies the current forward ASW
statement. -/
theorem aissenSchoenbergWhitneyForward_of_noNonneg
    (hASW : aissenSchoenbergWhitneyForwardNoNonnegStatement) :
    aissenSchoenbergWhitneyForwardStatement := by
  intro p hp0 _ hpf
  exact hASW hp0 hpf

/-- The two forward ASW interfaces are equivalent. -/
theorem aissenSchoenbergWhitneyForward_iff_noNonneg :
    aissenSchoenbergWhitneyForwardStatement ↔
      aissenSchoenbergWhitneyForwardNoNonnegStatement := by
  constructor
  · exact aissenSchoenbergWhitneyForwardNoNonneg_of_forward
  · exact aissenSchoenbergWhitneyForward_of_noNonneg

/-- Without a nonzero hypothesis, the forward ASW interface would force the
zero polynomial to be real-rooted, contrary to the strict local definition of
`IsRealRooted`. -/
theorem not_aissenSchoenbergWhitneyForward_without_nonzero :
    ¬ (∀ ⦃p : ℝ[X]⦄,
      HasNonnegCoeffs p →
      IsPolyaFrequencySequence (fun n => p.coeff n) →
      IsRealRooted p ∧ ∀ r ∈ p.roots, r ≤ 0) := by
  intro h
  have hnn : HasNonnegCoeffs (0 : ℝ[X]) := by
    intro n
    simp
  have hpf : IsPolyaFrequencySequence (fun n => (0 : ℝ[X]).coeff n) := by
    have hcoeff :
        (fun n => (0 : ℝ[X]).coeff n) = (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp
    rw [hcoeff]
    exact @isPolyaFrequencySequence_zero
  exact (h hnn hpf).1.1 rfl

/-- Planning stub for the reverse Aissen--Schoenberg--Whitney theorem. -/
def aissenSchoenbergWhitneyReverseStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    IsRealRooted p →
    (∀ r ∈ p.roots, r ≤ 0) →
    IsPolyaFrequencySequence (fun n => p.coeff n)

end RealRooted
