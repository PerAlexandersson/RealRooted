import RealRooted.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

open Polynomial Matrix

noncomputable section

namespace RealRooted
variable {a : ℕ → ℝ}

/-- Entry of the Toeplitz matrix attached to a sequence `a₀, a₁, ...`. -/
def toeplitz (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ if j ≤ i then a (i - j) else 0

@[simp]
lemma toeplitz_apply (a : ℕ → ℝ) (i j : ℕ) : toeplitz a i j = if j ≤ i then a (i - j) else 0 := rfl

@[to_fun (attr := simp)] lemma toeplitz_zero : toeplitz 0 = 0 := by ext; simp [toeplitz]

/-- The coefficient sequence of `p` is a Polya frequency sequence. -/
def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop := (toeplitz a).IsTotallyNonneg

/-- The zero sequence is Toeplitz totally nonnegative.  This is harmless for
PF sequences, but it means the strict real-rootedness conclusion in ASW must
exclude the zero polynomial. -/
theorem IsPolyaFreqSeq_zero : IsPolyaFreqSeq (fun _ : ℕ => (0 : ℝ)) := by
  simp [IsPolyaFreqSeq]

/-- A Polya-frequency sequence has nonnegative entries, by its `1 × 1`
Toeplitz minors. -/
protected nonrec theorem IsPolyaFreqSeq.nonneg (ha : IsPolyaFreqSeq a) (k : ℕ) :
    0 ≤ a k := by simpa using ha.nonneg k 0

/-- Planning stub for the forward Aissen--Schoenberg--Whitney theorem:
Toeplitz total nonnegativity of the coefficient sequence of a polynomial implies that the polynomial
splits. -/
def aissenSchoenbergWhitneyForwardStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    IsPolyaFreqSeq p.coeff →
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Planning stub for the reverse Aissen--Schoenberg--Whitney theorem. -/
def aissenSchoenbergWhitneyReverseStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    p.Splits →
    (∀ r ∈ p.roots, r ≤ 0) →
    IsPolyaFreqSeq p.coeff

end RealRooted
