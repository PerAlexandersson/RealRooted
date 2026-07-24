import RealRooted.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Pólya-frequency sequences

This file defines the Toeplitz matrix of a real sequence and the
Pólya-frequency property used by the Aissen--Schoenberg--Whitney theorem.
Keeping these definitions separate lets minor constructions depend on the
basic interface without importing the full ASW development.
-/

open Matrix

namespace RealRooted

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

/-- A sequence is a Pólya-frequency sequence. -/
def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop :=
  (toeplitz a).IsTotallyNonneg

/-- The zero sequence is Pólya-frequency. -/
theorem IsPolyaFreqSeq_zero :
    IsPolyaFreqSeq (fun _ : ℕ => (0 : ℝ)) := by
  simp [IsPolyaFreqSeq]

/-- A Pólya-frequency sequence has nonnegative entries, by its `1 × 1`
Toeplitz minors. -/
protected nonrec theorem IsPolyaFreqSeq.nonneg
    (ha : IsPolyaFreqSeq a) (k : ℕ) :
    0 ≤ a k := by
  simpa [IsPolyaFreqSeq] using ha.nonneg k 0

end RealRooted
