import RealRooted.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Pólya-frequency sequences

This file defines the Toeplitz matrix of a real sequence and the
Pólya-frequency property used by the Aissen--Schoenberg--Whitney theorem.
Keeping these definitions separate lets minor constructions depend on the
basic interface without importing the full ASW development.
-/

open Matrix Polynomial

namespace RealRooted

variable {a : ℕ → ℝ}

/-- Entry of the Toeplitz matrix attached to a sequence `a₀, a₁, ...`. -/
def toeplitz (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ if j ≤ i then a (i - j) else 0

@[simp]
lemma toeplitz_apply (a : ℕ → ℝ) (i j : ℕ) :
    toeplitz a i j = if j ≤ i then a (i - j) else 0 :=
  rfl

/-- The sequence obtained by evaluating a real polynomial at the
nonnegative integers. -/
def polynomialValueSeq (p : ℝ[X]) : ℕ → ℝ :=
  fun n => p.eval (n : ℝ)

@[simp]
lemma polynomialValueSeq_apply (p : ℝ[X]) (n : ℕ) :
    polynomialValueSeq p n = p.eval (n : ℝ) :=
  rfl

/-- Forward difference commutes with restricting polynomial evaluation to the
nonnegative integers. -/
theorem fwdDiff_polynomialValueSeq (p : ℝ[X]) :
    fwdDiff 1 (polynomialValueSeq p) =
      fun (n : ℕ) => fwdDiff 1 p.eval (n : ℝ) := by
  ext n
  simp [fwdDiff, polynomialValueSeq]

/-- Iterated forward differences commute with restricting polynomial
evaluation to the nonnegative integers. -/
theorem fwdDiff_iter_polynomialValueSeq (p : ℝ[X]) (k : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (polynomialValueSeq p) =
      fun (n : ℕ) => (fwdDiff (1 : ℝ))^[k] p.eval (n : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      ext n
      simp [fwdDiff, ih]

/-- Forward differences of a polynomial-value sequence vanish above the
polynomial's degree. -/
theorem fwdDiff_iter_polynomialValueSeq_eq_zero_of_natDegree_lt
    {p : ℝ[X]} {k : ℕ} (hpk : p.natDegree < k) :
    (fwdDiff (1 : ℕ))^[k] (polynomialValueSeq p) = 0 := by
  rw [fwdDiff_iter_polynomialValueSeq]
  ext n
  simpa using congr_fun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hpk) (n : ℝ)

/-- The `(natDegree + 1)`-st forward difference of a polynomial-value sequence
vanishes. -/
theorem fwdDiff_iter_polynomialValueSeq_degree_add_one_eq_zero (p : ℝ[X]) :
    (fwdDiff (1 : ℕ))^[p.natDegree + 1] (polynomialValueSeq p) = 0 :=
  fwdDiff_iter_polynomialValueSeq_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)

@[simp]
theorem polynomialValueSeq_mul (p q : ℝ[X]) :
    polynomialValueSeq (p * q) = polynomialValueSeq p * polynomialValueSeq q := by
  ext n
  simp [polynomialValueSeq]

/-- Toeplitz formation sends pointwise products of sequences to pointwise
products of their Toeplitz matrices. This is an entrywise identity, not a
total-nonnegativity closure theorem. -/
theorem toeplitz_pointwise_mul (a b : ℕ → ℝ) :
    toeplitz (a * b) =
      Matrix.of fun i j => toeplitz a i j * toeplitz b i j := by
  ext i j
  by_cases hji : j ≤ i <;> simp [toeplitz_apply, hji]

/-- Matrix form of multiplication for polynomial-value sequences. -/
theorem toeplitz_polynomialValueSeq_mul (p q : ℝ[X]) :
    toeplitz (polynomialValueSeq (p * q)) =
      Matrix.of fun i j =>
        toeplitz (polynomialValueSeq p) i j *
          toeplitz (polynomialValueSeq q) i j := by
  simpa only [polynomialValueSeq_mul] using
    toeplitz_pointwise_mul (polynomialValueSeq p) (polynomialValueSeq q)

@[to_fun (attr := simp)]
lemma toeplitz_zero : toeplitz 0 = 0 := by
  ext
  simp [toeplitz]

/-- A sequence is a Pólya-frequency sequence. -/
def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop :=
  (toeplitz a).IsTotallyNonneg

/-- The PF property for a product polynomial is exactly total nonnegativity
of the pointwise product of the two polynomial-value Toeplitz matrices. This
does not assert that the pointwise product is totally nonnegative. -/
theorem isPolyaFreqSeq_polynomialValueSeq_mul_iff (p q : ℝ[X]) :
    IsPolyaFreqSeq (polynomialValueSeq (p * q)) ↔
      (Matrix.of fun i j =>
        toeplitz (polynomialValueSeq p) i j *
          toeplitz (polynomialValueSeq q) i j).IsTotallyNonneg := by
  rw [IsPolyaFreqSeq, toeplitz_polynomialValueSeq_mul]

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
