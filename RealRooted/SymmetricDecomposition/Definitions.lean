import RealRooted.Basic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Symmetric-decomposition definitions

Foundational `I_d` and `R_d` transforms, their formula components, and the
predicates that specify the two Brändén--Solus symmetric decompositions.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Brändén--Solus `I_d(p) = x^d p(1/x)`, implemented using Mathlib's bounded
coefficient reflection operator. -/
def idTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p.reflect d

@[simp] lemma idTransform_zero (d : ℕ) :
    idTransform d (0 : ℝ[X]) = 0 := by
  simp [idTransform]

@[simp] lemma idTransform_add (d : ℕ) (p q : ℝ[X]) :
    idTransform d (p + q) = idTransform d p + idTransform d q := by
  simp [idTransform]

/-- Brändén--Solus `R_d(p)(x) = (-1)^d p(-1 - x)`. -/
def rdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)


/-- Formula from Lemma 2.1 for the symmetric `I_d`-decomposition component
`a = (p - x I_d(p)) / (1 - x)`, rewritten with monic denominator `X - 1`. -/
def idDecompositionAFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X * idTransform d p - p) /ₘ (X - 1)

/-- Formula from Lemma 2.1 for the symmetric `I_d`-decomposition component
`b = (I_d(p) - p) / (1 - x)`, rewritten with monic denominator `X - 1`. -/
def idDecompositionBFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (p - idTransform d p) /ₘ (X - 1)

/-- Formula from Lemma 2.2 for the symmetric `R_d`-decomposition component
`\tilde a = (1 + x) p - x R_d(p)`. -/
def rdDecompositionAFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X + 1) * p - X * rdTransform d p

/-- Formula from Lemma 2.2 for the symmetric `R_d`-decomposition component
`\tilde b = R_d(p) - p`. -/
def rdDecompositionBFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  rdTransform d p - p

/-- Predicate saying that `(a,b)` is the `I_d`-decomposition of `p` in the
sense of Brändén--Solus Lemma 2.1. -/
def IsIdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  idTransform d a = a ∧
  idTransform (d - 1) b = b

/-- Predicate saying that `(a,b)` is the `R_d`-decomposition of `p` in the
sense of Brändén--Solus Lemma 2.2. -/
def IsRdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  rdTransform d a = a ∧
  rdTransform (d - 1) b = b

lemma hasNonnegCoeffs_idTransform_iff {d : ℕ} {p : ℝ[X]} :
    HasNonnegCoeffs (idTransform d p) ↔ HasNonnegCoeffs p := by
  constructor
  · intro hp n
    have h := hp (Polynomial.revAt d n)
    simpa [idTransform, Polynomial.coeff_reflect, Polynomial.revAt_invol] using h
  · intro hp n
    simpa [idTransform, Polynomial.coeff_reflect] using hp (Polynomial.revAt d n)

@[deprecated (since := "2026-10-05")]
alias IdTransform := idTransform

@[deprecated (since := "2026-10-05")]
alias IdTransform_add := idTransform_add

@[deprecated (since := "2026-10-05")]
alias hasNonnegCoeffs_IdTransform_iff := hasNonnegCoeffs_idTransform_iff

end RealRooted
