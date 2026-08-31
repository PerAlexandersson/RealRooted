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
def IdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p.reflect d

@[simp] lemma IdTransform_zero (d : ℕ) :
    IdTransform d (0 : ℝ[X]) = 0 := by
  simp [IdTransform]

@[simp] lemma IdTransform_add (d : ℕ) (p q : ℝ[X]) :
    IdTransform d (p + q) = IdTransform d p + IdTransform d q := by
  simp [IdTransform]

/-- Brändén--Solus `R_d(p)(x) = (-1)^d p(-1 - x)`. -/
def RdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)


/-- Formula from Lemma 2.1 for the symmetric `I_d`-decomposition component
`a = (p - x I_d(p)) / (1 - x)`, rewritten with monic denominator `X - 1`. -/
def idDecompositionAFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X * IdTransform d p - p) /ₘ (X - 1)

/-- Formula from Lemma 2.1 for the symmetric `I_d`-decomposition component
`b = (I_d(p) - p) / (1 - x)`, rewritten with monic denominator `X - 1`. -/
def idDecompositionBFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (p - IdTransform d p) /ₘ (X - 1)

/-- Formula from Lemma 2.2 for the symmetric `R_d`-decomposition component
`\tilde a = (1 + x) p - x R_d(p)`. -/
def rdDecompositionAFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X + 1) * p - X * RdTransform d p

/-- Formula from Lemma 2.2 for the symmetric `R_d`-decomposition component
`\tilde b = R_d(p) - p`. -/
def rdDecompositionBFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  RdTransform d p - p

/-- Predicate saying that `(a,b)` is the `I_d`-decomposition of `p` in the
sense of Brändén--Solus Lemma 2.1. -/
def IsIdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  IdTransform d a = a ∧
  IdTransform (d - 1) b = b

/-- Predicate saying that `(a,b)` is the `R_d`-decomposition of `p` in the
sense of Brändén--Solus Lemma 2.2. -/
def IsRdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  RdTransform d a = a ∧
  RdTransform (d - 1) b = b

lemma hasNonnegCoeffs_IdTransform_iff {d : ℕ} {p : ℝ[X]} :
    HasNonnegCoeffs (IdTransform d p) ↔ HasNonnegCoeffs p := by
  constructor
  · intro hp n
    have h := hp (Polynomial.revAt d n)
    simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_invol] using h
  · intro hp n
    simpa [IdTransform, Polynomial.coeff_reflect] using hp (Polynomial.revAt d n)


end RealRooted
