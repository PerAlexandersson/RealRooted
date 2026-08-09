import RealRooted.Basic
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
import RealRooted.MultivariateStability

/-!
# Borcea--Branden finite-symbol challenge entry point

Human statement:
https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

This file records Lean-facing interfaces for the finite-degree algebraic
symbol theorem. The complex classification includes the rank-at-most-one
alternative from Theorem 1.1; outside that alternative, preservation is
equivalent to stability of the algebraic symbol. These are statement
interfaces, not proofs of the classification. Tactic-specific
coefficient-bidiagonal specializations live in `RealRooted.Tactic.FiniteSymbolPF`.
-/

open Polynomial BigOperators

namespace RealRooted
namespace Challenges
namespace BorceaBranden

noncomputable section

/-! ## Complex finite-symbol classification -/

/-- A complex linear operator on a coordinate-wise degree box preserves
upper-half-plane stability, allowing the zero output. -/
def PreservesComplexStabilityOnDegreeBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∀ f, MvUpperHalfPlaneStable f.1 →
    MvUpperHalfPlaneStableOrZero (T f)

/-- The exceptional branch in Borcea--Brändén Theorem 1.1: the operator has a
one-dimensional representation with a stable spanning polynomial. This also
includes the zero operator by taking the functional to be zero. -/
def HasStableRankOneRepresentation
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∃ (α : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] ℂ)
      (P : MvPolynomial σ ℂ),
    MvUpperHalfPlaneStable P ∧ ∀ f, T f = (α f) • P

/-- Borcea--Brändén, Theorem 1.1: a complex linear operator on a finite degree
box preserves upper-half-plane stability if and only if it has a stable
rank-at-most-one representation or its finite algebraic symbol is stable.

This is the main classification challenge. It is an explicit proposition, not
a proved theorem. -/
def finiteComplexSymbolClassificationStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] (κ : σ → ℕ)
      (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ),
    PreservesComplexStabilityOnDegreeBox κ T ↔
      HasStableRankOneRepresentation κ T ∨
        MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T)

/-- Admitted Borcea--Brändén finite complex-symbol classification.

This is the single explicit admission for the classification challenge tracked
in issue #356. It is not a checked proof. -/
theorem finiteComplexSymbolClassification :
    finiteComplexSymbolClassificationStatement := by
  sorry

/-- Outside the rank-at-most-one alternative, the main classification has the
familiar form: an operator preserves stability if and only if its algebraic
symbol is stable. This remains an explicit challenge proposition. -/
def finiteComplexSymbolIffStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] (κ : σ → ℕ)
      (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ),
    ¬HasStableRankOneRepresentation κ T →
      (PreservesComplexStabilityOnDegreeBox κ T ↔
        MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T))

/-- Admitted non-rank-one form of the complex finite-symbol classification.

This is a formal consequence of the single admitted classification theorem,
not an additional admission. -/
theorem finiteComplexSymbolIff :
    finiteComplexSymbolIffStatement := by
  intro σ _ κ T hrank
  rw [finiteComplexSymbolClassification σ κ T]
  simp only [hrank, false_or]

/-! ## Real univariate application interface -/

/-- Regard a univariate polynomial as a bivariate polynomial in the first
variable. -/
def polynomialInFirstMv (p : ℝ[X]) : MvPolynomial (Fin 2) ℝ :=
  p.eval₂ (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.X (0 : Fin 2))

/-- The finite algebraic symbol `T((x + y)^d)` of a real linear operator on
univariate polynomials, expanded through the monomial basis in degree `d`. -/
def finiteAlgebraicSymbol (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    MvPolynomial (Fin 2) ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    MvPolynomial.C (Nat.choose d k : ℝ) *
      polynomialInFirstMv (T ((X : ℝ[X]) ^ k)) *
        (MvPolynomial.X (1 : Fin 2)) ^ (d - k)

/-- Degree-bounded preservation of real-rootedness, allowing the zero output. -/
def PreservesRealRootedUpTo
    (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ {p : ℝ[X]}, p.natDegree ≤ d → p.Splits → T p = 0 ∨ (T p).Splits

/-- The positive-symbol sufficiency direction of Borcea--Branden,
Theorem 1.2(b), specialized to one real source variable of degree at most `d`.

The paper's symbol is `T((z + w)^d)`, which is `finiteAlgebraicSymbol d T`
after expanding in the monomial basis. The complex counterpart is
Theorem 1.1(b). The statement below records only the application-facing
implication to real-rooted inputs and zero-aware outputs, not the converse,
the signed-symbol branch, or the low-rank alternative. -/
def finiteSymbolTheoremStatement : Prop :=
  ∀ {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]},
    MvUpperHalfPlaneStable (complexifyMv (finiteAlgebraicSymbol d T)) →
      PreservesRealRootedUpTo d T

/- The checked witness lives in
`RealRooted.BorceaBranden.Applications.RealUnivariateSymbol`; importing it here
would create an application/core cycle. -/

/-- Direct use of the finite-symbol theorem interface. -/
theorem preservesRealRootedUpTo_of_finiteSymbol
    (hBB : finiteSymbolTheoremStatement)
    {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hstable :
      MvUpperHalfPlaneStable (complexifyMv (finiteAlgebraicSymbol d T))) :
    PreservesRealRootedUpTo d T :=
  hBB hstable

end

end BorceaBranden
end Challenges
end RealRooted
