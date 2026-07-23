import Mathlib.Algebra.MvPolynomial.Basic
import RealRooted.Basic

/-!
# Borcea--Branden finite-symbol challenge entry point

Human statement:
https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

This file records a Lean-facing interface for the finite-degree algebraic
symbol theorem.  It is a statement interface: proving the theorem itself
requires a substantial multivariate stability development.  Tactic-specific
coefficient-bidiagonal specializations live in `RealRooted.Tactic.FiniteSymbolPF`.
-/

open Polynomial BigOperators

namespace RealRooted
namespace Challenges
namespace BorceaBranden

noncomputable section

/-- Complexification of a real multivariate polynomial. -/
def complexifyMv {sigma : Type*} (P : MvPolynomial sigma ℝ) :
    MvPolynomial sigma ℂ :=
  P.map Complex.ofRealHom

/-- Stability in a product of open upper half-planes. -/
def MvUpperHalfPlaneStable {sigma : Type*} (P : MvPolynomial sigma ℂ) : Prop :=
  ∀ z : sigma → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.eval z P ≠ 0

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

/-- Finite-degree Borcea--Branden algebraic-symbol theorem, as a named
classical interface. -/
def finiteSymbolTheoremStatement : Prop :=
  ∀ {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]},
    MvUpperHalfPlaneStable (complexifyMv (finiteAlgebraicSymbol d T)) →
      PreservesRealRootedUpTo d T

/-- Compatibility alias for issue notes and search. -/
abbrev borceaBrandenFiniteSymbolStatement : Prop :=
  finiteSymbolTheoremStatement

/-- Direct use of the finite-symbol theorem interface. -/
theorem preservesRealRootedUpTo_of_finiteSymbol
    (hBB : finiteSymbolTheoremStatement)
    {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hstable :
      MvUpperHalfPlaneStable (complexifyMv (finiteAlgebraicSymbol d T))) :
    PreservesRealRootedUpTo d T :=
  hBB hstable

/-- Marker for the missing multivariate-stability infrastructure needed before
the full finite-symbol classification can be proved. -/
abbrev NeedsMultivariateStabilityAPI : Prop := True

/-- Current scaffold for the Borcea--Branden finite-symbol theorem. -/
theorem finiteSymbolClassification_scaffold :
    NeedsMultivariateStabilityAPI :=
  trivial

end

end BorceaBranden
end Challenges
end RealRooted
