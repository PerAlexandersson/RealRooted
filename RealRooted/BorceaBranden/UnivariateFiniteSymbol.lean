import RealRooted.Basic
import RealRooted.MultivariateStability

/-!
# Real-univariate finite algebraic symbols

This module owns the application-facing real-univariate definitions for the
Borcea--Branden finite-symbol theorem. The complex classification backend is
independent in `RealRooted.BorceaBranden.FiniteSymbolClassification`.
-/

open Polynomial BigOperators

namespace RealRooted
namespace BorceaBranden

noncomputable section

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
end RealRooted
