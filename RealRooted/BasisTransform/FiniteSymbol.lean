module

public import RealRooted.MultivariateStability
public import RealRooted.BorceaBranden.UnivariateFiniteSymbol
public import RealRooted.BasisTransform
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
public import RealRooted.PFPolynomial

/-!
# Finite algebraic symbols of polynomial basis transforms

This module computes the finite Borcea--Branden symbol of the linear map
sending `X ^ n` to a prescribed polynomial `P n`.  Stability of this explicit
symbol gives degree-bounded real-rootedness preservation, and coefficientwise
nonnegativity of the relevant basis images upgrades the conclusion to the
Polya-frequency property.
-/

public section

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.BorceaBranden

private theorem hasNonnegCoeffs_basisTransform_of_natDegree_le
    {P : ℕ → ℝ[X]} {d : ℕ} {p : ℝ[X]}
    (hP : ∀ k, k ≤ d → HasNonnegCoeffs (P k))
    (hpdeg : p.natDegree ≤ d) (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (Polynomial.basisTransform P p) := by
  intro j
  rw [Polynomial.coeff_basisTransform, Polynomial.sum_def]
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg (hp k)
  apply hP k
  exact (Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hk)).trans hpdeg

/-- The finite algebraic symbol of the basis transform `X ^ n ↦ P n` is
the binomially weighted homogenization of the basis images `P n`. -/
theorem finiteAlgebraicSymbol_basisTransformₗ (P : ℕ → ℝ[X]) (d : ℕ) :
    finiteAlgebraicSymbol d (Polynomial.basisTransformₗ P) =
      ∑ k ∈ Finset.range (d + 1),
        MvPolynomial.C (Nat.choose d k : ℝ) *
          polynomialInFirstMv (P k) *
            MvPolynomial.X (1 : Fin 2) ^ (d - k) := by
  classical
  simp [finiteAlgebraicSymbol]

/-- Stability of the explicit finite symbol of a basis transform gives
degree-bounded preservation of real-rootedness, allowing the zero output. -/
theorem basisTransform_splits_or_zero_of_finiteSymbol_stable
    {P : ℕ → ℝ[X]} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (∑ k ∈ Finset.range (d + 1),
          MvPolynomial.C (Nat.choose d k : ℝ) *
            polynomialInFirstMv (P k) *
              MvPolynomial.X (1 : Fin 2) ^ (d - k))))
    (hpdeg : p.natDegree ≤ d) (hp : p.Splits) :
    Polynomial.basisTransform P p = 0 ∨
      (Polynomial.basisTransform P p).Splits := by
  have hfinite : MvUpperHalfPlaneStable
      (complexifyMv
        (finiteAlgebraicSymbol d (Polynomial.basisTransformₗ P))) := by
    rw [finiteAlgebraicSymbol_basisTransformₗ]
    exact hSymbol
  simpa using
    (finiteSymbol_preservesRealRootedUpTo hfinite hpdeg hp)

/-- If the explicit finite symbol is stable and the basis images in its degree
box have nonnegative coefficients, the basis transform sends every PF
polynomial in that box to a PF polynomial. -/
theorem basisTransform_isPF_of_finiteSymbol_stable
    {P : ℕ → ℝ[X]} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (∑ k ∈ Finset.range (d + 1),
          MvPolynomial.C (Nat.choose d k : ℝ) *
            polynomialInFirstMv (P k) *
              MvPolynomial.X (1 : Fin 2) ^ (d - k))))
    (hP : ∀ k, k ≤ d → HasNonnegCoeffs (P k))
    (hpdeg : p.natDegree ≤ d) (hp : IsPFPolynomial p) :
    IsPFPolynomial (Polynomial.basisTransform P p) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hasNonnegCoeffs_basisTransform_of_natDegree_le
      hP hpdeg hp.hasNonnegCoeffs
  · apply basisTransform_splits_or_zero_of_finiteSymbol_stable
      hSymbol hpdeg
    exact hp.splits

end RealRooted.BorceaBranden
