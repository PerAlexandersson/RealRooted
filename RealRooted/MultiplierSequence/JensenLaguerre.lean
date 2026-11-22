module

public import RealRooted.MultiplierSequence.JensenProduct
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
import RealRooted.MultiplierSequence.JensenConvolution
import RealRooted.Laguerre.NegativeParameters
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Laguerre versions of Jensen polynomials

The degree-dependent Laguerre auxiliary gives the factorial normalization
`d! Q` of O'Sullivan's Laguerre Jensen polynomial. Its construction uses rising
factorials and remains defined at the parameters `-1` and `-2`, where formulas
using quotients of Gamma functions require separate treatment.

Splitting of the input Jensen polynomial at a fixed degree suffices for
splitting of every Laguerre transform at parameters at least `-2`.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- Degree-dependent exponential Taylor data for the factorial-normalized
Laguerre auxiliary. -/
noncomputable def laguerreJensenCoeff (d : ℕ) (alpha : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (ascPochhammer ℝ (d - k)).eval (alpha + k + 1)

/-- The factorial-normalized Laguerre Jensen family, using rising factorials
so that the endpoint parameters require no division. -/
noncomputable def laguerreJensenPolynomial (d : ℕ) (gamma : ℕ → ℝ) (alpha : ℝ) : ℝ[X] :=
  jensenProductPolynomial d gamma (laguerreJensenCoeff d alpha)

/-- The Laguerre auxiliary's Jensen polynomial is the classical-sign
Laguerre polynomial in factorial normalization. -/
theorem jensenPolynomial_laguerreJensenCoeff (d : ℕ) (alpha : ℝ) :
    jensenPolynomial d (laguerreJensenCoeff d alpha) =
      (generalizedLaguerre d alpha).comp (-X) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_comp_neg_X, coeff_generalizedLaguerre]
  by_cases hk : k ≤ d
  · simp only [ite_eq_left hk, laguerreJensenCoeff]
    ring
  · simp [hk]

/-- The coefficient formula indexed by degree loss. Only the zero-loss term
has degree `d` in the Laguerre parameter. -/
theorem coeff_laguerreJensenPolynomial (d k : ℕ) (gamma : ℕ → ℝ) (alpha : ℝ) :
    (laguerreJensenPolynomial d gamma alpha).coeff k =
      if k ≤ d then (d.choose k : ℝ) *
        ∑ r ∈ Finset.range (k + 1),
          (k.choose r : ℝ) * (-1 : ℝ) ^ r * gamma (k - r) *
            (ascPochhammer ℝ (d - r)).eval (alpha + r + 1)
      else 0 := by
  rw [laguerreJensenPolynomial, coeff_jensenProductPolynomial,
    binomialConvolution_comm, binomialConvolution]
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [laguerreJensenCoeff]
    ring
  · rfl

/-- The Laguerre Jensen degree bound holds even at degenerate parameters. -/
theorem natDegree_laguerreJensenPolynomial_le (d : ℕ) (gamma : ℕ → ℝ) (alpha : ℝ) :
    (laguerreJensenPolynomial d gamma alpha).natDegree ≤ d :=
  natDegree_jensenProductPolynomial_le d _ _

/-- A splitting Jensen polynomial gives splitting Laguerre Jensen polynomials
throughout the extended parameter range. -/
theorem laguerreJensenPolynomial_splits {d : ℕ} {gamma : ℕ → ℝ} {alpha : ℝ}
    (hgamma : (jensenPolynomial d gamma).Splits) (halpha : -2 ≤ alpha) :
    (laguerreJensenPolynomial d gamma alpha).Splits := by
  apply jensenProductPolynomial_splits d hgamma
  rw [jensenPolynomial_laguerreJensenCoeff]
  exact (generalizedLaguerre_splits_of_neg_two_le d halpha).comp_neg_X

end RealRooted
