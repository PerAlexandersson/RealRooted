import RealRooted.GarloffWagner.Hadamard
import RealRooted.GarloffWagner.Theorem12
import RealRooted.Hadamard
import RealRooted.PolynomialValueEulerNumerator.Product.PF.Causal

/-!
# Hadamard challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hadamard-products"
authors = ["Maló", "Pólya", "Schur", "Wagner", "Garloff"]
years = [1895, 1914, 1992, 1996]

[[definitions]]
name = "RealRooted.schurSzegoComp"
module = "RealRooted.Hadamard.Basic"
label = "Schur–Szegő composition"

[[definitions]]
name = "RealRooted.hadamardProduct"
module = "RealRooted.Hadamard.Product"
label = "Hadamard product"

[[definitions]]
name = "RealRooted.IsPFPolynomial"
module = "RealRooted.PFPolynomial"
label = "PF polynomial"

[[definitions]]
name = "RealRooted.polynomialValueSeq"
module = "RealRooted.AissenSchoenbergWhitneyBase"
label = "Values of a polynomial at 0, 1, 2, …"

[[definitions]]
name = "RealRooted.gwSchurProduct"
module = "RealRooted.GarloffWagner.Algebra"
label = "Factorial Schur product"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.schurSzegoComp_eq_zero_or_splits"
label = "Schur–Szegő composition preserves real-rootedness"

[[theorems]]
name = """RealRooted.Challenges.Hadamard.\
isFiniteMultiplierSequence_iff_isPFPolynomial_jensenPolynomial"""
label = "Finite Pólya–Schur theorem"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.interl_hadamardProduct_of_strictInterl"
label = "Garloff–Wagner: Hadamard products preserve interlacing"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.isPolyaFreqSeq_mul_coeff"
label = "Maló: termwise products of finite PF sequences are PF"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.isPolyaFreqSeq_polynomialValueSeq_mul"
label = "Products of polynomial value sequences are PF"

[[theorems]]
name = "RealRooted.gwHadamardProductPF"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Garloff–Wagner: Hadamard products of PF polynomials are PF"

[[theorems]]
name = "RealRooted.gwSchurProductInterl"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Garloff–Wagner: the Schur product preserves interlacing"
-->

<!-- realrooted-catalog-content -->
# Hadamard products and Schur–Szegő composition

Schur–Szegő composition and coefficientwise products preserve several
real-rootedness and interlacing classes. This page also covers the finite
Pólya–Schur theorem and Maló’s theorem: the termwise product of two finite
Pólya frequency sequences is again a Pólya frequency sequence. Equivalently,
the entrywise product of their totally nonnegative Toeplitz matrices is
totally nonnegative.

If the value sequences $f(0), f(1), f(2), \dotsc$ and $g(0), g(1), g(2), \dotsc$
of two real polynomials are Pólya frequency sequences, then so is the value
sequence of $fg$.

The results of Garloff and Wagner for PF polynomials (real-rooted with
nonnegative coefficients):

- **PF closure:** the Hadamard product $\sum_k a_k b_k x^k$ of two PF
  polynomials is PF.
- **Interlacing:** if $f \ll g$ and $p \ll q$, then $f \ast p \ll g \ast q$, where $\ast$
  is the Hadamard product.
- **Schur product:** the factorial Schur product, with
  coefficients $k!\, a_k b_k$, preserves interlacing in its first argument.

## References

E. Maló, “Note sur les équations algébriques dont toutes les racines sont
réelles,” *Journal de Mathématiques Spéciales* 4 (1895), 7–10; G. Pólya and
I. Schur, “Über zwei Arten von Faktorenfolgen in der Theorie der algebraischen
Gleichungen,” *Journal für die reine und angewandte Mathematik* 144 (1914),
89–113; D. G. Wagner, “Total positivity of Hadamard products,” *Journal of
Mathematical Analysis and Applications* 163 (1992), 459–483; J. Garloff and
D. G. Wagner, “Hadamard products of stable polynomials are stable,” *Journal
of Mathematical Analysis and Applications* 202 (1996), 797–809.  See the
[Hadamard-product overview](https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems)
and [Schur–Szegő composition](https://www.symmetricfunctions.com/realRooted.htm#schurSzegoComposition)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

Human statements:

* Hadamard product theorems:
  https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems
* Schur--Szego composition:
  https://www.symmetricfunctions.com/realRooted.htm#schurSzegoComposition
* Polya-frequency sequences:
  https://www.symmetricfunctions.com/polyaFrequency.htm#aissenSchoenbergWhitney

Original publications include:

* G. Polya and I. Schur, "Ueber zwei Arten von Faktorenfolgen in der Theorie
  der algebraischen Gleichungen", J. Reine Angew. Math. 144 (1914), 89--113.
* D. G. Wagner, "Total positivity of Hadamard products", J. Math. Anal. Appl.
  163 (1992), 459--483.
* J. Garloff and D. G. Wagner, "Hadamard products of stable polynomials are
  stable", J. Math. Anal. Appl. 202 (1996), 797--809.

This module exposes the main theorem interfaces.  The reduction graph,
Hurwitz-matrix routes, and low-degree support lemmas remain in
`RealRooted.Hadamard`.

The polynomial-value PF product theorem below is restricted to sequences of
the form `n ↦ p(n)`; it is not a closure theorem for arbitrary PF sequences.
Its PF convention includes the zero polynomial and permits nonpositive, rather
than strictly negative, roots.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Hadamard

/-- Fixed-degree Schur--Szego composition theorem. -/
theorem schurSzegoComp_eq_zero_or_splits {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  RealRooted.finiteSchurSzegoComposition hf hfdeg hpdeg hsplits

/-- Finite Polya--Schur theorem in the nonnegative-coefficient convention. -/
theorem isFiniteMultiplierSequence_iff_isPFPolynomial_jensenPolynomial {n : ℕ}
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFiniteMultiplierSequence n gamma ↔ IsPFPolynomial (jensenPolynomial n gamma) :=
  RealRooted.finitePolyaSchur_nonneg hgamma

/-- Garloff--Wagner interlacing theorem for coefficientwise products. -/
theorem interl_hadamardProduct_of_strictInterl {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : StrictInterl f g) (hpq : StrictInterl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) :=
  RealRooted.gwHadamardProductNonnegInterl hf hg hp hq hfg hpq

/-- Maló's theorem for finite-support Pólya-frequency sequences: their termwise
product is again a Pólya-frequency sequence.  Equivalently, the entrywise
product of their lower-triangular Toeplitz matrices is totally nonnegative.
Polynomial coefficients encode the finite-support condition. -/
theorem isPolyaFreqSeq_mul_coeff {p q : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) (hq : IsPolyaFreqSeq q.coeff) :
    IsPolyaFreqSeq (fun n => p.coeff n * q.coeff n) := by
  have h := RealRooted.maloToeplitzHadamard_isTotallyNonneg hp hq
  rw [← RealRooted.toeplitz_pointwise_mul] at h
  exact h

/-- Polynomial-value PF sequences are closed under polynomial multiplication.
This includes zero inputs; for nonzero inputs the proof derives the canonical
Euler-numerator certificates through causal differences. -/
theorem isPolyaFreqSeq_polynomialValueSeq_mul {f g : ℝ[X]}
    (hf : IsPolyaFreqSeq (polynomialValueSeq f))
    (hg : IsPolyaFreqSeq (polynomialValueSeq g)) :
    IsPolyaFreqSeq (polynomialValueSeq (f * g)) :=
  RealRooted.isPolyaFreqSeq_polynomialValueSeq_mul_of_polyaFreqSeq hf hg

end Hadamard
end Challenges
end RealRooted
