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
name = "RealRooted.toeplitz"
module = "RealRooted.AissenSchoenbergWhitneyBase"
label = "Toeplitz matrix of a sequence"

[[definitions]]
name = "RealRooted.gwSchurProduct"
module = "RealRooted.GarloffWagner.Algebra"
label = "Factorial Schur product"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.finiteSchurSzegoComposition"
label = "Schur–Szegő composition preserves real-rootedness"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.finitePolyaSchur_nonneg"
label = "Finite Pólya–Schur theorem"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.garloffWagnerHadamardNonnegInterl"
label = "Hadamard products preserve interlacing"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.maloToeplitzHadamard"
label = "Maló: Hadamard products of totally nonnegative Toeplitz matrices"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.polynomialValueProductPolyaFrequency"
label = "Products of polynomial value sequences are PF"

[[theorems]]
name = "RealRooted.gwHadamardProductPF"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Garloff–Wagner: Hadamard products of PF polynomials are PF"

[[theorems]]
name = "RealRooted.gwHadamardProductInterl_of_strictInterl"
module = "RealRooted.GarloffWagner.Hadamard"
label = "Garloff–Wagner: Hadamard products preserve interlacing"

[[theorems]]
name = "RealRooted.gwSchurProductInterl"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Garloff–Wagner, Theorem 12: the Schur product preserves interlacing"
-->

<!-- realrooted-catalog-content -->
# Hadamard products and Schur–Szegő composition

Schur–Szegő composition and coefficientwise products preserve several
real-rootedness and interlacing classes. This page also covers the finite
Pólya–Schur theorem and Maló’s theorem on totally nonnegative Toeplitz
matrices.

The results of Garloff and Wagner for PF polynomials (real-rooted with
nonnegative coefficients):

- **PF closure:** the Hadamard product `sum_k a_k b_k x^k` of two PF
  polynomials is PF.
- **Interlacing:** if `f ≪ g` and `p ≪ q`, then `f ∗ p ≪ g ∗ q`, where `∗`
  is the Hadamard product.
- **Schur product (Theorem 12):** the factorial Schur product, with
  coefficients `k! a_k b_k`, preserves interlacing in its first argument.

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
theorem finiteSchurSzegoComposition :
    ∀ {n : ℕ} {f p : ℝ[X]},
      IsPFPolynomial f →
      f.natDegree ≤ n →
      p.natDegree ≤ n →
      p.Splits →
        schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  RealRooted.finiteSchurSzegoComposition

/-- Finite Polya--Schur theorem in the nonnegative-coefficient convention. -/
theorem finitePolyaSchur_nonneg :
    ∀ {n : ℕ} {gamma : ℕ → ℝ},
      (∀ k, 0 ≤ gamma k) →
        (IsFiniteMultiplierSequence n gamma ↔
          IsPFPolynomial (jensenPolynomial n gamma)) :=
  RealRooted.finitePolyaSchur_nonneg

/-- Garloff--Wagner interlacing theorem for coefficientwise products. -/
theorem garloffWagnerHadamardNonnegInterl :
    ∀ {f g p q : ℝ[X]},
      HasNonnegCoeffs f → HasNonnegCoeffs g →
      HasNonnegCoeffs p → HasNonnegCoeffs q →
      StrictInterl f g → StrictInterl p q →
      Interl (hadamardProduct f p) (hadamardProduct g q) :=
  RealRooted.gwHadamardProductNonnegInterl

/-- Maló's theorem for finite-support Pólya-frequency sequences: the
entrywise product of their lower-triangular Toeplitz matrices is totally
nonnegative.  Polynomial coefficients encode the finite-support condition. -/
theorem maloToeplitzHadamard {p q : ℝ[X]}
    (hp : (toeplitz p.coeff).IsTotallyNonneg)
    (hq : (toeplitz q.coeff).IsTotallyNonneg) :
    (Matrix.of fun i j =>
      toeplitz p.coeff i j * toeplitz q.coeff i j).IsTotallyNonneg :=
  RealRooted.maloToeplitzHadamard_isTotallyNonneg hp hq

/-- Polynomial-value PF sequences are closed under polynomial multiplication.
This includes zero inputs; for nonzero inputs the proof derives the canonical
Euler-numerator certificates through causal differences. -/
theorem polynomialValueProductPolyaFrequency
    {f g : ℝ[X]} (hf : IsPolyaFreqSeq (polynomialValueSeq f))
    (hg : IsPolyaFreqSeq (polynomialValueSeq g)) :
    IsPolyaFreqSeq (polynomialValueSeq (f * g)) :=
  hf.pointwise_mul_of_polynomialValue hg

end Hadamard
end Challenges
end RealRooted
