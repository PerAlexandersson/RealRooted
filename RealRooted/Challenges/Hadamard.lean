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

[[definitions]]
name = "RealRooted.hadamardProduct"
module = "RealRooted.HadamardProduct"

[[definitions]]
name = "RealRooted.IsPFPolynomial"
module = "RealRooted.PFPolynomial"

[[definitions]]
name = "RealRooted.toeplitz"
module = "RealRooted.AissenSchoenbergWhitneyBase"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.finiteSchurSzegoComposition"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.finitePolyaSchur_nonneg"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.garloffWagnerHadamardNonnegInterl"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.maloToeplitzHadamard"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.polynomialValueProductPolyaFrequency"
-->

<!-- realrooted-catalog-content -->
# Hadamard products and Schur–Szegő composition

Schur–Szegő composition and coefficientwise products preserve several
real-rootedness and interlacing classes. The page also includes the finite
Pólya–Schur theorem and Maló’s total-nonnegativity theorem for Toeplitz
matrices.

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
