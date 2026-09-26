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
name = "RealRooted.Challenges.Hadamard.SchurSzegoComposition"

[[definitions]]
name = "RealRooted.Challenges.Hadamard.HadamardProduct"

[[definitions]]
name = "RealRooted.Challenges.Hadamard.PolyaFrequencyPolynomial"

[[definitions]]
name = "RealRooted.Challenges.Hadamard.ToeplitzMatrix"

[[definitions]]
name = "RealRooted.Challenges.Hadamard.MatrixHadamardProduct"

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

This page collects checked closure theorems for coefficientwise products.  A
fixed-degree Schur–Szegő composition with a Pólya-frequency factor preserves
real splitting up to zero.  The finite Pólya–Schur theorem characterizes
nonnegative multiplier sequences by their Jensen polynomials.  The
Garloff–Wagner theorem preserves proper position under Hadamard product.
Maló's theorem says that the entrywise product of two totally nonnegative
lower-triangular Toeplitz matrices remains totally nonnegative when the
diagonal sequences have finite support.  Polynomial-value Pólya-frequency
sequences are also closed under multiplication of their defining polynomials.

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

/-- Challenge-facing name for the fixed-degree Schur--Szego composition. -/
noncomputable abbrev SchurSzegoComposition (n : Nat) (f g : ℝ[X]) : ℝ[X] :=
  schurSzegoComp n f g

/-- Challenge-facing name for coefficientwise Hadamard product. -/
noncomputable abbrev HadamardProduct (p q : ℝ[X]) : ℝ[X] :=
  hadamardProduct p q

/-- Challenge-facing name for polynomial-side Pólya-frequency. -/
abbrev PolyaFrequencyPolynomial (p : ℝ[X]) : Prop :=
  IsPFPolynomial p

/-- The lower-triangular Toeplitz matrix associated with a sequence. -/
abbrev ToeplitzMatrix (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  toeplitz a

/-- Entrywise (Hadamard) product of two matrices. -/
abbrev MatrixHadamardProduct (M N : Matrix ℕ ℕ ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun i j => M i j * N i j

/-- Challenge-facing name for a nonnegative-coefficient proper-position pair. -/
abbrev NonnegativeProperPositionPair (f g : ℝ[X]) : Prop :=
  HasNonnegCoeffs f ∧ HasNonnegCoeffs g ∧ StrictInterl f g

/-- Fixed-degree Schur--Szego composition theorem. -/
theorem finiteSchurSzegoComposition :
    ∀ {n : ℕ} {f p : ℝ[X]},
      PolyaFrequencyPolynomial f →
      f.natDegree ≤ n →
      p.natDegree ≤ n →
      p.Splits →
        SchurSzegoComposition n f p = 0 ∨ (SchurSzegoComposition n f p).Splits :=
  RealRooted.finiteSchurSzegoComposition

/-- Finite Polya--Schur theorem in the nonnegative-coefficient convention. -/
theorem finitePolyaSchur_nonneg :
    ∀ {n : ℕ} {gamma : ℕ → ℝ},
      (∀ k, 0 ≤ gamma k) →
        (IsFiniteMultiplierSequence n gamma ↔
          PolyaFrequencyPolynomial (jensenPolynomial n gamma)) :=
  RealRooted.finitePolyaSchur_nonneg

/-- Garloff--Wagner proper-position Hadamard theorem. -/
theorem garloffWagnerHadamardNonnegInterl :
    ∀ {f g p q : ℝ[X]},
      NonnegativeProperPositionPair f g →
      NonnegativeProperPositionPair p q →
      Interl (HadamardProduct f p) (HadamardProduct g q) :=
  fun hfg hpq =>
    RealRooted.garloffWagnerHadamardNonnegInterl
      hfg.1 hfg.2.1 hpq.1 hpq.2.1 hfg.2.2 hpq.2.2

/-- Maló's theorem for finite-support Pólya-frequency sequences: the
entrywise product of their lower-triangular Toeplitz matrices is totally
nonnegative.  Polynomial coefficients encode the finite-support condition. -/
theorem maloToeplitzHadamard {p q : ℝ[X]}
    (hp : (ToeplitzMatrix p.coeff).IsTotallyNonneg)
    (hq : (ToeplitzMatrix q.coeff).IsTotallyNonneg) :
    (MatrixHadamardProduct (ToeplitzMatrix p.coeff)
      (ToeplitzMatrix q.coeff)).IsTotallyNonneg :=
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
