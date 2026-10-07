import RealRooted.GarloffWagner.Hadamard
import RealRooted.GarloffWagner.Theorem12
import RealRooted.Hadamard
import RealRooted.Hadamard.FiniteReflection
import RealRooted.Hadamard.SchurSzegoMultiplicity
import RealRooted.Hadamard.SchurSzegoSigns
import RealRooted.MultiplierSequence.PolyaSchur.Schur
import RealRooted.PolynomialValueEulerNumerator.Product.PF.Causal
import RealRooted.PolynomialValueEulerNumerator.Product.Brenti

/-!
# Hadamard challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hadamard-products"
authors = ["Maló", "Pólya", "Schur", "Brenti", "Wagner", "Garloff", "Kostov", "Shapiro", "Brändén",
  "Ferroni", "Jochemko"]
years = [1895, 1914, 1989, 1992, 1996, 2006, 2010, 2024]

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
name = "RealRooted.factorialHadamardProduct"
module = "RealRooted.GarloffWagner.Algebra"
label = "Factorial Hadamard product"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.schurSzegoComp_eq_zero_or_splits"
label = "Schur–Szegő composition preserves real-rootedness"

[[theorems]]
name = "RealRooted.rootMultiplicity_schurSzegoComp"
module = "RealRooted.Hadamard.SchurSzegoMultiplicity"
label = "Kostov–Shapiro: exact multiplicity of the root −ab of a Schur–Szegő composition"

[[theorems]]
name = "RealRooted.schurSzegoComp_roots_sign_counts_of_roots_neg"
module = "RealRooted.Hadamard.SchurSzegoSigns"
label = "Kostov–Shapiro: composition with a negative-rooted polynomial preserves root signs"

[[theorems]]
name = """RealRooted.Challenges.Hadamard.\
isFiniteMultiplierSequence_iff_isPFPolynomial_jensenPolynomial"""
label = "Finite Pólya–Schur theorem"

[[theorems]]
name = """RealRooted.Challenges.Hadamard.\
isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg"""
label = "Finite Pólya–Schur theorem, alternating signs"

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
name = "RealRooted.IsPFPolynomial.polynomialValueEulerNumerator_of_roots_mem_Icc"
module = "RealRooted.PolynomialValueEulerNumerator.Product.Brenti"
label = "Brenti: zeros in [−1, 0] give a PF Euler numerator"

[[theorems]]
name = "RealRooted.IsPFPolynomial.hadamardProduct"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Garloff–Wagner: Hadamard products of PF polynomials are PF"

[[theorems]]
name = "RealRooted.Interl.factorialHadamardProduct_right"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Garloff–Wagner: the factorial Hadamard product preserves interlacing"

[[theorems]]
name = "RealRooted.Challenges.Hadamard.factorialHadamardProduct_eq_zero_or_splits"
label = "Schur: the factorial product preserves real-rootedness"
-->

<!-- realrooted-catalog-content -->
# Hadamard products and Schur–Szegő composition

Schur–Szegő composition and coefficientwise products preserve several
real-rootedness and interlacing classes. This page also covers the finite
Pólya–Schur theorem and Maló’s theorem: the termwise product of two finite
Pólya frequency sequences is again a Pólya frequency sequence. Equivalently,
the entrywise product of their totally nonnegative Toeplitz matrices is
totally nonnegative.

**Theorem** (Kostov–Shapiro; Kostov). Let $f$ and $g$ have degree $n$, let
$a \neq 0$ be a root of $f$ of multiplicity $m$ and $b \neq 0$ a root of $g$ of
multiplicity $l$, with $m + l \geq n$. Then $-ab$ is a root of the Schur–Szegő
composition $f *_n g$ of multiplicity exactly $m + l - n$; in particular it is not a
root when $m + l = n$. The roots must be nonzero, as Kostov (2010) points out.
If moreover $f$ is real-rooted and $g$ has only negative roots, then $f *_n g$ is
real-rooted with as many positive, zero and negative roots as $f$.

**Finite Pólya–Schur theorem.** Fix $n \geq 0$ and let $T_\gamma(x^k) =
\gamma_k x^k$. Then $T_\gamma$ maps every real-rooted polynomial of degree at
most $n$ to zero or a real-rooted polynomial if and only if the Jensen
polynomial $\sum_{k=0}^n \binom{n}{k} \gamma_k x^k$ is zero or has only real
zeros, all in one of the half-lines $(-\infty, 0]$ and $[0, \infty)$. The
formalization covers two sign patterns: if every $\gamma_k \geq 0$, the zeros
lie in $(-\infty, 0]$; if every $(-1)^k \gamma_k \geq 0$, they lie in
$[0, \infty)$.

If the value sequences $f(0), f(1), f(2), \dotsc$ and $g(0), g(1), g(2), \dotsc$
of two real polynomials are Pólya frequency sequences, then so is the value
sequence of $fg$ (Wagner). The Lean proof follows Brändén, Ferroni and
Jochemko, who derive Wagner's theorem from the fact that a bilinear map on
homogeneous bivariate polynomials, built from a harmonic substitution, preserves
stability.

**Theorem (Brenti).** If every zero of $p$ lies in $[-1, 0]$ and its leading coefficient
is positive, then the numerator $W$ of $\sum_{n \ge 0} p(n)\, x^n = W(x)/(1-x)^{\deg p + 1}$
is real-rooted with nonnegative coefficients. For $p = x + a$ the numerator is
$a + (1-a)x$; Wagner's product theorem handles the general case.

The results of Garloff and Wagner for PF polynomials (real-rooted with
nonnegative coefficients):

- **PF closure:** the Hadamard product $\sum_k a_k b_k x^k$ of two PF
  polynomials is PF.
- **Interlacing:** if $f \ll g$ and $p \ll q$, then $f \ast p \ll g \ast q$, where $\ast$
  is the Hadamard product.
- **Factorial Hadamard product:** the factorial Hadamard product (Schur's
  factorial product), with coefficients $k!\, a_k b_k$, preserves interlacing in
  its first argument.

**Theorem (Schur).** If $f = \sum_k a_k x^k$ is real-rooted and
$g = \sum_k b_k x^k$ is real-rooted with all zeros of one sign, then the
factorial Hadamard product $\sum_k k!\, a_k b_k x^k$ is zero or real-rooted.

## References

E. Maló, “Note sur les équations algébriques dont toutes les racines sont
réelles,” *Journal de Mathématiques Spéciales* 4 (1895), 7–10; G. Pólya and
I. Schur, “Über zwei Arten von Faktorenfolgen in der Theorie der algebraischen
Gleichungen,” *Journal für die reine und angewandte Mathematik* 144 (1914),
89–113; D. G. Wagner, “Total positivity of Hadamard products,” *Journal of
Mathematical Analysis and Applications* 163 (1992), 459–483; J. Garloff and
D. G. Wagner, “Hadamard products of stable polynomials are stable,” *Journal
of Mathematical Analysis and Applications* 202 (1996), 797–809; P. Brändén,
L. Ferroni and K. Jochemko, “Preservation of inequalities under Hadamard
products,” arXiv:2408.12386 (2024). V. Kostov and B.
Shapiro, “On the Schur–Szegő composition of polynomials,” *C. R. Math. Acad. Sci.
Paris* 343 (2006), 81–86; V. P. Kostov, “Interlacing properties and the Schur–Szegő
composition,” *Functional Analysis and Other Mathematics* 3 (2010), 65–74.  See the
[Hadamard-product overview](https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems),
[Schur–Szegő composition](https://www.symmetricfunctions.com/realRooted.htm#schurSzegoComposition),
and the [finite multiplier criterion](https://www.symmetricfunctions.com/realRooted.htm#finiteMultiplierSequenceCriterion)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

Human statements:

* Hadamard product theorems:
  https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems
* Schur--Szego composition:
  https://www.symmetricfunctions.com/realRooted.htm#schurSzegoComposition
* Polya-frequency sequences:
  https://www.symmetricfunctions.com/polyaFrequency.htm#aissenSchoenbergWhitney
* Finite multiplier criterion:
  https://www.symmetricfunctions.com/realRooted.htm#finiteMultiplierSequenceCriterion

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

/-- Finite Pólya--Schur theorem for sequences with `(-1)^k γ_k ≥ 0`: the
Jensen polynomial is zero or real-rooted with all zeros in `[0, ∞)`. -/
theorem isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg {n : ℕ}
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ (-1) ^ k * gamma k) :
    IsFiniteMultiplierSequence n gamma ↔
      (jensenPolynomial n gamma = 0 ∨ (jensenPolynomial n gamma).Splits) ∧
        ∀ r ∈ (jensenPolynomial n gamma).roots, 0 ≤ r :=
  RealRooted.isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg hgamma

/-- Schur's factorial product theorem: if `f` is real-rooted and `g` is
real-rooted with all zeros of one sign, then `∑ k! aₖ bₖ xᵏ` is zero or
real-rooted. -/
theorem factorialHadamardProduct_eq_zero_or_splits {f g : ℝ[X]} (hf : f.Splits)
    (hg : g.Splits) (hsign : (∀ r ∈ g.roots, r ≤ 0) ∨ ∀ r ∈ g.roots, 0 ≤ r) :
    factorialHadamardProduct f g = 0 ∨ (factorialHadamardProduct f g).Splits :=
  RealRooted.factorialHadamardProduct_eq_zero_or_splits hf hg hsign

/-- Garloff--Wagner interlacing theorem for coefficientwise products. -/
theorem interl_hadamardProduct_of_strictInterl {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : StrictInterl f g) (hpq : StrictInterl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) :=
  RealRooted.StrictInterl.interl_hadamardProduct hf hg hp hq hfg hpq

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
