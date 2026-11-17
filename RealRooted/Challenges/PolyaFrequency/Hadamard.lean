module

import RealRooted.GarloffWagner.Algebra
import RealRooted.GarloffWagner.Hadamard
import RealRooted.GarloffWagner.HurwitzStable
import RealRooted.GarloffWagner.Theorem12
import RealRooted.Hadamard.Basic
import RealRooted.Hadamard.Consequences
import RealRooted.Hadamard.Grace
import RealRooted.Hadamard.Product
import RealRooted.Hadamard.RootIntervals
import RealRooted.Hadamard.SchurSzegoMultiplicity
import RealRooted.MultiplierSequence.PolyaSchur.Schur
import RealRooted.PolynomialValueEulerNumerator.Product.PF.Causal

/-!
# Hadamard products and Schur–Szegő composition

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "hadamard-products"
formalized = "2026-07-03"
references = [
  "Schur1914",
  "Wagner1992",
  "GarloffWagner1996",
  "KostovShapiro2006",
]
authors = ["Maló", "Schur", "Wagner", "Garloff", "Kostov", "Shapiro"]
years = [1895, 1914, 1992, 1996, 2006]

[[definitions]]
name = "RealRooted.hadamardProduct"
module = "RealRooted.Hadamard.Product"
label = "Hadamard product"

[[definitions]]
name = "RealRooted.factorialHadamardProduct"
module = "RealRooted.GarloffWagner.Algebra"
label = "Factorial Hadamard product"

[[definitions]]
name = "RealRooted.schurSzegoComp"
module = "RealRooted.Hadamard.Basic"
label = "Schur–Szegő composition"

[[theorems]]
name = "RealRooted.IsPFPolynomial.hadamardProduct"
module = "RealRooted.GarloffWagner.Theorem12"
label = "Maló–Schur: Hadamard products of PF polynomials are PF"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.mul_coeff"
module = "RealRooted.Hadamard.Consequences"
label = "Termwise products of Pólya frequency coefficient sequences are Pólya frequency"

[[theorems]]
name = "RealRooted.factorialHadamardProduct_eq_zero_or_splits"
module = "RealRooted.MultiplierSequence.PolyaSchur.Schur"
label = "Schur: Σ k! aₖbₖxᵏ is real-rooted when b has roots of one sign"

[[theorems]]
name = "RealRooted.StrictInterl.interl_hadamardProduct"
module = "RealRooted.GarloffWagner.Hadamard"
label = "Garloff–Wagner: Hadamard products preserve interlacing"
headline = true

[[theorems]]
name = "RealRooted.IsHurwitzStable.hadamardProduct"
module = "RealRooted.GarloffWagner.HurwitzStable"
label = "Garloff–Wagner: Hadamard products of Hurwitz-stable polynomials are Hurwitz stable"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_polynomialValueSeq_mul_of_polyaFreqSeq"
module = "RealRooted.PolynomialValueEulerNumerator.Product.PF.Causal"
label = "Wagner: if f(0), f(1), … and g(0), g(1), … are PF, so is the value sequence of fg"

[[theorems]]
name = "RealRooted.finiteSchurSzegoComposition"
module = "RealRooted.Hadamard.Grace"
label = "Schur–Szegő composition with a PF polynomial preserves real-rootedness"

[[theorems]]
name = "RealRooted.rootMultiplicity_schurSzegoComp"
module = "RealRooted.Hadamard.SchurSzegoMultiplicity"
label = "Kostov–Shapiro: the root −ab of f *ₙ g has multiplicity exactly m + l − n"

[[theorems]]
name = "RealRooted.IsRealRootedIn.schurSzegoComp_Icc"
module = "RealRooted.Hadamard.RootIntervals"
label = "Kostov–Shapiro: roots in [−b, −a] and [−v, −u] give roots in [−bv, −au]"
-->

<!-- realrooted-catalog-content -->
# Hadamard products and Schur–Szegő composition

The Hadamard product multiplies two polynomials coefficientwise. It preserves Pólya frequency
polynomials, interlacing and Hurwitz stability, and the Schur–Szegő composition, a normalized
Hadamard product, preserves real-rootedness and maps root intervals to root intervals.

## Results

A *PF polynomial* is a real polynomial with nonnegative coefficients that is zero or
real-rooted. For $f=\sum_kf_kx^k$ and $g=\sum_kg_kx^k$ the *Hadamard product* is
$f\ast g=\sum_kf_kg_kx^k$ and the *factorial Hadamard product* is
$f\circledast g=\sum_kk!\,f_kg_kx^k$. For $f,g$ of degree at most $n$ the *Schur–Szegő
composition* is
$$
f*_ng=\sum_{k=0}^n\binom nk^{-1}f_kg_kx^k.
$$

**Theorem (Maló; Schur).** [@Schur1914] If $f$ and $g$ are PF polynomials, so is $f\ast g$.
Equivalently, the termwise product of two Pólya frequency sequences with finite support is
Pólya frequency. If $f$ is real-rooted and $g$ is real-rooted with all roots of one sign, then
$f\circledast g$ is zero or real-rooted.

**Theorem (Garloff–Wagner).** [@GarloffWagner1996] If $f\ll g$ and $p\ll q$ have nonnegative
coefficients, then $f\ast p\ll g\ast q$ unless one side is zero. If $f,g,p$ are PF and
$f\ll g$, then $f\circledast p\ll g\circledast p$ unless one side is zero. A real polynomial is
*Hurwitz stable* if it has nonnegative coefficients and no zero with positive real part; if
$f$ and $g$ are Hurwitz stable and $f\ast g\ne0$, then $f\ast g$ is Hurwitz stable
[@GarloffWagner1996, Thm. 1].

**Theorem (Wagner).** [@Wagner1992] Let $f,g$ be real polynomials. If the value sequences
$f(0),f(1),\dots$ and $g(0),g(1),\dots$ are Pólya frequency sequences, so is the value
sequence of $fg$.

**Theorem (Schur–Szegő; Kostov–Shapiro).** [@KostovShapiro2006] Let $f$ be a PF polynomial
and $g$ a real-rooted polynomial, both of degree at most $n$. Then $f*_ng$ is zero or
real-rooted. Now let $f,g$ have degree $n$, let $a\ne0$ be a root of $f$ of multiplicity $m$
and $b\ne0$ a root of $g$ of multiplicity $l$, with $m+l\ge n$. Then $-ab$ is a root of $f*_ng$
of multiplicity exactly $m+l-n$. If $g$ has degree $n$ and all roots in $[-b,-a]$, where
$0<a\le b$, and $f$ has all roots in $[-v,-u]$, where $0\le u\le v$, then $f*_ng$ has all
roots in $[-bv,-au]$.

## Use

The Hadamard product is a diagonal operator $x^k\mapsto\gamma_kx^k$; the diagonal operators
that preserve real-rootedness are the [multiplier sequences](rr:multiplier-sequences), which
include the finite Pólya–Schur theorem. Euler numerators of polynomial value sequences are
treated with [Brändén's E transform](rr:branden-e-transform), and the Hermite–Biehler
correspondence behind the Hurwitz-stable case is on the
[Hermite–Biehler page](rr:hermite-biehler-hurwitz).

## Proof

Write $f=q(x^2)+x\,p(x^2)$. By the Hermite–Biehler theorem $f$ is Hurwitz stable exactly when
$p\ll q$ with nonnegative coefficients, or one of $p,q$ is zero and the other is a PF
polynomial. The Hadamard product acts on the two parts separately, so the Hurwitz-stable case
follows from the interlacing and PF statements. The Schur–Szegő composition is the case of
Grace's apolarity theorem in which one polynomial has all roots in a half-line.

## References

E. Maló, “Note sur les équations algébriques dont toutes les racines sont réelles,”
*Journal de Mathématiques Spéciales* 4 (1895), 7–10;
[@Schur1914; @Wagner1992; @GarloffWagner1996; @KostovShapiro2006]. See also
[Hadamard products](sf:hadamardProductTheorems) and the
[Schur–Szegő composition](sf:schurSzegoComposition) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
