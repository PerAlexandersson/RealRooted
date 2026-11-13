module

public import RealRooted.AissenSchoenbergWhitneyBase
public import RealRooted.CoefficientShape.LiuMao
public import RealRooted.GarloffWagner.Algebra
public import RealRooted.GarloffWagner.Hadamard
public import RealRooted.GarloffWagner.Theorem12
public import RealRooted.Hadamard
public import RealRooted.Hadamard.Basic
public import RealRooted.Hadamard.Consequences
public import RealRooted.Hadamard.FiniteReflection
public import RealRooted.Hadamard.Grace
public import RealRooted.Hadamard.KostovMap
public import RealRooted.Hadamard.OrderedRoots
public import RealRooted.Hadamard.Product
public import RealRooted.Hadamard.RootIntervals
public import RealRooted.Hadamard.SchurSzegoMultiplicity
public import RealRooted.Hadamard.SchurSzegoSigns
public import RealRooted.Hadamard.SchurSzegoSimple
public import RealRooted.Hadamard.SequenceCounterexamples
public import RealRooted.Hadamard.SequenceOperators
public import RealRooted.MultiplierSequence.PolyaSchur.Schur
public import RealRooted.PFPolynomial
public import RealRooted.PolynomialValueEulerNumerator.Product.Brenti
public import RealRooted.PolynomialValueEulerNumerator.Product.PF.Causal

/-!
# Hadamard products and Schur–Szegő composition

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hadamard-products"
formalized = "2026-07-03"
tags = []
references = [
  "SchurPolya1914",
  "Wagner1992",
  "GarloffWagner1996",
  "BrandenFerroniJochemko2024x",
  "LiuMao2026Hadamard",
  "KostovShapiro2006",
  "Kostov2010",
]
authors = [
  "Maló", "Pólya", "Schur", "Brenti", "Wagner", "Garloff", "Kostov", "Shapiro", "Brändén",
  "Ferroni", "Jochemko", "Liu", "Mao"]
years = [1895, 1914, 1989, 1992, 1996, 2006, 2010, 2024, 2026]

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
name = "RealRooted.finiteSchurSzegoComposition"
module = "RealRooted.Hadamard.Grace"
label = "Schur–Szegő composition preserves real-rootedness"

[[theorems]]
name = "RealRooted.rootMultiplicity_schurSzegoComp"
module = "RealRooted.Hadamard.SchurSzegoMultiplicity"
label = "Kostov–Shapiro: exact multiplicity of the root −ab of a Schur–Szegő composition"

[[theorems]]
name = "RealRooted.exists_forced_factors_of_rootMultiplicity_schurSzegoComp"
module = "RealRooted.Hadamard.SchurSzegoSimple"
label = "Kostov–Shapiro: every nonzero multiple root of P *_n Q is a forced product −ab"

[[theorems]]
name = "RealRooted.schurSzegoComp_roots_sign_counts_of_roots_neg"
module = "RealRooted.Hadamard.SchurSzegoSigns"
label = "Kostov–Shapiro: composition with a negative-rooted polynomial preserves root signs"

[[theorems]]
name = "RealRooted.splits_schurSzegoComp_of_roots_neg"
module = "RealRooted.Hadamard.SchurSzegoSigns"
label = "Composition with a negative-rooted polynomial preserves real-rootedness"

[[theorems]]
name = "RealRooted.IsRealRootedIn.schurSzegoComp_Icc"
module = "RealRooted.Hadamard.RootIntervals"
label = "Kostov–Shapiro: roots in [−b, −a] and [−v, −u] give roots in [−bv, −au]"

[[theorems]]
name = "RealRooted.IsRealRootedIn.schurSzegoComp_Icc_zero"
module = "RealRooted.Hadamard.RootIntervals"
label = "Kostov–Shapiro: roots in [−b, 0] and [−v, 0] give roots in [−bv, 0]"

[[theorems]]
name = "RealRooted.IsRealRootedIn.schurSzegoComp_Icc_of_natDegree_le"
module = "RealRooted.Hadamard.RootIntervals"
label = "Root intervals for an input of degree at most n"

[[theorems]]
name = "RealRooted.IsRealRootedIn.schurSzegoComp_Icc_zero_of_natDegree_le"
module = "RealRooted.Hadamard.RootIntervals"
label = "Root rays [−b, 0] for an input of degree at most n; the output may be zero"

[[theorems]]
name = "RealRooted.IsRealRootedIn.maps_schurSzegoComp_Icc"
module = "RealRooted.Hadamard.RootIntervals"
label = "Fixed Schur–Szegő composition maps strict root intervals"

[[theorems]]
name = "RealRooted.IsRealRootedIn.maps_schurSzegoComp_Icc_zero"
module = "RealRooted.Hadamard.RootIntervals"
label = "Fixed Schur–Szegő composition maps root rays, allowing zero output"

[[theorems]]
name = "RealRooted.IsRealRootedIn.orderedRoot_schurSzegoComp_bounds"
module = "RealRooted.Hadamard.OrderedRoots"
label = "Coordinatewise bounds for the ordered roots of a Schur–Szegő composition"

[[theorems]]
name = "RealRooted.basisTransformₗ_schurSzegoComp"
module = "RealRooted.Hadamard.SequenceOperators"
label = "Fixed Schur–Szegő composition postcomposes a polynomial-sequence operator"

[[theorems]]
name = "RealRooted.basisTransformₗ_C_mul"
module = "RealRooted.Hadamard.SequenceOperators"
label = "Termwise sequence scaling precomposes by a diagonal operator"

[[theorems]]
name = "RealRooted.basisTransformₗ_schurSzegoComp_C_mul"
module = "RealRooted.Hadamard.SequenceOperators"
label = "Combined diagonal precomposition and Schur–Szegő postcomposition"

[[theorems]]
name = "RealRooted.MapsRealRootedIn.basisTransform_schurSzegoComp_C_mul"
module = "RealRooted.Hadamard.SequenceOperators"
label = "Root-location preservation for the combined sequence operation"

[[theorems]]
name = "RealRooted.rowwiseHadamardProduct_counterexample"
module = "RealRooted.Hadamard.SequenceCounterexamples"
label = "Two preserving sequence maps can have a non-real-rooted rowwise Hadamard product"

[[theorems]]
name = "RealRooted.rowwiseNormalizedSchurProduct_counterexample"
module = "RealRooted.Hadamard.SequenceCounterexamples"
label = "Identical invertible maps can have non-real-rooted rowwise Schur squares"

[[theorems]]
name = "RealRooted.Kostov.interiorCoeff_composition"
module = "RealRooted.Hadamard.KostovMap"
label = "Kostov: Schur–Szegő factorizations have coefficients affine in σ(a)"

[[theorems]]
name = "RealRooted.Kostov.coeffMap_eq_sigma"
module = "RealRooted.Hadamard.KostovMap"
label = "Kostov's coefficient map recovers the symmetric functions of a factorization"

[[theorems]]
name = "RealRooted.Hadamard.finiteMultiplierSequence_iff_jensen_isPFPolynomial"
module = "RealRooted.Hadamard.Grace"
label = "Finite Pólya–Schur theorem"

[[theorems]]
name = "RealRooted.isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg"
module = "RealRooted.Hadamard.FiniteReflection"
label = "Finite Pólya–Schur theorem, alternating signs"

[[theorems]]
name = "RealRooted.StrictInterl.interl_hadamardProduct"
module = "RealRooted.GarloffWagner.Hadamard"
label = "Garloff–Wagner: Hadamard products preserve interlacing"
headline = true

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.mul_coeff"
module = "RealRooted.Hadamard.Consequences"
label = "Maló: termwise products of Pólya frequency coefficient sequences are PF"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_polynomialValueSeq_mul_of_polyaFreqSeq"
module = "RealRooted.PolynomialValueEulerNumerator.Product.PF.Causal"
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
name = "RealRooted.factorialHadamardProduct_eq_zero_or_splits"
module = "RealRooted.MultiplierSequence.PolyaSchur.Schur"
label = "Schur: the factorial product preserves real-rootedness"

[[theorems]]
name = "RealRooted.LiuMao.coeffLCNIZ_polynomialValueEulerNumerator_mul"
module = "RealRooted.CoefficientShape.LiuMao"
label = "Liu–Mao: log-concave Euler numerators without internal zeros are closed under products"
-->

<!-- realrooted-catalog-content -->
# Hadamard products and Schur–Szegő composition

Coefficientwise products of polynomials preserve Pólya frequency polynomials and interlacing.
The same holds for the Schur–Szegő composition, which also controls root locations, and the
finite Pólya–Schur theorem characterizes the diagonal operators that preserve real-rootedness.

## Results

A *PF polynomial* is a real polynomial with nonnegative coefficients that is zero or
real-rooted. For $f=\sum_kf_kx^k$ and $p=\sum_kp_kx^k$, the *Hadamard product* is
$f\ast p=\sum_kf_kp_kx^k$ and the *factorial Hadamard product* is
$f\circledast p=\sum_kk!\,f_kp_kx^k$. For $f$ and $g$ of degree at most $n$, the *Schur–Szegő
composition* is
$$
f*_ng=\sum_{k=0}^n\binom nk^{-1}f_kg_kx^k.
$$

**Theorem (Garloff–Wagner).** [@GarloffWagner1996] For PF polynomials $p,q$ the Hadamard
product $p\ast q$ is PF. If $f \ll g$ and $p \ll q$ have nonnegative coefficients, then
$f\ast p \ll g\ast q$ or one of $f\ast p$ and $g\ast q$ is zero. If $f,g,p$ are PF and $f\ll g$
(or one of $f,g$ is zero), then $f\circledast p\ll g\circledast p$ or one of them is zero.

**Theorem (Schur; Maló).** [@SchurPolya1914] If $f$ and $g$ are real-rooted and the roots of
$g$ are all nonpositive or all nonnegative, then $f\circledast g$ is zero or real-rooted. The
termwise product of two Pólya frequency coefficient sequences of polynomials is a Pólya
frequency sequence; equivalently, the entrywise product of their totally nonnegative Toeplitz
matrices is totally nonnegative.

**Theorem (Schur–Szegő; Kostov–Shapiro).** [@KostovShapiro2006; @Kostov2010] If $f$ is a PF
polynomial of degree at most $n$ and $g$ is real-rooted of degree at most $n$, then $f*_ng$ is
zero or real-rooted. Now let $f$ and $g$ have degree $n$, let $a \neq 0$ be a root of $f$ of
multiplicity $m$ and $b \neq 0$ a root of $g$ of multiplicity $l$, with $m + l \geq n$. Then
$-ab$ is a root of $f *_n g$ of multiplicity exactly $m + l - n$. If moreover $f$ is
real-rooted and $g$ has only negative roots, then $f *_n g$ is real-rooted with as many
positive, zero and negative roots as $f$, every nonzero root of multiplicity at least two is
such a product $-ab$ with $m+l>n$, and all other nonzero roots are simple. Real-rootedness
still holds when $f$ and $g$ only have degree at most $n$.

Root intervals are mapped to root intervals [@KostovShapiro2006]. If $g$ has degree $n$ with all
roots in $[-b,-a]$, where $0<a\le b$, and $f$ has degree at most $n$ with all roots in
$[-v,-u]$, where $0\le u\le v$, then $f*_ng$ has all roots in $[-bv,-au]$. If instead the roots
of $f$ lie in $[-v,0]$ and those of $g$ in $[-b,0]$ with $b,v\ge0$, then $f*_ng$ is zero or has
all roots in $[-bv,0]$, and it is nonzero when $\deg f=n$. Under the first hypotheses, with
$\deg f=m$, let $\beta_1\le\dots\le\beta_m$ be the roots of the degree-$m$ reduction of $g$ and
$\rho_1\le\dots\le\rho_m$ those of $f*_ng$; then $v\beta_i\le\rho_i\le u\beta_i$ for every $i$.

**Theorem (finite Pólya–Schur).** Let $\gamma_0,\dots,\gamma_n$ be real, let
$T_\gamma(x^k) = \gamma_k x^k$ and $J(x)=\sum_{k=0}^n \binom{n}{k} \gamma_k x^k$. If every
$\gamma_k \geq 0$, then $T_\gamma$ maps each real-rooted polynomial of degree at most $n$ to
zero or a real-rooted polynomial if and only if $J$ is a PF polynomial. If every
$(-1)^k\gamma_k \geq 0$, it does so if and only if $J$ is zero or real-rooted with all roots
in $[0,\infty)$.

For value sequences, Wagner's theorem says: if $f(0),f(1),f(2),\dotsc$ and
$g(0),g(1),g(2),\dotsc$ are Pólya frequency sequences for real polynomials $f,g$, then so is
the value sequence of $fg$ [@Wagner1992; @BrandenFerroniJochemko2024x]. Write
$\sum_{n \ge 0} p(n)\, x^n = W(p)(x)/(1-x)^{\deg p + 1}$. By Brenti, if $p$ is real-rooted with
all roots in $[-1, 0]$ and nonnegative leading coefficient, then $W(p)$ is PF; for $p = x + a$
with $0\le a\le1$ it is $a + (1-a)x$. By Liu and Mao [@LiuMao2026Hadamard], if the coefficients
of $W(p)$ and $W(q)$ are nonnegative, log-concave and without internal zeros (up to $\deg p$
and $\deg q$), then so are those of $W(pq)$ (up to $\deg pq$); the example $W(p) = 1 + x^3$,
$W(q) = x$, $W(pq) = 4x + 3x^3 + x^4$ shows that internal zeros must be excluded.

Further results: Kostov's coefficient map, which shows that a monic $P$ with $P(-1)=0$ written
as $K_{a_1}*_n\dots*_nK_{a_{n-1}}$, $K_a=(x+1)^{n-1}(x+a)$, has interior coefficients affine
in $\sigma_j(a_1,\dots,a_{n-1})$ with an invertible scaled Vandermonde linear part, so its
coefficients determine $\sigma(a)$; and the fact that root-location preservation passes to
rowwise Schur–Szegő and diagonal scaling of a polynomial sequence, but not to rowwise Hadamard
products of two preserving sequence maps (one sends $(1+2x)^2$ to $1+3x+4x^2$) or to rowwise
normalized Schur squares of one invertible preserving sequence (one sends $1+2x$ to
$(9x^2+24x+17)/8$).

## References

- E. Maló, “Note sur les équations algébriques dont toutes les racines sont réelles,”
  *Journal de Mathématiques Spéciales* 4 (1895), 7–10.
- [@SchurPolya1914; @Wagner1992; @GarloffWagner1996; @KostovShapiro2006; @Kostov2010].
- [@BrandenFerroniJochemko2024x; @LiuMao2026Hadamard].
- V. P. Kostov, “Eigenvectors in the context of the Schur–Szegő composition of polynomials,”
  *Mathematica Balkanica* 22 (2008), 155–173.

See also [Hadamard products](sf:hadamardProductTheorems),
[Schur–Szegő composition](sf:schurSzegoComposition) and the
[finite multiplier criterion](sf:finiteMultiplierSequenceCriterion) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

Human statements:

* Hadamard product theorems:
  sf:hadamardProductTheorems
* Schur--Szego composition:
  sf:schurSzegoComposition
* Polya-frequency sequences:
  sf:aissenSchoenbergWhitney
* Finite multiplier criterion:
  sf:finiteMultiplierSequenceCriterion

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
