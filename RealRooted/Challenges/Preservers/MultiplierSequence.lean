module

import RealRooted.Hadamard.FiniteReflection
import RealRooted.Hadamard.Grace
import RealRooted.MultiplierSequence
import RealRooted.MultiplierSequence.CoefficientRatio
import RealRooted.MultiplierSequence.FallingFactorial
import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.MultiplierSequence.Laguerre
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned
import RealRooted.MultiplierSequence.ProperPositionPF

/-!
# Multiplier sequences and the Pólya–Schur theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "concepts"
slug = "multiplier-sequences"
formalized = "2026-09-07"
references = [
  "SchurPolya1914",
  "BorceaBranden2009I",
  "BorceaBranden2010",
  "Branden2015",
]
authors = ["Pólya", "Schur", "Borcea", "Brändén"]
years = [1914, 2009]

[[definitions]]
name = "RealRooted.IsMultiplierSequence"
module = "RealRooted.MultiplierSequence.Infinite"
label = "Multiplier sequence"

[[definitions]]
name = "RealRooted.jensenPolynomial"
module = "RealRooted.MultiplierSequence"
label = "Jensen polynomials"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.iff_signedLaguerrePolya_egf"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned"
label = "Pólya–Schur: γ is a multiplier sequence iff ±Σ γₖ(±z)ᵏ/k! is of type I"
headline = true

[[theorems]]
name = "RealRooted.IsPFMultiplierSequence.iff_laguerrePolya_egf"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse"
label = "Pólya–Schur: PF multiplier sequences are the type I Laguerre–Pólya class"

[[theorems]]
name = "RealRooted.isMultiplierSequence_iff_jensenPolynomial_isPF"
module = "RealRooted.MultiplierSequence.PolyaSchur"
label = "Pólya–Schur: γ ≥ 0 is a multiplier sequence iff its Jensen polynomials are PF"

[[theorems]]
name = "RealRooted.Hadamard.finiteMultiplierSequence_iff_jensen_isPFPolynomial"
module = "RealRooted.Hadamard.Grace"
label = "Finite Pólya–Schur theorem for γ ≥ 0"

[[theorems]]
name = "RealRooted.isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg"
module = "RealRooted.Hadamard.FiniteReflection"
label = "Finite Pólya–Schur theorem for alternating signs"

[[theorems]]
name = "RealRooted.isMultiplierSequence_eval_of_roots_nonpos"
module = "RealRooted.MultiplierSequence.Laguerre"
label = "Laguerre: φ(0), φ(1), φ(2), … is a multiplier sequence when φ has roots ≤ 0"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_inv_ascPochhammer"
module = "RealRooted.MultiplierSequence.InvPochhammer"
label = "Reciprocal rising factorials 1/(α)ₖ form a PF multiplier sequence"

[[theorems]]
name = "RealRooted.IsFinitePFMultiplierSequence.interl_diagonalOperator"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Borcea–Brändén: finite PF multiplier sequences preserve interlacing of PF polynomials"

[[theorems]]
name = "RealRooted.forall_splits_fallingSchur_iff"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "f is real-rooted iff all its falling-factorial truncations are"

[[theorems]]
name = "RealRooted.isPFPolynomial_of_pochhammer_coeff_ratio"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "A polynomial with a hypergeometric coefficient ratio is PF"
-->

<!-- realrooted-catalog-content -->
# Multiplier sequences and the Pólya–Schur theorem

A real sequence $\gamma$ is a multiplier sequence if $\sum a_kx^k\mapsto\sum\gamma_ka_kx^k$
preserves real-rootedness. Pólya and Schur characterized these sequences by their Jensen
polynomials and by the Laguerre–Pólya class; the result underlies most coefficientwise proofs
of real-rootedness.

## Results

A polynomial is *real-rooted* if it is zero or splits over $\mathbb R$, and *PF* if moreover
its coefficients are nonnegative. For a real sequence $\gamma$ let
$\Gamma\bigl(\sum_ka_kx^k\bigr)=\sum_k\gamma_ka_kx^k$. Then $\gamma$ is a *multiplier sequence*
if $\Gamma$ maps real-rooted polynomials to real-rooted polynomials, a *PF multiplier sequence*
if $\Gamma$ maps PF polynomials to PF polynomials, and a *finite* one of degree $n$ if this holds
for inputs of degree at most $n$. The *Jensen polynomials* are
$g_n(x)=\sum_{k=0}^n\binom nk\gamma_kx^k$.

**Theorem (Pólya–Schur).** [@SchurPolya1914] Let $\gamma_k\ge0$ for all $k$. Then $\gamma$ is a
multiplier sequence if and only if every Jensen polynomial $g_n$ is PF. Suppose that
$f(z)=\sum_k\gamma_kz^k/k!$ has positive radius of convergence. Then $\gamma$ is a PF
multiplier sequence if and only if $f$ is in the
[Laguerre–Pólya class](rr:laguerre-polya-class) of type I, and $\gamma$ is a multiplier
sequence if and only if one of $f(z)$, $-f(z)$, $f(-z)$, $-f(-z)$ is of type I.

**Theorem (finite Pólya–Schur).** Let $\gamma_0,\dotsc,\gamma_n$ be real. If every
$\gamma_k\ge0$, then $\gamma$ is a finite multiplier sequence of degree $n$ if and only if
$g_n$ is PF. If every $(-1)^k\gamma_k\ge0$, it is one if and only if $g_n$ is real-rooted with
all roots in $[0,\infty)$.

**Theorem (Laguerre).** If $\varphi$ is a real-rooted polynomial with only nonpositive roots,
then $\varphi(0),\varphi(1),\varphi(2),\dotsc$ is a multiplier sequence. For real $\alpha>0$
the sequence $1/(\alpha)_k$, with $(\alpha)_k=\alpha(\alpha+1)\dotsm(\alpha+k-1)$, is a PF
multiplier sequence.

**Theorem (interlacing; Borcea–Brändén).** [@BorceaBranden2009I; @BorceaBranden2010] If
$\gamma$ is a finite PF multiplier sequence of degree $N$ and $f\ll g$ are PF of degree at most
$N$, then $\Gamma f\ll\Gamma g$.

**Corollary (falling-factorial truncations).** For $f=\sum_jc_jt^j$ and $p\in\mathbb N$ put
$T_pf=\sum_jp(p-1)\dotsm(p-j+1)\,c_jt^j$. Then $f$ is real-rooted if and only if $T_pf$ is
real-rooted for every $p\ge0$.

**Corollary (hypergeometric coefficient ratios).** Let $a,b>0$, and let $p$ have degree at
most $d$ with $p(0)>0$ and
$$
(k+1)(a+k)\,p_{k+1}=(d-k)(b+d-k-1)\,p_k\qquad(0\le k<d).
$$
Then $p$ is PF. The parameter region is that of Martínez-Finkelshtein, Morales and Perales.

## Use

Multiplier sequences are the diagonal case of the
[Borcea–Brändén classification](rr:borcea-branden-classification) of linear preservers. They
act on coefficients, so they combine with [Hadamard products](rr:hadamard-products) and with
the operators $\varphi(D)$ of the [Hermite–Poulain theorem](rr:hermite-poulain).

## Proof

Applying $\Gamma$ to $(1+x)^n$ gives $g_n$, so the Jensen condition is necessary. Conversely,
$\Gamma f$ is the Schur–Szegő composition of $f$ with $g_n$, which is real-rooted by Grace's
theorem. Since $T_pf$ is the composition of $f$ with $(1+t)^p$, it is real-rooted when $f$ is;
conversely $T_pf(t/p)\to f(t)$ coefficientwise as $p\to\infty$. A polynomial with the stated
coefficient ratio is a positive multiple of $\sum_k\binom dkx^k/\bigl((a)_k(b)_{d-k}\bigr)$, which
is PF because $1/(a)_k$ and $1/(b)_k$ are PF multiplier sequences and reversal preserves PF
polynomials of degree $d$.

## References

[@SchurPolya1914]; [@BorceaBranden2009I]; [@BorceaBranden2010]; [@Branden2015];
A. Martínez-Finkelshtein, J. Morales and D. Perales, “Real roots of hypergeometric polynomials
via finite free convolution,” Thm. 4.6. See also [multiplier sequences](sf:multiplierSequences)
and the [finite multiplier criterion](sf:finiteMultiplierSequenceCriterion) on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
