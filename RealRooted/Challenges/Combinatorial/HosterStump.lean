module

import RealRooted.HosterStump.PosetChow

/-!
# Real-rooted Chow polynomials of simplicial posets

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chow-polynomials-simplicial-posets"
formalized = "2026-10-08"
tags = []
references = [
  "HosterStump2025x",
]
authors = ["Hoster", "Stump"]
years = [2025]

[[definitions]]
name = "RealRooted.HosterStump.IsSimplicialPoset"
module = "RealRooted.HosterStump.PosetBasic"
label = "Simplicial poset: every lower interval is Boolean, every element lies below rank n"

[[definitions]]
name = "RealRooted.HosterStump.chowOfFlagH"
module = "RealRooted.HosterStump.Chow"
label = "Chow polynomial of a flag h-vector"

[[definitions]]
name = "RealRooted.HosterStump.augChowOfFlagH"
module = "RealRooted.HosterStump.Chow"
label = "Augmented Chow polynomial of a flag h-vector"

[[definitions]]
name = "RealRooted.HosterStump.refined"
module = "RealRooted.HosterStump.Refined"
label = "Refined descent polynomials p^{S ⊆ T}_{n,k}"

[[theorems]]
name = "RealRooted.HosterStump.isRealRooted_chowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "Chow polynomials of simplicial posets with nonnegative h-vector are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.HosterStump.isRealRooted_chowOfFlagH_dualFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "The dual Chow polynomial is real-rooted"

[[theorems]]
name = "RealRooted.HosterStump.isRealRooted_augChowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "The augmented Chow polynomial is real-rooted"

[[theorems]]
name = "RealRooted.HosterStump.strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "For n ≥ 1, the dual Chow polynomial interlaces the augmented one"

[[theorems]]
name = "RealRooted.HosterStump.isSimplicialFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "Stanley's identity for the flag h-vector of a simplicial poset"

[[theorems]]
name = "RealRooted.HosterStump.isInterlacingDiagram_range"
module = "RealRooted.HosterStump.Step"
label = "For n ≥ 2, the refined descent polynomials form interlacing diagrams"
-->

<!-- realrooted-catalog-content -->
# Real-rooted Chow polynomials of simplicial posets

The Chow, dual Chow and augmented Chow polynomials of a graded simplicial poset with nonnegative
$h$-vector are real-rooted, and the dual Chow polynomial interlaces the augmented one.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated. Let $P$ be a
finite graded poset of rank $n$ with a bottom element $\hat0$, in which every lower interval
$[\hat 0,x]$ is a Boolean lattice and every element lies below an element of rank $n$ (a
*simplicial poset*). Write $h_0,\dots,h_n$ for its $h$-vector and $\beta(S)$ for the flag
$h$-vector of $\hat P$, the poset $P$ with a top element added. A set of integers is *isolated* if
it contains no two consecutive integers. The Chow and augmented Chow polynomials of $\hat P$ are
$$
H_{\hat P}(x)=\sum_{\substack{S\subseteq\{2,\dots,n\}\\ S\text{ isolated}}}
  \beta(S)\,x^{|S|}(1+x)^{n-2|S|},\qquad
H^{\mathrm{aug}}_{\hat P}(x)=\sum_{\substack{S\subseteq\{1,\dots,n\}\\ S\text{ isolated}}}
  \beta(S)\,x^{|S|}(1+x)^{n+1-2|S|}.
$$
The dual Chow polynomial $H_{\hat P^*}$ is defined by the same formula as $H_{\hat P}$ with the
flag $h$-vector $\beta^*(S)=\beta(n+1-S)$ of the dual poset.

**Theorem (Hoster–Stump).** If the $h$-vector of $P$ is nonnegative, then $H_{\hat P}$,
$H_{\hat P^*}$ and $H^{\mathrm{aug}}_{\hat P}$ are nonzero and real-rooted. If moreover $n\ge1$,
then $H_{\hat P^*}\ll H^{\mathrm{aug}}_{\hat P}$ [@HosterStump2025x].

**Stanley's identity.** For every simplicial poset $P$ of rank $n$,
$$
\beta(S)=\sum_{k}h_k\,\#\{w\in\mathfrak S_{n+1}:w_1=k+1,\ \operatorname{Des}w=n+1-S\}.
$$

## Use

The paper notes that the theorem covers Cohen–Macaulay simplicial posets and the lattices of
flats of uniform matroids.

## Proof

By Stanley's identity, the $\gamma$-polynomials of the three palindromic Chow polynomials are
$\sum_kh_k\,p^{T}_{n,k}$ for refined descent polynomials $p^{S\subseteq T}_{n,k}$. For $n\ge2$,
these polynomials form interlacing diagrams: every path through the diagram is an interlacing
sequence. Induction on $n$ proves this, and real-rootedness and interlacing pass from the
$\gamma$-polynomials to the Chow polynomials.

The paper's convention that any two polynomials of degree at most one interlace would make its
Lemma 2.3 false, with a counterexample among linear and quadratic polynomials; we use weak
interlacing without that convention.

## References

- [@HosterStump2025x]
- R. P. Stanley, *Combinatorics and Commutative Algebra*, 2nd ed., Birkhäuser, 1996, III.6.
- L. Ferroni, J. P. Matherne and L. Vecchi, “Chow functions for partially ordered sets,” 2024.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.HosterStump`.
-/
