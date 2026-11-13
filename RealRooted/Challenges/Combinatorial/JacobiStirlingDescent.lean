module

import RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted

/-!
# Jacobi–Stirling descent polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-stirling-descent"
formalized = "2026-10-07"
tags = []
references = [
  "GesselLinZeng2012",
  "MaWang2026x",
]
authors = ["Gessel", "Lin", "Zeng", "Ma", "Wang"]
years = [2012, 2026]

[[definitions]]
name = "RealRooted.JacobiStirlingDescent.insertion"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "The insertion operator D_L f = (1 + Lx) f + x(1 - x) f'"

[[definitions]]
name = "RealRooted.JacobiStirlingDescent.descentPoly"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "The descent polynomial A_{k,S}"

[[definitions]]
name = "RealRooted.JacobiStirlingDescent.descentSum"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = "The Jacobi–Stirling descent polynomial A_{k,i}"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.isGood_descentPoly"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "For k ≥ 1, A_{k,S} has degree 2k − |S| − 1, constant term 1, simple negative roots"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.StrictInterleave.insertion_succ"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Comparison"
label = "If f ≺ g, deg g = deg f + 1 and deg f < L, then D_L f ≺ D_{L+1} g"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.weightedDescentSum_splits_simple_neg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = "For i ∈ {1, 2, 3, k − 2, k − 1}, nonnegative combinations of A_{k,S} are real-rooted"
headline = true

[[theorems]]
objects = ["Jacobi–Stirling descent polynomials"]
name = "RealRooted.JacobiStirlingDescent.descentSum_splits_simple_neg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = "A_{k,i} is real-rooted for i ∈ {1, 2, 3, k − 2, k − 1}"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.X_mul_descentPoly_Icc"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "Deleting every barred letter: x A_{k,[k]} is the second-order Eulerian polynomial"
-->

<!-- realrooted-catalog-content -->
# Jacobi–Stirling descent polynomials

The Jacobi–Stirling descent polynomials $A_{k,i}$ are real-rooted for $i\in\{1,2,3,k-2,k-1\}$.

## Results

Gessel, Lin and Zeng studied Jacobi–Stirling permutations: permutations of the multiset
$M_k=\{\bar1,1,1,\bar2,2,2,\dotsc,\bar k,k,k\}$ with a Stirling-type pattern condition. For
$S\subseteq[k]$, let $A_{k,S}(x)$ count the Jacobi–Stirling permutations of
$M_k\setminus\{\bar s:s\in S\}$ by descents, and let $A_{k,i}=\sum_{|S|=i}A_{k,S}$. They conjectured
that every $A_{k,i}$ is real-rooted [@GesselLinZeng2012, Conj. 15].

We define $A_{k,S}$ by the insertion recurrences $A_{0,S}=1$,
$$
A_{k,S}=D_L\,A_{k-1,S\setminus\{k\}}\quad(k\in S),\qquad
A_{k,S}=D_{L+1}D_L\,A_{k-1,S}\quad(k\notin S),
$$
with $L=3(k-1)-|S\cap[k-1]|$ and the insertion operator $D_Lf=(1+Lx)f+x(1-x)f'$.

**Theorem (Ma–Wang).** Let $1\le i\le k$ with $i\in\{1,2,3,k-2,k-1\}$. Every nonzero nonnegative
combination $\sum_{|S|=i}c_SA_{k,S}$ has only simple negative roots, all real. In particular
$A_{k,i}$ is real-rooted with simple negative roots [@MaWang2026x, Thm. 2].

**Proposition.** For $k\ge1$ and $S\subseteq[k]$, $A_{k,S}$ has degree $2k-|S|-1$, constant term
$1$, nonnegative coefficients and only simple negative roots. When every barred letter is deleted,
$x\,A_{k,[k]}$ is the second-order Eulerian polynomial, the descent polynomial of Stirling
permutations.

## Proof

Let $f\ll g$ be polynomials with simple negative roots and no common root, with
$\deg g=\deg f+1$, and let $L>\deg f$. Then $D_Lf\ll D_{L+1}g$ with no common root, by the
identity $g\,D_Lf-f\,D_{L+1}g=-x\,W\bigl(g,(x-1)f\bigr)$ and the positivity of the Wronskian
$W(g,(x-1)f)$. An induction on $k$ compares every $A_{k,S}$ with one fixed polynomial, and
nonnegative combinations of polynomials that all interlace a common polynomial keep that
property.

## References

- [@GesselLinZeng2012, Conj. 15]
- [@MaWang2026x, Thm. 2]
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.JacobiStirling.Descent`.
-/
