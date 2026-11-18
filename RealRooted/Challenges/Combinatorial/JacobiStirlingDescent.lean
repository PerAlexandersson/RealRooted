module

import RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic
import RealRooted.CombinatorialExamples.JacobiStirling.Descent.Comparison
import RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted
import RealRooted.CombinatorialExamples.JacobiStirling.FirstKind
import RealRooted.CombinatorialExamples.JacobiStirling.FirstKindPF
import RealRooted.CombinatorialExamples.JacobiStirling.Inverse
import RealRooted.CombinatorialExamples.JacobiStirling.SecondKind
import RealRooted.CombinatorialExamples.JacobiStirling.TotallyNonnegative

/-!
# Jacobi–Stirling numbers and descent polynomials

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "families"
slug = "jacobi-stirling"
formalized = "2026-10-07"
references = [
  "GelineauZeng2010",
  "Mongelli2012",
  {key = "GesselLinZeng2012", at = "Conj. 15"},
  "AndrewsEggeGawronskiLittlejohn2013",
  {key = "MaWang2026x", at = "Thm. 2"},
]
authors = ["Gelineau", "Zeng", "Mongelli", "Gessel", "Lin", "Ma", "Wang"]
years = [2010, 2012, 2026]

[[definitions]]
name = "RealRooted.JacobiStirling.firstKind"
module = "RealRooted.CombinatorialExamples.JacobiStirling.FirstKind"
label = "Jacobi–Stirling numbers of the first kind"

[[definitions]]
name = "RealRooted.JacobiStirling.secondKind"
module = "RealRooted.CombinatorialExamples.JacobiStirling.SecondKind"
label = "Jacobi–Stirling numbers of the second kind"

[[definitions]]
name = "RealRooted.JacobiStirlingDescent.insertion"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "The insertion operator $D_L f = (1 + Lx) f + x(1 - x) f'$"

[[definitions]]
name = "RealRooted.JacobiStirlingDescent.descentSum"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = "The Jacobi–Stirling descent polynomial $A_{k,i}$"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.weightedDescentSum_splits_simple_neg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = 'Ma–Wang: for $i ∈ \{1, 2, 3, k - 2, k - 1\}$, every $∑ c_S A_{k,S}$ is real-rooted'
headline = true

[[theorems]]
objects = ["Jacobi–Stirling descent polynomials"]
name = "RealRooted.JacobiStirlingDescent.descentSum_splits_simple_neg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = '$A_{k,i}$ is real-rooted for $i ∈ \{1, 2, 3, k - 2, k - 1\}$'

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.isGood_descentPoly"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "For $k ≥ 1$, $A_{k,S}$ has degree $2k - |S| - 1$, constant term 1, simple negative roots"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.StrictInterleave.insertion_succ"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Comparison"
label = 'If $f ≺ g$, $\deg g = \deg f + 1$ and $\deg f < L$, then $D_L f ≺ D_{L+1} g$'

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.X_mul_descentPoly_Icc"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "Deleting every barred letter: $x A_{k,[k]}$ is the second-order Eulerian polynomial"

[[theorems]]
name = "RealRooted.JacobiStirling.firstKindMatrix_isTotallyNonneg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.TotallyNonnegative"
label = "Mongelli: the first-kind triangle is totally nonnegative for z ≥ −1"

[[theorems]]
objects = ["Jacobi–Stirling first-kind row polynomials"]
property = "pf"
name = "RealRooted.JacobiStirling.firstKindRow_isPFPolynomial"
module = "RealRooted.CombinatorialExamples.JacobiStirling.FirstKindPF"
label = "First-kind rows are Pólya frequency polynomials for z ≥ −1"

[[theorems]]
name = "RealRooted.JacobiStirling.signedFirstKind_mul_secondKind_sum"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Inverse"
label = "The signed first-kind and second-kind triangles are mutually inverse"
-->

<!-- realrooted-catalog-content -->
# Jacobi–Stirling numbers and descent polynomials

The Jacobi–Stirling numbers generalize the Stirling numbers through the spectral theory of the
Jacobi differential operator. Their first-kind triangle is totally nonnegative (Mongelli), and
the descent polynomials of Jacobi–Stirling permutations are real-rooted in the cases settled by
S.-M. Ma and Y. Wang, part of a conjecture of Gessel, Lin and Zeng.

## Results

The Jacobi–Stirling numbers of the first and second kind, $\mathrm{Jc}(n,k;z)$ and
$\mathrm{JS}(n,k;z)$, satisfy $\mathrm{Jc}(0,0)=\mathrm{JS}(0,0)=1$, vanish if exactly one index
is $0$, and for $n,k\ge1$
$$
\mathrm{Jc}(n,k)=\mathrm{Jc}(n-1,k-1)+(n-1)(n-1+z)\,\mathrm{Jc}(n-1,k),\qquad
\mathrm{JS}(n,k)=\mathrm{JS}(n-1,k-1)+k(k+z)\,\mathrm{JS}(n-1,k).
$$
The case $z=1$ gives the Legendre–Stirling numbers. The signed first-kind and the second-kind
triangles are mutually inverse.

**Theorem (Mongelli).** [@Mongelli2012] For $z\ge-1$ the triangle $(\mathrm{Jc}(n,k;z))$ is
totally nonnegative, and for $n\ge1$
$$
\sum_k\mathrm{Jc}(n,k;z)\,x^k=x\prod_{i=1}^{n-1}\bigl(x+i(i+z)\bigr),
$$
so every row is a Pólya frequency polynomial.

Jacobi–Stirling permutations are permutations of the multiset
$M_k=\{\bar1,1,1,\dots,\bar k,k,k\}$ with a Stirling-type pattern condition. For
$S\subseteq[k]$ let $A_{k,S}$ count those of $M_k\setminus\{\bar s:s\in S\}$ by descents, and
$A_{k,i}=\sum_{|S|=i}A_{k,S}$. Gessel, Lin and Zeng conjectured that every $A_{k,i}$ is
real-rooted [@GesselLinZeng2012, Conj. 15]. We define $A_{k,S}$ by the insertion recurrences
$A_{0,S}=1$, $A_{k,S}=D_LA_{k-1,S\setminus\{k\}}$ for $k\in S$ and
$A_{k,S}=D_{L+1}D_LA_{k-1,S}$ for $k\notin S$, with $L=3(k-1)-|S\cap[k-1]|$ and
$D_Lf=(1+Lx)f+x(1-x)f'$.

**Theorem (Ma–Wang).** [@MaWang2026x, Thm. 2] Let $1\le i\le k$ with
$i\in\{1,2,3,k-2,k-1\}$. Every nonzero nonnegative combination $\sum_{|S|=i}c_SA_{k,S}$ has
only simple negative roots. In particular $A_{k,i}$ is real-rooted.

Each $A_{k,S}$ with $k\ge1$ has degree $2k-|S|-1$, constant term $1$ and only simple negative
roots, and $x\,A_{k,[k]}$ is the second-order Eulerian polynomial.

## Proof

Mongelli's triangle is the elementary-symmetric triangle of the weights $i(i+z)\ge0$, a product
of nonnegative bidiagonal matrices. For the descent polynomials, if $f\ll g$ have simple negative
roots and no common root, $\deg g=\deg f+1$ and $L>\deg f$, then $D_Lf\ll D_{L+1}g$, by the
identity $g\,D_Lf-f\,D_{L+1}g=-x\,W\bigl(g,(x-1)f\bigr)$ and the positivity of the Wronskian. An
induction on $k$ compares every $A_{k,S}$ with one fixed polynomial, and nonnegative
combinations of polynomials that interlace a common polynomial keep that property.

## References

[@GelineauZeng2010]; [@Mongelli2012]; [@GesselLinZeng2012, Conj. 15];
[@AndrewsEggeGawronskiLittlejohn2013]; [@MaWang2026x, Thm. 2].
<!-- /realrooted-catalog-content -->
-/
