import RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted

/-!
# Jacobi–Stirling descent polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-stirling-descent"
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
label = "Each A_{k,S} has degree 2k - |S| - 1 and simple negative zeros"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.StrictInterleave.insertion_succ"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Comparison"
label = "Insertions preserve strict interleaving"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.weightedDescentSum_splits_simple_neg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = "Nonnegative combinations for i ∈ {1, 2, 3, k − 2, k − 1} have simple negative zeros"
headline = true

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.descentSum_splits_simple_neg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.RealRooted"
label = "A_{k,i} is real-rooted for i ∈ {1, 2, 3, k − 2, k − 1}"

[[theorems]]
name = "RealRooted.JacobiStirlingDescent.X_mul_descentPoly_Icc"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic"
label = "With every barred letter deleted: the second-order Eulerian polynomials"
-->

<!-- realrooted-catalog-content -->
# Jacobi–Stirling descent polynomials

Gessel, Lin and Zeng studied Jacobi–Stirling permutations: permutations of the
multiset $M_k = \{\bar 1, 1, 1, \bar 2, 2, 2, \dotsc, \bar k, k, k\}$ with a
Stirling-type pattern condition. For $S \subseteq [k]$, let $A_{k,S}(x)$ count
the Jacobi–Stirling permutations of $M_k \setminus \{\bar s : s \in S\}$ by
descents, and let $A_{k,i} = \sum_{|S| = i} A_{k,S}$. They conjectured that
every $A_{k,i}$ is real-rooted.

Inserting the letters one at a time gives the recurrences
$$A_{k,S} = D_L A_{k-1,S \setminus \{k\}} \quad (k \in S), \qquad
  A_{k,S} = D_{L+1} D_L A_{k-1,S} \quad (k \notin S),$$
with $L = 3(k-1) - |S \cap [k-1]|$ and the insertion operator
$$D_L f = (1 + Lx) f + x(1 - x) f'.$$
Here these recurrences define the polynomials. The permutation model is not
formalized.

**Theorem** (Ma–Wang). Let $1 \le i \le k$ with $i \in \{1, 2, 3, k-2, k-1\}$.
Every nonzero nonnegative combination $\sum_{|S| = i} c_S A_{k,S}$ has only
simple negative zeros. In particular, $A_{k,i}$ is real-rooted.

Each $A_{k,S}$ has degree $2k - |S| - 1$, constant term $1$ and simple negative
zeros. When every barred letter is deleted, $x A_{k,[k]}$ is the second-order
Eulerian polynomial.

## Proof idea

If $\deg f < L$, then $D_L f$ has degree $\deg f + 1$ and strictly interlaces
$f$, because $D_L f(r) = r(1 - r) f'(r)$ at each zero $r$ of $f$. If $f$
strictly interlaces $g$ with $\deg g = \deg f + 1$, then
$D_L f \prec D_{L+1} g$, and $D_L f \prec D_L g$ when $L > \deg g$. The proof
uses the identity
$$g \, D_L f - f \, D_{L+1} g = -x \, W\bigl(g, (x - 1) f\bigr)$$
and the positivity of the Wronskian $W(g, (x-1) f)$. For each family, an
induction on $k$ compares every $A_{k,S}$ with a single polynomial:
$A_{k,\emptyset}$, $H_k = D_{3k-3} A_{k-1,\emptyset}$, $A_{k-1,\emptyset}$, or
a second-order Eulerian polynomial. Nonnegative combinations of polynomials that
all strictly interlace a common polynomial keep that property.

## References

I. M. Gessel, Z. Lin and J. Zeng, “Jacobi–Stirling polynomials and
$P$-partitions,” *European Journal of Combinatorics* 33 (2012), 1987–2000;
S.-M. Ma and M.-X. Wang, “Binomial expansions of Jacobi–Stirling numbers and
real-rootedness of Jacobi–Stirling descent polynomials,” arXiv:2610.03111
(2026), Section 4.

The theorem was formalized in RealRooted issue #1105.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.JacobiStirling.Descent`.
-/
