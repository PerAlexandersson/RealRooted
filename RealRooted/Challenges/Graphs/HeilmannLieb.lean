module

public import RealRooted.Graph.IndependencePolynomial.Basic
public import RealRooted.Graph.IndependencePolynomial.ClawFree
public import RealRooted.Graph.MatchingPolynomial
public import RealRooted.Graph.MatchingVertexInterlacing
public import RealRooted.HeilmannLieb
public import RealRooted.Mathlib.Combinatorics.SimpleGraph.MatchingPolyOn
public import RealRooted.RankTwoMatching.Basic
public import RealRooted.RankTwoMatching.Endpoint
public import RealRooted.RankTwoMatching.Transform

/-!
# Heilmann–Lieb theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "heilmann-lieb"
formalized = "2026-10-06"
tags = []
references = [
  "HeilmannLieb1972",
  "Engstrom2007",
  "ChudnovskySeymour2007",
]
authors = ["Heilmann", "Lieb", "Godsil", "Engström"]
years = [1972, 1981, 2007]

[[definitions]]
name = "RealRooted.Graph.matchingPolynomialByEdges"
module = "RealRooted.Graph.MatchingPolynomial"
label = "Matching-generating polynomial"

[[definitions]]
name = "RealRooted.Graph.weightedMatchingPolynomialByEdges"
module = "RealRooted.Graph.MatchingPolynomial"
label = "Edge-weighted matching-generating polynomial"

[[definitions]]
name = "RealRooted.Graph.weightedIndepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Basic"
label = "Vertex-weighted independence polynomial"

[[definitions]]
name = "SimpleGraph.matchingPolyOn"
module = "RealRooted.Mathlib.Combinatorics.SimpleGraph.MatchingPolyOn"
label = "Matching polynomial μ_S(x) of the induced subgraph G[S]"

[[definitions]]
name = "RealRooted.Graph.rankTwoBinomialTransform"
module = "RealRooted.RankTwoMatching.Transform"
label = "Rank-two binomial transform"

[[definitions]]
name = "RealRooted.Graph.completeGraphRankTwoWeight"
module = "RealRooted.RankTwoMatching.Basic"
label = "Rank-two edge weights a_i b_j + a_j b_i on a complete graph"

[[theorems]]
objects = ["Matching polynomials"]
name = "RealRooted.Graph.matchingPolynomialByEdges_splits"
module = "RealRooted.HeilmannLieb"
label = "Heilmann–Lieb: the matching polynomial is real-rooted"

[[theorems]]
objects = ["Matching polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_matchingPolyOn_erase"
module = "RealRooted.Graph.MatchingVertexInterlacing"
label = "Deleting a vertex interlaces the matching polynomial"

[[theorems]]
name = "RealRooted.splits_matchingPolyOn"
module = "RealRooted.Graph.MatchingVertexInterlacing"
label = "Heilmann–Lieb: μ_S is real-rooted"

[[theorems]]
name = "RealRooted.abs_le_of_isRoot_matchingPolyOn"
module = "RealRooted.Graph.MatchingVertexInterlacing"
label = "Heilmann–Lieb root bound |x| ≤ 2√(Δ − 1)"

[[theorems]]
name = "RealRooted.Graph.weightedIndepPoly_splits_of_clawFree"
module = "RealRooted.Graph.IndependencePolynomial.ClawFree"
label = "Engström: weighted independence polynomials of claw-free graphs are real-rooted"
symcat = "weightedIndependencePolynomial"

[[theorems]]
name = "RealRooted.Graph.weightedMatchingPolynomialByEdges_splits"
module = "RealRooted.HeilmannLieb"
label = "Weighted matching polynomials are real-rooted"
headline = true

[[theorems]]
objects = ["Weighted matching polynomials"]
property = "pf"
name = "RealRooted.Graph.weightedMatchingPolynomialByEdges_isPFPolynomial"
module = "RealRooted.HeilmannLieb"
label = "Weighted matching polynomials are PF polynomials"

[[theorems]]
name = "RealRooted.Graph.rankTwoBinomialTransform_isPF"
module = "RealRooted.RankTwoMatching.Transform"
label = "The rank-two binomial transform preserves PF polynomials"

[[theorems]]
name = "RealRooted.Graph.exists_nonneg_completeGraphRankTwoWeight_eq_coeff_sum"
module = "RealRooted.RankTwoMatching.Endpoint"
label = "A PF polynomial is a rank-two weighted matching polynomial of K_M"

[[theorems]]
name = "RealRooted.Graph.weightedMatchingNumber_completeGraph_rankTwo"
module = "RealRooted.RankTwoMatching.Endpoint"
label = "Rank-two weighted matching numbers of a complete graph"
-->

<!-- realrooted-catalog-content -->
# Heilmann–Lieb theorem

Matching polynomials are real-rooted, and deleting a vertex gives an interlacing polynomial; the
same holds for weighted matching polynomials and for weighted independence polynomials of
claw-free graphs.

## Results

Let $G$ be a finite simple graph. Its *matching-generating polynomial* is
$$
m_G(x)=\sum_{M}x^{|M|},
$$
where $M$ ranges over the matchings of $G$, that is, the sets of pairwise disjoint edges. For
edge weights $w\colon E(G)\to\mathbb R$, the weighted version replaces $x^{|M|}$ by
$x^{|M|}\prod_{e\in M}w(e)$. The signed form is
$$
\mu_G(x)=\sum_k(-1)^k m_k\,x^{n-2k},
$$
where $m_k$ is the number of $k$-matchings and $n=|V(G)|$; for a vertex set $S$ we write
$\mu_S$ for the polynomial of the induced subgraph $G[S]$. Heilmann and Lieb use the signed
form $\mu_G$.

**Theorem (Heilmann--Lieb).** [@HeilmannLieb1972, Thm. 4.2] The polynomial $m_G(x)$ is
real-rooted. If all edge weights are nonnegative, the weighted polynomial is real-rooted with
nonnegative coefficients and nonpositive roots, that is, it is a Pólya frequency polynomial.

**Theorem (vertex deletion; Heilmann--Lieb, Godsil).** For every $S$ and $v\in S$,
$\mu_{S\setminus\{v\}}\ll\mu_S$. In particular $\mu_S$ is real-rooted.

**Theorem (root bound).** Let $\Delta\ge2$ and suppose every vertex of $G[S]$ has degree at most
$\Delta$. Then every root $r$ of $\mu_S$ satisfies $|r|\le2\sqrt{\Delta-1}$. Heilmann and Lieb
prove the strict inequality.

**Theorem (Engström).** [@Engstrom2007, Thm. 2.5] Let $G$ be a finite claw-free graph and let
$w\colon V(G)\to\mathbb R$ be nonnegative. Then
$$
I(G,w,x)=\sum_{A}x^{|A|}\prod_{v\in A}w(v),
$$
summed over the independent sets $A$ of $G$, is real-rooted.

**Theorem (rank-two binomial transform).** Let $p$ be a Pólya frequency polynomial with
$p(0)=1$, and let $M\ge\deg p$. Then
$$
\sum_{k=0}^{M}k!\Bigl(\sum_{j=0}^{\deg p}p_j\binom jk\binom{M-j}k\Bigr)x^k
$$
is a Pólya frequency polynomial. Its coefficient of $x^k$ is $p(1)$ times the weighted number
of $k$-matchings of the complete graph $K_M$ with edge weights $a_ib_j+a_jb_i\ge0$, for suitable
nonnegative vectors $a,b$ determined by $p$.

## Proof

The matchings of $G$ are the independent sets of the claw-free line graph $L(G)$, so the
weighted matching polynomial of $G$ is a weighted independence polynomial of $L(G)$ and
Engström's theorem applies. Engström's theorem is the weighted form of the
[Chudnovsky--Seymour theorem](rr:chudnovsky-seymour), proved by the same
induction on vertex subsets.

For vertex deletion, use $\mu_S=x\mu_{S\setminus v}-\sum_{u\sim v}\mu_{S\setminus\{v,u\}}$.
By induction each $\mu_{S\setminus\{v,u\}}$ interlaces $\mu_{S\setminus v}$, hence so does
their sum, and the three-term step gives $\mu_{S\setminus v}\ll\mu_S$. The same recurrence
gives the root bound.

For the transform, orienting each edge of a matching of $K_M$ shows that the weighted
$k$-matching number with weights $a_ib_j+a_jb_i$ is $k!$ times a sum over pairs of disjoint
$k$-subsets. Writing the coefficients of $p$ in this form with nonnegative $a,b$ gives that
the transform is $p(1)$ times a weighted matching polynomial of $K_M$.

## References

[@HeilmannLieb1972, Thm. 4.2]; C. D. Godsil, "Matchings and walks in graphs," *J. Graph
Theory* 5 (1981), 285–297; [@Engstrom2007, Thm. 2.5]; [@ChudnovskySeymour2007]. Background on
the [matching polynomial](sf:matchingPolynomial) and the
[weighted independence polynomial](sf:weightedIndependencePolynomial) is on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes the plain and weighted Heilmann–Lieb theorems, Engström's
weighted claw-free theorem, and the rank-two binomial transform.  The proofs
live in `RealRooted.HeilmannLieb`, `RealRooted.Graph.IndependencePolynomial.ClawFree`
and `RealRooted.RankTwoMatching`.
-/
