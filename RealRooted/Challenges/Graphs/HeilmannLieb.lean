module

import RealRooted.Graph.MatchingPolynomial
import RealRooted.Graph.MatchingVertexInterlacing
import RealRooted.HeilmannLieb
import RealRooted.Mathlib.Combinatorics.SimpleGraph.MatchingPolyOn
import RealRooted.RookPolynomial

/-!
# Heilmann–Lieb theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "heilmann-lieb"
formalized = "2026-10-06"
references = [
  "HeilmannLieb1972",
  "Nijenhuis1976",
]
authors = ["Heilmann", "Lieb", "Nijenhuis", "Godsil"]
years = [1972, 1976, 1981]

[[definitions]]
name = "RealRooted.Graph.weightedMatchingPolynomialByEdges"
module = "RealRooted.Graph.MatchingPolynomial"
label = "Edge-weighted matching polynomial"

[[definitions]]
name = "SimpleGraph.matchingPolyOn"
module = "RealRooted.Mathlib.Combinatorics.SimpleGraph.MatchingPolyOn"
label = "Signed matching polynomial $μ_S$ of the induced subgraph $G[S]$"

[[definitions]]
name = "RealRooted.Rook.weightedRookPolynomial"
module = "RealRooted.RookPolynomial"
label = "Weighted rook polynomial"

[[theorems]]
objects = ["Matching polynomials"]
name = "RealRooted.Graph.matchingPolynomialByEdges_splits"
module = "RealRooted.HeilmannLieb"
label = "The matching polynomial of a finite graph is real-rooted"

[[theorems]]
name = "RealRooted.Graph.weightedMatchingPolynomialByEdges_splits"
module = "RealRooted.HeilmannLieb"
label = "Heilmann–Lieb: matching polynomials with nonnegative edge weights are real-rooted"
headline = true

[[theorems]]
objects = ["Weighted matching polynomials"]
property = "pf"
name = "RealRooted.Graph.weightedMatchingPolynomialByEdges_isPFPolynomial"
module = "RealRooted.HeilmannLieb"
label = "With nonnegative edge weights the matching polynomial is a PF polynomial"

[[theorems]]
objects = ["Matching polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_matchingPolyOn_erase"
module = "RealRooted.Graph.MatchingVertexInterlacing"
label = "Deleting a vertex gives an interlacing matching polynomial"

[[theorems]]
name = "RealRooted.abs_le_of_isRoot_matchingPolyOn"
module = "RealRooted.Graph.MatchingVertexInterlacing"
label = "With maximum degree Δ ≥ 2, every root satisfies |x| ≤ 2√(Δ − 1)"

[[theorems]]
name = "RealRooted.Rook.weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges"
module = "RealRooted.RookPolynomial"
label = "A weighted rook polynomial is a bipartite weighted matching polynomial"

[[theorems]]
objects = ["Weighted rook polynomials"]
property = "pf"
name = "RealRooted.Rook.weightedRookPolynomial_isPFPolynomial"
module = "RealRooted.RookPolynomial"
label = "Nijenhuis: rook polynomials with nonnegative weights are PF polynomials"

[[theorems]]
objects = ["Rook polynomials"]
property = "pf"
name = "RealRooted.Rook.rookPolynomial_isPFPolynomial"
module = "RealRooted.RookPolynomial"
label = "Rook polynomials of finite boards are PF polynomials"
-->

<!-- realrooted-catalog-content -->
# Heilmann–Lieb theorem

The matching polynomial of a finite graph is real-rooted, also with nonnegative edge weights,
and deleting a vertex gives a polynomial that interlaces it. Rook polynomials are matching
polynomials of complete bipartite graphs, so Nijenhuis's theorem is a special case.

## Results

Let $G$ be a finite simple graph and $w\colon E(G)\to[0,\infty)$. The *weighted matching
polynomial* is
$$
m_G(x)=\sum_{M}x^{|M|}\prod_{e\in M}w(e),
$$
where $M$ ranges over the matchings of $G$. For $S\subseteq V(G)$ let
$\mu_S(x)=\sum_k(-1)^km_k\,x^{|S|-2k}$, where $m_k$ is the number of $k$-matchings of $G[S]$.

**Theorem (Heilmann–Lieb).** [@HeilmannLieb1972, Thm. 4.2] The polynomial $m_G$ is real-rooted.
Its coefficients are nonnegative, so it is a Pólya frequency polynomial.

**Theorem (vertex deletion; Heilmann–Lieb, Godsil).** For every $S\subseteq V(G)$ and $v\in S$,
$\mu_{S\setminus\{v\}}\ll\mu_S$.

**Theorem (root bound).** If every vertex of $G[S]$ has at most $\Delta\ge2$ neighbours in $S$,
then every root $r$ of $\mu_S$ satisfies $|r|\le2\sqrt{\Delta-1}$.

**Corollary (Nijenhuis).** [@Nijenhuis1976] Let $A$ be a real matrix with nonnegative entries.
The weighted rook polynomial $\sum_Px^{|P|}\prod_{(i,j)\in P}A_{ij}$, summed over placements
$P$ of non-attacking rooks, is a Pólya frequency polynomial. It is the weighted matching
polynomial of the complete bipartite graph on rows and columns with edge weights $A_{ij}$.

## Use

Matchings of $G$ are independent sets of its line graph, which is claw-free, so the theorem is
the line-graph case of the [Chudnovsky–Seymour theorem](rr:chudnovsky-seymour). The root bound
$2\sqrt{\Delta-1}$ is the bound behind the construction of bipartite Ramanujan graphs by Marcus,
Spielman and Srivastava.

## Proof

For vertex deletion we use
$\mu_S=x\,\mu_{S\setminus\{v\}}-\sum_{u\sim v}\mu_{S\setminus\{u,v\}}$. By induction on $|S|$
each $\mu_{S\setminus\{u,v\}}$ interlaces $\mu_{S\setminus\{v\}}$, hence so does their sum
([Wagner's lemma](rr:interlacing)), and the three-term step gives
$\mu_{S\setminus\{v\}}\ll\mu_S$. The same recurrence gives the root bound. The weighted theorem
is the line-graph case of Engström's weighted form of the Chudnovsky–Seymour theorem.

## References

[@HeilmannLieb1972, Thm. 4.2]; C. D. Godsil, "Matchings and walks in graphs," *J. Graph
Theory* 5 (1981), 285–297; [@Nijenhuis1976]. See also the
[matching polynomial](sf:matchingPolynomial) and [rook polynomials](sf:rookPolynomial) on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
