import RealRooted.HeilmannLieb
import RealRooted.RankTwoMatching.Transform
import RealRooted.Graph.MatchingVertexInterlacing

/-!
# Heilmann–Lieb challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "heilmann-lieb"
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
name = "RealRooted.Graph.rankTwoBinomialTransform"
module = "RealRooted.RankTwoMatching.Transform"
label = "Rank-two binomial transform"

[[theorems]]
name = "RealRooted.Challenges.HeilmannLieb.matchingPolynomial_splits"
label = "Heilmann–Lieb: the matching polynomial is real-rooted"
headline = true

[[theorems]]
name = "RealRooted.interlaces_matchingPolyOn_erase"
module = "RealRooted.Graph.MatchingVertexInterlacing"
label = "Deleting a vertex interlaces the matching polynomial"

[[theorems]]
name = "RealRooted.Challenges.HeilmannLieb.clawFree_weightedIndepPoly_splits"
label = "Engström: weighted independence polynomials of claw-free graphs are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Challenges.HeilmannLieb.weightedMatchingPolynomial_splits"
label = "Weighted matching polynomials are real-rooted"

[[theorems]]
name = "RealRooted.Challenges.HeilmannLieb.weightedMatchingPolynomial_isPFPolynomial"
label = "Weighted matching polynomials are PF polynomials"

[[theorems]]
name = "RealRooted.Challenges.HeilmannLieb.rankTwoBinomialTransform_isPFPolynomial"
label = "The rank-two binomial transform preserves PF polynomials"
-->

<!-- realrooted-catalog-content -->
# The Heilmann–Lieb theorem

Let $G$ be a finite simple graph. Its **matching-generating polynomial** is
$$
m_G(x) = \sum_{M} x^{|M|},
$$
where $M$ ranges over the matchings of $G$, that is, the sets of pairwise
disjoint edges. Given edge weights $w \colon E(G) \to \mathbb{R}$, the
weighted version replaces $x^{|M|}$ by $\prod_{e \in M} w(e)\, x^{|M|}$.

**Theorem** (Heilmann–Lieb). The polynomial $m_G(x)$ is real-rooted. More
generally, if all edge weights are nonnegative, then the weighted
matching-generating polynomial is real-rooted with nonnegative coefficients
and nonpositive zeros, so its coefficients form a Pólya frequency sequence.

We formalize the generating form $m_G(x)$ used on symmetricfunctions.com,
and also the signed form
$$
\mu_G(x) = \sum_k (-1)^k m_k x^{n-2k}
$$
of Heilmann and Lieb, where $m_k$ is the number of $k$-matchings and
$n = |V(G)|$.

**Theorem** (Heilmann–Lieb, Godsil). For every vertex $v$, the polynomial
$\mu_{G - v}$ interlaces $\mu_G$. In particular $\mu_G$ is real-rooted.

**Theorem** (Engström). Let $G$ be a finite claw-free graph and let
$w \colon V(G) \to \mathbb{R}$ be nonnegative vertex weights. Then the
weighted independence polynomial
$$
I(G, w, x) = \sum_{A} x^{|A|} \prod_{v \in A} w(v),
$$
where $A$ ranges over the independent sets of $G$, is real-rooted.

**Corollary.** Let $p$ be a polynomial with nonnegative coefficients,
nonpositive real zeros, and $p(0) = 1$, and let $M \geq \deg p$. Then the
rank-two binomial transform
$$
\sum_{k=0}^{M} k! \left( \sum_{j=0}^{\deg p} p_j \binom{j}{k} \binom{M-j}{k}
\right) x^k
$$
also has nonnegative coefficients and nonpositive real zeros.

## Proof idea

Engström's theorem is the weighted form of the
[Chudnovsky–Seymour theorem](/RealRooted/theorems/chudnovsky-seymour/), and we
prove it by the same induction on vertex subsets, which shows that the
polynomials obtained by deleting closed neighborhoods are compatible. The
matchings of $G$ are exactly the independent sets of the line graph $L(G)$,
which is claw-free, so the weighted matching polynomial of $G$ is the
weighted independence polynomial of $L(G)$. Nonnegative coefficients then
force the zeros to be nonpositive. For the corollary, we write the
coefficients of $p$ through rank-two edge weights $a_i b_j + a_j b_i \geq 0$
on the complete graph $K_M$; the transform is then $p(1)$ times the weighted
matching polynomial of $K_M$.

The vertex-deletion theorem follows from the recurrence
$\mu_G = x\,\mu_{G-v} - \sum_{u \sim v} \mu_{G-v-u}$. By induction every
$\mu_{G-v-u}$ interlaces $\mu_{G-v}$, so their sum does too, and the
three-term step gives $\mu_{G-v} \ll \mu_G$.

## References

O. J. Heilmann and E. H. Lieb, “Theory of monomer-dimer systems,” *Comm.
Math. Phys.* 25 (1972), 190–232, Theorem 4.2; C. D. Godsil, “Matchings and
walks in graphs,” *J. Graph Theory* 5 (1981), 285–297; A. Engström, “Inequalities on
well-distributed point sets on circles,” *J. Inequal. Pure Appl. Math.* 8
(2007), Theorem 2.5; M. Chudnovsky and P. Seymour, “The roots of the
independence polynomial of a clawfree graph,” *J. Combin. Theory Ser. B* 97
(2007), 350–357. See the
[matching polynomial](https://www.symmetricfunctions.com/realRootedGraphs.htm#matchingPolynomial)
and the
[weighted independence polynomial](https://www.symmetricfunctions.com/realRootedGraphs.htm#weightedIndependencePolynomial)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes the plain and weighted Heilmann–Lieb theorems, Engström's
weighted claw-free theorem, and the rank-two binomial transform.  The proofs
live in `RealRooted.HeilmannLieb`, `RealRooted.Graph.IndependencePolynomial.ClawFree`
and `RealRooted.RankTwoMatching`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace HeilmannLieb

/-- **Heilmann–Lieb**: the matching-generating polynomial of a finite graph is
real-rooted. -/
theorem matchingPolynomial_splits {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (Graph.matchingPolynomialByEdges G).Splits :=
  Graph.matchingPolynomialByEdges_splits G

/-- **Weighted Heilmann–Lieb**: the edge-weighted matching-generating
polynomial is real-rooted for nonnegative weights. -/
theorem weightedMatchingPolynomial_splits {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (wt : G.edgeSet → ℝ) (hwt : ∀ e, 0 ≤ wt e) :
    (Graph.weightedMatchingPolynomialByEdges G wt).Splits :=
  Graph.weightedMatchingPolynomialByEdges_splits G wt hwt

/-- For nonnegative edge weights, the weighted matching-generating polynomial
has nonnegative coefficients and only real nonpositive roots. -/
theorem weightedMatchingPolynomial_isPFPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (wt : G.edgeSet → ℝ) (hwt : ∀ e, 0 ≤ wt e) :
    IsPFPolynomial (Graph.weightedMatchingPolynomialByEdges G wt) :=
  Graph.weightedMatchingPolynomialByEdges_isPFPolynomial G wt hwt

/-- **Engström**: the vertex-weighted independence polynomial of a finite
claw-free graph is real-rooted for nonnegative weights. -/
theorem clawFree_weightedIndepPoly_splits {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : Graph.ClawFree G) (wt : V → ℝ)
    (hwt : ∀ v, 0 ≤ wt v) :
    (Graph.weightedIndepPoly G wt).Splits :=
  Graph.clawFree_weightedIndepPoly_splits hG wt hwt

/-- The rank-two binomial transform maps a PF polynomial with constant term
one to a PF polynomial, provided the ambient size bounds the degree. -/
theorem rankTwoBinomialTransform_isPFPolynomial {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hconst : p.coeff 0 = 1) {M : ℕ} (hdeg : p.natDegree ≤ M) :
    IsPFPolynomial (Graph.rankTwoBinomialTransform p M) :=
  Graph.rankTwoBinomialTransform_isPF hp hconst hdeg

end HeilmannLieb
end Challenges
end RealRooted
