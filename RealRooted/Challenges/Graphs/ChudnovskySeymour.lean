module

public import RealRooted.Graph.ClawFree
public import RealRooted.Graph.IndependencePolynomial.Basic
public import RealRooted.Graph.IndependencePolynomial.ClawFree
public import RealRooted.HeilmannLieb

/-!
# Chudnovsky--Seymour challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chudnovsky-seymour"
formalized = "2026-07-09"
tags = []
references = [
  "ChudnovskySeymour2007",
]
authors = ["Chudnovsky", "Seymour"]
years = [2007]

[[definitions]]
name = "RealRooted.Graph.ClawFree"
module = "RealRooted.Graph.ClawFree"
label = "Claw-free graph"

[[definitions]]
name = "RealRooted.Graph.indepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Basic"
label = "Independence polynomial"

[[theorems]]
name = "RealRooted.Graph.clawFree_indepPoly_splits"
module = "RealRooted.Graph.IndependencePolynomial.ClawFree"
label = "Chudnovsky–Seymour: claw-free graphs have real-rooted independence polynomials"

[[theorems]]
name = "RealRooted.Graph.clawFree_weightedIndepPoly_splits"
module = "RealRooted.Graph.IndependencePolynomial.ClawFree"
label = "Weighted independence polynomials of claw-free graphs are real-rooted"
headline = true
symcat = "weightedIndependencePolynomial"
-->

<!-- realrooted-catalog-content -->
# Claw-free independence polynomials

The independence polynomial of a finite claw-free graph is real-rooted, also with nonnegative
vertex weights.

## Results

A graph is *claw-free* if no vertex has three pairwise non-adjacent neighbors. The independence
polynomial of a finite graph $G$ is $\sum_A x^{|A|}$, summed over the independent sets $A$ of
$G$.

**Theorem (Chudnovsky--Seymour).** If $G$ is a finite claw-free graph, then its independence
polynomial is real-rooted [@ChudnovskySeymour2007].

**Theorem (weighted form).** Let $G$ be a finite claw-free graph and let $w(v)\ge0$ for every
vertex $v$. Then
$$
\sum_A x^{|A|}\prod_{v\in A}w(v)
$$
is real-rooted. This is due to Engstr\"om; see the
[Heilmann--Lieb page](rr:heilmann-lieb).

## References

[@ChudnovskySeymour2007]. Background on claw-free graphs is on
[symmetricfunctions.com](sf:clawFreeGraph).
<!-- /realrooted-catalog-content -->

Human statement:
sf:clawFreeGraph

Original publication: M. Chudnovsky and P. Seymour, "The roots of the
independence polynomial of a clawfree graph", J. Combin. Theory Ser. B 97
(2007), 350--357.

This module states the Chudnovsky--Seymour theorem for finite graphs.
-/
