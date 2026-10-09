import RealRooted.HosterStump.PosetChow

/-!
# Hoster–Stump challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chow-polynomials-simplicial-posets"
authors = ["Hoster", "Stump"]
years = [2025]

[[definitions]]
name = "RealRooted.HosterStump.IsSimplicialPoset"
module = "RealRooted.HosterStump.PosetBasic"
label = "Graded simplicial poset: every lower interval is Boolean"

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
label = "Hoster–Stump: Chow polynomials of h-positive simplicial posets are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.HosterStump.isRealRooted_augChowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "Hoster–Stump: the augmented Chow polynomial is real-rooted"

[[theorems]]
name = "RealRooted.HosterStump.strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "Hoster–Stump: the dual Chow polynomial interlaces the augmented one"

[[theorems]]
name = "RealRooted.HosterStump.isSimplicialFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "Stanley's identity for the flag h-vector of a simplicial poset"

[[theorems]]
name = "RealRooted.HosterStump.isInterlacingDiagram_range"
module = "RealRooted.HosterStump.Step"
label = "The interlacing diagrams of the refined descent polynomials"
-->

<!-- realrooted-catalog-content -->
# Chow polynomials of simplicial posets

Let $P$ be a finite graded simplicial poset of rank $n$: every lower interval
$[\hat 0, x]$ is a Boolean lattice. Write $h_0, \dots, h_n$ for its $h$-vector and
$\beta(S)$ for the flag $h$-vector of $\hat P$, the poset $P$ with a top element added.
The Chow and augmented Chow polynomials of $\hat P$ are
$$
H_{\hat P}(x) = \sum_{\substack{S \subseteq \{2,\dots,n\}\\ S \text{ isolated}}}
  \beta(S)\, x^{|S|} (1+x)^{n-2|S|}, \qquad
H^{\mathrm{aug}}_{\hat P}(x) = \sum_{\substack{S \subseteq \{1,\dots,n\}\\ S \text{ isolated}}}
  \beta(S)\, x^{|S|} (1+x)^{n+1-2|S|},
$$
where a set is *isolated* if it contains no two consecutive integers.

**Theorem** (Hoster–Stump). If the $h$-vector of $P$ is nonnegative, then
$H_{\hat P}$, $H_{\hat P^*}$ and $H^{\mathrm{aug}}_{\hat P}$ are real-rooted, and the
roots of $H_{\hat P^*}$ interlace those of $H^{\mathrm{aug}}_{\hat P}$.

This covers Cohen–Macaulay simplicial posets and the lattices of flats of uniform matroids.

## Proof idea

By Stanley's identity, $\beta(S)$ is a nonnegative combination of the $h_k$ with
coefficients that count permutations of $n+1$ letters with first letter $k+1$ and a given
descent set. The $\gamma$-polynomials of the three palindromic Chow polynomials are
therefore $\sum_k h_k\, p^{T}_{n,k}$ for refined descent polynomials $p^{S \subseteq T}_{n,k}$.
Arranged in three rows, these polynomials form an *interlacing diagram*: every path
through the diagram is an interlacing sequence. The proof is by induction on $n$, using
partial sums and moving windows of interlacing sequences. Real-rootedness and interlacing
then pass from the $\gamma$-polynomials back to the Chow polynomials.

The formalization uses the zero-aware weak interlacing relation of the library. The paper's
convention that any two polynomials of degree at most one interlace would make its Lemma 2.3
false; the library records an explicit counterexample.

## References

E. Hoster and C. Stump, “Chow polynomials of simplicial posets with positive $h$-vector are
real-rooted,” arXiv:2508.15538 (2025); R. P. Stanley, *Combinatorics and Commutative
Algebra*, 2nd ed., Birkhäuser, 1996, III.6; L. Ferroni, J. P. Matherne and L. Vecchi, “Chow
functions for partially ordered sets,” 2024.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.HosterStump`.
-/
