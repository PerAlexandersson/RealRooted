module

import RealRooted.CombinatorialExamples.CycleTypeDescents.DistinctParts
import RealRooted.CombinatorialExamples.CycleTypeDescents.PrimePowers
import RealRooted.CombinatorialExamples.CycleTypeDescents.RepeatedParts
import RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes
import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import RealRooted.CombinatorialExamples.LongCycleDescents.SmallMixtures
import RealRooted.CombinatorialExamples.LongCycleDescents.Words
import RealRooted.IntervalDifferential.DiskTransfer

/-!
# Descent polynomials of permutations with long cycles

<!-- realrooted-catalog
version = 1
kind = "conjecture"
conjecture = "Alexandersson (2026), descents of permutations with long cycles"
section = "theorems"
slug = "long-cycle-descents"
formalized = "2026-11-26"
references = [
  "Alexandersson2026Eulerian",
  "Branden2006",
]
authors = ["Bowen Zuo", "Alexandersson"]
years = [2026]
symcat = ["conjLongCycleDescents"]

[[definitions]]
name = "RealRooted.LongCycleDescents.HasLongCycles"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.Words"
label = "All cycles of a permutation have length at least $k$"

[[definitions]]
name = "RealRooted.LongCycleDescents.descentPolynomial"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.Words"
label = "Descent polynomial $D_{n,k}$ of the permutations with all cycles of length at least $k$"

[[definitions]]
name = "RealRooted.LongCycleDescents.realDescentPolynomial"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.Boundary"
label = "The polynomial $D_{n,k}$ over the reals"

[[theorems]]
objects = ["Descent polynomials of permutations with long cycles"]
property = "real-rooted"
name = "RealRooted.LongCycleDescents.realDescentPolynomial_splits"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes"
label = "Zuo: $D_{n,k}$ is real-rooted for all $n≥k≥3$"
headline = true

[[theorems]]
name = "RealRooted.LongCycleDescents.common_isolating_intervals"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes"
label = "The rows $D_{n,k}$, $3≤k≤n$, share isolating intervals for $n≥3$, $n≠5$"

[[theorems]]
objects = ["Mixtures of long-cycle descent polynomials"]
name = "RealRooted.LongCycleDescents.long_mixture_roots"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes"
label = "Nonnegative mixtures of the rows $D_{n,k}$, $k≥3$: nonpositive roots, simple for $n≠5$"

[[theorems]]
name = "RealRooted.LongCycleDescents.long_mixture_roots_nodup_iff"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes"
label = "Such a mixture has simple roots exactly when $n≠5$"

[[theorems]]
name = "RealRooted.LongCycleDescents.all_cutoffs_splits"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes"
label = "Every cutoff $1≤k≤n$ splits, including the Eulerian and derangement cases"

[[theorems]]
name = "RealRooted.LongCycleDescents.mixture_four_roots"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.SmallMixtures"
label = "Mixtures of the four rows for $n=4$, with cutoffs 1 and 2, split"

[[theorems]]
name = "RealRooted.LongCycleDescents.mixture_five_roots"
module = "RealRooted.CombinatorialExamples.LongCycleDescents.SmallMixtures"
label = "Mixtures of the five rows for $n=5$, with cutoffs 1 and 2, split"

[[theorems]]
name = "RealRooted.IntervalDifferential.intervalSpectralApply_one_roots"
module = "RealRooted.IntervalDifferential.DiskTransfer"
label = "Operator insertion: roots of $Q$ in radius $5/4$, $p_2≥-2$ ⇒ simple zeros in $(-1,1)$"

[[theorems]]
objects = ["Descent polynomials of conjugacy classes with distinct cycle lengths"]
name = "RealRooted.CycleTypeDescents.realDescentPolynomial_isRealRootedIn"
module = "RealRooted.CombinatorialExamples.CycleTypeDescents.DistinctParts"
label = "Distinct cycle lengths $≥3$ give a real-rooted class polynomial with nonpositive roots"

[[theorems]]
name = "RealRooted.CycleTypeDescents.realDescentPolynomial_isRealRooted_prime_pow"
module = "RealRooted.CombinatorialExamples.CycleTypeDescents.PrimePowers"
label = "A single cycle of prime-power length $≥3$ gives a real-rooted polynomial"

[[theorems]]
name = "RealRooted.CycleTypeDescents.exists_nonreal_root_realDescentPolynomial_three_three"
module = "RealRooted.CombinatorialExamples.CycleTypeDescents.RepeatedParts"
label = "Counterexample: the cycle type $(3,3)$ has a nonreal zero"
-->

<!-- realrooted-catalog-content -->
# Descent polynomials of permutations with long cycles

Let $D_{n,k}(t)=\sum_\pi t^{\operatorname{des}\pi}$ over the permutations $\pi$ of $[n]$ all of
whose cycles have length at least $k$. Alexandersson conjectured that $D_{n,k}$ is real-rooted;
Bowen Zuo proved it for $3\le k\le n$ and all $n$. The cutoffs $k=1,2$ are the Eulerian and
derangement cases [@Alexandersson2026Eulerian].

## Results

**Theorem (Zuo).** For $3\le k\le n$, $D_{n,k}$ is real-rooted. More precisely, for $n\ge3$ and
$n\ne5$, every nonzero nonnegative mixture of the rows $D_{n,k}$, $k\ge3$, has simple
nonpositive roots, and the rows share common isolating intervals. At $n=5$ a repeated root occurs.

Zuo's proof [Zuo, v1.0.0](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/releases/tag/v1.0.0)
combines sign evaluations on a mesh with finite certificates; his archive includes a complete
formalization.
Mixtures that include the cutoff-1 and cutoff-2 rows are formalized here only for $n\le5$.

**Cycle types.** For distinct cycle lengths $\ge3$ the class polynomial is real-rooted, by a
diamond-product argument and Brändén's theorem [@Branden2006]. A single cycle of prime-power
length is also real-rooted. Repeated parts can fail: the type $(3,3)$ has a nonreal zero.

## Proof

The formalization follows a shorter operator proof. The Gessel–Reutenauer alphabet polynomial
factors as $q(q^2-1)Q(q)$. With $z=(1+t)/(1-t)$ and $L=(z^2-1)\,d/dz+4z$,
$$
D_{n,k}(t)=6t(1-t)^{n-3}\,[Q(L/2)\,1](z).
$$
Inserting the factors of $Q$ one at a time keeps the zeros simple in $(-1,1)$ when the roots of
$Q$ lie in the disk of radius $5/4$ and their second power sum is at least $-2$. This is the
reusable interval-differential theorem. A coefficient bound gives these hypotheses for $n\ge18$,
and a proved kernel checker covers $n\le17$.

Parts are adapted from Bowen Zuo's formalization (Apache-2.0).

## References

[@Alexandersson2026Eulerian, Thm. 2.1]; [@Branden2006, Thm. 3.13];
[Zuo, Real zeros of descent polynomials for permutations with a minimum cycle length (2026)](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/releases/tag/v1.0.0).
<!-- /realrooted-catalog-content -->
-/
