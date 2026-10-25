module

public import RealRooted.CombinatorialExamples.ColoredSetPartitions
public import RealRooted.CombinatorialExamples.Motzkin
public import RealRooted.CombinatorialExamples.PathPowerIndependence
public import RealRooted.CombinatorialExamples.Simsun
public import RealRooted.CombinatorialExamples.SingletonFreeSetPartitions
public import RealRooted.CombinatorialExamples.StirlingPermutations
public import RealRooted.CombinatorialExamples.SturmDerangementsExc
public import RealRooted.CombinatorialExamples.Touchard

/-!
# Sturm sequences from derivative recurrences

<!-- realrooted-catalog
version = 1
section = "families"
slug = "sturm-sequence-families"
formalized = "2026-05-12"
references = [
  "GesselStanley1978",
  "MantaciRakotondrajao2003",
  "Bona2009",
  "ChowShiu2011",
  "Wang2014",
  "BonaHezo2016",
]
authors = ["Gessel", "Stanley", "Bóna", "Mantaci", "Rakotondrajao", "Chow", "Shiu", "Mező",
  "Wang"]
years = [1978, 2003, 2009, 2011, 2014, 2016]

[[definitions]]
name = "RealRooted.touchard"
module = "RealRooted.Touchard"
label = "Touchard polynomials"

[[definitions]]
name = "RealRooted.stirlingPermutations"
module = "RealRooted.CombinatorialExamples.StirlingPermutations"
label = "Stirling-permutation descent polynomials"

[[definitions]]
name = "RealRooted.sturmDerangementsExc"
module = "RealRooted.CombinatorialExamples.SturmDerangementsExc"
label = "Derangement polynomials by excedances"

[[definitions]]
name = "RealRooted.simsun"
module = "RealRooted.CombinatorialExamples.Simsun"
label = "Simsun descent polynomials"

[[definitions]]
name = "RealRooted.singletonFreeSetPartitions"
module = "RealRooted.CombinatorialExamples.SingletonFreeSetPartitions"
label = "Set partitions without singleton blocks"

[[definitions]]
name = "RealRooted.coloredSetPartitions"
module = "RealRooted.CombinatorialExamples.ColoredSetPartitions"
label = "Colored set-partition polynomials"

[[theorems]]
name = "RealRooted.interlaces_touchard_succ"
module = "RealRooted.CombinatorialExamples.Touchard"
label = "Consecutive Touchard polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.coeff_touchard_eq_stirlingSecond"
module = "RealRooted.CombinatorialExamples.Touchard"
label = "Touchard coefficients are Stirling numbers of the second kind"

[[theorems]]
name = "RealRooted.interlaces_stirlingPermutations_succ"
module = "RealRooted.CombinatorialExamples.StirlingPermutations"
label = "Consecutive Stirling-permutation descent polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.interlaces_sturmDerangementsExc_succ"
module = "RealRooted.CombinatorialExamples.SturmDerangementsExc"
label = "Consecutive derangement polynomials interlace"

[[theorems]]
name = "RealRooted.strictInterl_simsun_succ"
module = "RealRooted.CombinatorialExamples.Simsun"
label = "Consecutive simsun polynomials interlace"

[[theorems]]
name = "RealRooted.Challenges.SturmSequenceFamilies.strictInterl_singletonFreeSetPartitions_succ"
label = "Consecutive singleton-free set-partition polynomials interlace"

[[theorems]]
name = "RealRooted.interlaces_coloredSetPartitions_succ"
module = "RealRooted.CombinatorialExamples.ColoredSetPartitions"
label = "Consecutive colored set-partition polynomials interlace"

[[theorems]]
name = "RealRooted.touchard_eq_coloredSetPartitions_zero_one"
module = "RealRooted.CombinatorialExamples.Touchard"
label = "Touchard polynomials are colored set-partition polynomials with c = 0, m = 1"

[[theorems]]
name = "RealRooted.isRealRooted_motzkin"
module = "RealRooted.CombinatorialExamples.Motzkin"
label = "Motzkin polynomials are real-rooted"

[[theorems]]
name = "RealRooted.strictInterl_motzkin_succ"
module = "RealRooted.CombinatorialExamples.Motzkin"
label = "Consecutive Motzkin polynomials interlace"

[[theorems]]
name = "RealRooted.splits_sum_choose_sub_mul"
module = "RealRooted.CombinatorialExamples.PathPowerIndependence"
label = "Independence polynomials of path powers ∑ C(m − rk, k) xᵏ are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Sturm sequences from derivative recurrences

For nonzero real-rooted polynomials $f$ and $g$ we write $f \ll g$
(`StrictInterl f g`) as on the [interlacing page](/RealRooted/concepts/interlacing/),
and `Interlaces f g` when moreover $\deg g = \deg f + 1$.

Each family below is **defined by its recurrence**. The combinatorial
interpretations are cited, not formalized. The one exception is the Touchard
family, whose coefficients are proved to be Stirling numbers of the second kind.

- **Touchard** (`touchard`): $T_0 = 1$ and $T_{n+1} = x T_n + x T_n'$. Then
  `Interlaces` $T_n$ $T_{n+1}$ for all $n$.
- **Stirling permutations** (`stirlingPermutations`): $P_0 = 1$ and
  $P_{n+1} = (2n+1)x P_n + x(1-x) P_n'$. Then `Interlaces` $P_n$ $P_{n+1}$ for
  all $n$.
- **Derangements** (`sturmDerangementsExc`): $P_0 = P_1 = 0$, $P_2 = x$ and
  $P_{n+3} = x\bigl((n+2) P_{n+1} + (n+2) P_{n+2} + (1-x) P_{n+2}'\bigr)$. Then
  `Interlaces` $P_n$ $P_{n+1}$ for all $n \geq 2$.
- **Simsun permutations** (`simsun`): $P_0 = 1$ and
  $P_{n+1} = (1 + nx) P_n + x(1-2x) P_n'$. Then $P_n \ll P_{n+1}$ for all $n$.
- **Singleton-free set partitions** (`singletonFreeSetPartitions`): $D_0 = 1$,
  $D_1 = 0$ and $D_{n+2} = x\bigl((n+1) D_n + D_{n+1}'\bigr)$. Then
  $D_n \ll D_{n+1}$ for all $n \geq 2$.
- **Colored set partitions** (`coloredSetPartitions c m`): $T_0 = 1$ and
  $T_{n+1} = (x + c) T_n + m x T_n'$. Then `Interlaces` $T_n$ $T_{n+1}$ for all
  $n$.

The parameters $c$ and $m$ of the colored family are natural numbers. The
Touchard polynomials are the case $c = 0$, $m = 1$, and $c = 1$, $m = 2$ gives
the type $B$ set partitions of D. Wang. Furthermore,
$$
T_n(x) = \sum_{k} S(n, k)\, x^k,
$$
where $S(n, k)$ is the Stirling number of the second kind (`Nat.stirlingSecond`).

The degree of the simsun polynomial does not rise at every step, so its
consecutive members are related by $\ll$ rather than by `Interlaces`. In the
derangement and singleton-free families the polynomial $P_1$, respectively
$D_1$, is zero, so interlacing starts at index $2$.

Classically, $T_n$ counts set partitions of $\{1, \dotsc, n\}$ by blocks, the
Stirling-permutation polynomials count Stirling permutations by descents, the
derangement polynomials count derangements of $\{1, \dotsc, n\}$ by
excedances, the simsun polynomials count simsun permutations of
$\{1, \dotsc, n\}$ by descents, and $D_n$ counts set partitions of
$\{1, \dotsc, n\}$ without singleton blocks by blocks.

Two further families: the Motzkin polynomials, defined by their three-term
recurrence, are real-rooted and consecutive ones interlace. For all $r$ and $m$
the polynomial $\sum_k \binom{m - rk}{k} x^k$ is real-rooted; for $r \le m$ it
is the independence polynomial of the $r$-th power of a path, a claw-free
graph, so real-rootedness also follows from the
[Chudnovsky–Seymour theorem](/RealRooted/theorems/chudnovsky-seymour/).

## Proof idea

In the first-order recurrences, $P_{n+1} = u P_n + v P_n'$, where $v$ is one
of $x$, $x(1-x)$, $x(1-2x)$ and $mx$. The polynomial $P_n$ has nonnegative
coefficients, so its zeros are nonpositive and $v$ is nonpositive there. The
Liu–Wang criterion with the interlacer $P_n' \ll P_n$ then gives
$P_n \ll P_{n+1}$. In the derangement and singleton-free recurrences, the
earlier row enters with a nonnegative coefficient, and Wagner's lemma on
nonnegative combinations of common interlacers handles the extra term.

## References

See [@GesselStanley1978; @MantaciRakotondrajao2003; @Bona2009;
@ChowShiu2011; @Wang2014; @BonaHezo2016]. See also the
[Touchard polynomials](sf:touchardPolynomial),
[Stirling permutations](sf:stirlingPermutationDescentPolynomial), the
[derangement polynomials](sf:derangementPolynomial), and the
[Motzkin-polynomial theorem](sf:motzkinPolynomialsRealRooted)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

The families and their interlacing proofs live in
`RealRooted.CombinatorialExamples`.
-/

@[expose] public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace SturmSequenceFamilies

/-- Consecutive singleton-free set-partition polynomials satisfy `D n ≪ D (n + 1)` for
`n ≥ 2`. -/
theorem strictInterl_singletonFreeSetPartitions_succ {n : ℕ} (hn : 2 ≤ n) :
    StrictInterl (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1)) :=
  RealRooted.strictInterl_singletonFreeSetPartitions_succ n hn

end SturmSequenceFamilies
end Challenges
end RealRooted
