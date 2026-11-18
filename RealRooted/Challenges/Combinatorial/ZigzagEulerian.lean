module

import RealRooted.CenteredEulerian.Basis
import RealRooted.CenteredEulerian.ColumnBound
import RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions
import RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted
import RealRooted.IntervalDifferential.Basic
import RealRooted.IntervalDifferential.LinearInsertion
import RealRooted.IntervalDifferential.MobiusRoots
import RealRooted.IntervalDifferential.QuadraticInsertion
import RealRooted.IntervalDifferential.UniversalTransfer

/-!
# Zig-zag Eulerian polynomials

<!-- realrooted-catalog
version = 1
kind = "conjecture"
conjecture = "Petersen–Zhuang (2024), Conjecture 6.1(a)"
section = "families"
slug = "zigzag-eulerian"
formalized = "2026-10-23"
tags = ["coauthored-paper"]
references = [
  "Alexandersson2026Eulerian",
  "PetersenZhuang2024x",
  "CoonsSullivant2023",
]
authors = ["Petersen", "Zhuang", "Alexandersson"]
years = [2024, 2026]

[[definitions]]
name = "RealRooted.ZigzagEulerian.IsUpDown"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions"
label = "Alternating permutations"

[[definitions]]
name = "RealRooted.ZigzagEulerian.swapCount"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions"
label = "Swap statistic"

[[definitions]]
name = "RealRooted.ZigzagEulerian.zigzagEulerianPolynomial"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions"
label = "Zig-zag Eulerian polynomial"

[[definitions]]
name = "RealRooted.CenteredEulerian.polynomial"
module = "RealRooted.CenteredEulerian.Basis"
label = "Centered polynomial $p_n(c)$"

[[definitions]]
name = "RealRooted.IntervalDifferential.zigzagOperator"
module = "RealRooted.IntervalDifferential.Basic"
label = "The centered zigzag differential operator L"

[[theorems]]
objects = ["Zig-zag Eulerian polynomials"]
name = "RealRooted.ZigzagEulerian.zigzagEulerianPolynomial_roots"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted"
label = "Zig-zag Eulerian polynomials have simple negative roots"
headline = true

[[theorems]]
name = "RealRooted.CenteredEulerian.polynomial_root_normSq_lt"
module = "RealRooted.CenteredEulerian.ColumnBound"
label = "Complex zeros of the centered polynomials satisfy |c|² < 13/3"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagLinearFactor_roots"
module = "RealRooted.IntervalDifferential.LinearInsertion"
label = "Inserting a real factor inserts a simple root into each gap"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagQuadraticFactor_roots"
module = "RealRooted.IntervalDifferential.QuadraticInsertion"
label = "Inserting a conjugate pair in the disk of squared radius 13/3 keeps simple interval roots"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagTransform_parity_roots_of_disk"
module = "RealRooted.IntervalDifferential.UniversalTransfer"
label = "A parity polynomial with all roots in the disk transforms to simple roots in (−1, 1)"

[[theorems]]
name = "RealRooted.IntervalDifferential.splits_roots_nodup_neg_of_mobius_eval"
module = "RealRooted.IntervalDifferential.MobiusRoots"
label = "The map (z − 1)/(z + 1) carries simple roots in (−1, 1) to simple negative roots"
-->

<!-- realrooted-catalog-content -->
# Zig-zag Eulerian polynomials

The zig-zag Eulerian polynomials count alternating permutations by swaps. They have only
simple negative roots, which settles a conjecture of Petersen and Zhuang. The proof bounds the
zeros of a centered family in a disk and transfers this bound through a differential operator.

## Results

Let $H_n(t)=\sum_\pi t^{\operatorname{sw}(\pi)}$ over the permutations $\pi$ of $[n]$ with
$\pi_1<\pi_2>\pi_3<\dotsb$, where a *swap* of $\pi$ is a value $i$ with
$\pi^{-1}(i)+1<\pi^{-1}(i+1)$ and $\operatorname{sw}(\pi)$ is the number of swaps. Then
$H_1=H_2=1$, $H_3=1+t$ and $H_4=1+3t+t^2$.

**Theorem (Alexandersson).** [@Alexandersson2026Eulerian, Thm. 7.1] For every $n\ge1$, $H_n$
has degree $\max(n-2,0)$ and only simple negative roots. Hence $Z_n(t)=tH_n(t)$ is
real-rooted, as conjectured in [@PetersenZhuang2024x, Conj. 6.1(a)].

**Theorem (disk bound).** [@Alexandersson2026Eulerian, Lemma 7.3] Let
$$
\sum_{n\geq 0} p_n(c)\, s^n = \sqrt{1-s^2}\,(\sec + \tan)\bigl(c \arcsin s\bigr).
$$
For $n \geq 2$, every complex zero $c$ of $p_n$ satisfies $|c|^2 < 13/3$.

**Theorem (transfer).** [@Alexandersson2026Eulerian, Lemma 7.4] Let
$LF = (x^2-1)\,F' + 3x\,F$, and call a polynomial *interval-simple* if it has only simple real
roots, all in $(-1,1)$. If $F\ne0$ is interval-simple and $-3<a<3$, then $(L-a)F$ is
interval-simple; if $F$ is interval-simple of degree at least $4$ and $a^2+b^2\le 13/3$, then
$\bigl((L-a)^2+b^2\bigr)F$ is interval-simple. Consequently, if $Q\ne0$ has degree at least
$3$, $Q(-x)=\pm Q(x)$ and every root of $Q$ satisfies $|c|^2\le 13/3$, then $Q(L)\,1$ is
interval-simple.

## Proof

For $n\ge2$, $p_n(c)$ is divisible by $c^2-1$, and with $Q_n=p_n/(c^2-1)$ we have
$(z+1)^{n-2}H_n\bigl((z-1)/(z+1)\bigr)=\text{const}\cdot Q_n(L)\,1$. The disk bound comes from
a Riccati equation for the generating function and a column-sum estimate for multiplication by
$c^2$ in the centered basis. The transfer theorem inserts the real and conjugate-pair factors of
$Q_n$ one at a time, and $z\mapsto(z-1)/(z+1)$ maps $(-1,1)$ onto the negative real axis.

## References

[@Alexandersson2026Eulerian, Thm. 7.1]; [@PetersenZhuang2024x, Conj. 6.1(a)];
[@CoonsSullivant2023].
<!-- /realrooted-catalog-content -->
-/
