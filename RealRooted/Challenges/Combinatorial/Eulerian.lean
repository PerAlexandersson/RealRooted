module

import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.CombinatorialExamples.EulerianStatistic
import RealRooted.CombinatorialExamples.TypeBEulerian
import RealRooted.GeneralizedEulerian
import RealRooted.GeneralizedEulerian.GeneratingFunction

/-!
# Eulerian polynomials

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "families"
slug = "eulerian"
formalized = "2026-07-10"
references = [
  "Frobenius1910",
  "Brenti1994",
]
authors = ["Frobenius", "Brenti"]
years = [1910, 1994]

[[definitions]]
name = "RealRooted.eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Shifted Eulerian polynomials $P_n = t A_{n+1}$"

[[definitions]]
name = "RealRooted.typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Type B Eulerian polynomials"

[[definitions]]
name = "RealRooted.generalizedEulerian"
module = "RealRooted.GeneralizedEulerian"
label = "Generalized Eulerian polynomials"

[[theorems]]
objects = ["Eulerian polynomials"]
name = "RealRooted.isRealRooted_eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Frobenius: the Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
objects = ["Eulerian polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_eulerianTilde_succ"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Consecutive Eulerian polynomials interlace"

[[theorems]]
objects = ["Type B Eulerian polynomials"]
name = "RealRooted.isRealRooted_typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Brenti: the type B Eulerian polynomials are real-rooted"

[[theorems]]
objects = ["Type B Eulerian polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_typeBEulerian_succ"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Consecutive type B Eulerian polynomials interlace"

[[theorems]]
objects = ["Generalized Eulerian polynomials"]
name = "RealRooted.generalizedEulerian_splits"
module = "RealRooted.GeneralizedEulerian"
label = "For $c > 0$, $E_n^{(c)}$ is real-rooted"

[[theorems]]
objects = ["Generalized Eulerian polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_generalizedEulerian_succ"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "For $c > 0$, $E_n^{(c)}$ interlaces $E_{n+1}^{(c)}$"

[[theorems]]
name = "RealRooted.eulerianTilde_eq_X_mul_generalizedEulerian_one"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "The shifted Eulerian polynomial $P_n$ equals $t E_n^{(1)}$"

[[theorems]]
name = "RealRooted.typeBEulerian_eq_generalizedEulerian_two"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "The type B Eulerian polynomial $B_n$ equals $E_n^{(2)}$"

[[theorems]]
name = "RealRooted.genPoly_univ_descentCount"
module = "RealRooted.CombinatorialExamples.EulerianStatistic"
label = "The descent polynomial of permutations of $n+1$ letters is $E_n^{(1)}$"

[[theorems]]
name = "RealRooted.isRealRooted_genPoly_univ_descentCount"
module = "RealRooted.CombinatorialExamples.EulerianStatistic"
label = "The descent polynomial of permutations of n+1 letters is real-rooted"
-->

<!-- realrooted-catalog-content -->
# Eulerian polynomials

The Eulerian polynomial $A_n(t)$ counts the permutations of $[n]$ by descents. Frobenius proved
that it has only real roots. The same holds for Brenti's type $B$ analogue and for a
one-parameter family containing both, and consecutive members of each family interlace.

## Results

For real $c$, the *generalized Eulerian polynomials* are $E^{(c)}_0=1$ and
$$
E^{(c)}_{n+1}=\bigl(1+(cn+1)t\bigr)E^{(c)}_n+c\,t(1-t)\bigl(E^{(c)}_n\bigr)'.
$$
Let $A_n(t)=\sum_{\sigma\in\mathfrak S_n}t^{\operatorname{des}\sigma}$. Then
$E^{(1)}_n=A_{n+1}$, and $E^{(2)}_n=B_n$ is the type $B$ Eulerian polynomial, the descent
polynomial of the signed permutations of $[n]$.

**Theorem (Frobenius).** [@Frobenius1910] The Eulerian polynomial $A_n$ is real-rooted, and
$A_n\ll A_{n+1}$. Equivalently, $P_n=tA_{n+1}$, given by $P_0=t$ and
$P_{n+1}=t\bigl((n+2)P_n+(1-t)P_n'\bigr)$, is real-rooted and $P_n\ll P_{n+1}$.

**Theorem (Brenti).** [@Brenti1994] The type $B$ Eulerian polynomial $B_n$ is real-rooted, and
$B_n\ll B_{n+1}$.

**Theorem (generalized Eulerian polynomials).** For $c>0$ and $n\ge0$, $E^{(c)}_n$ is nonzero
and real-rooted, and $E^{(c)}_n\ll E^{(c)}_{n+1}$.

## Use

The recurrence is the case $u=1+(cn+1)t$, $v=ct(1-t)$ of the
[Ma–Wang criterion](rr:ma-wang-liu-wang): $v\le0$ at the nonpositive roots of $E^{(c)}_n$.
Many descent polynomials are built from the same Euler steps; see the
[Euler operator page](rr:eulerian-operators) and the
[Eulerian-type polynomials](rr:eulerian-compendium).

## References

[@Frobenius1910]; [@Brenti1994]. See also [Eulerian polynomials](sf:eulerianPolynomial) and
[type B Eulerian polynomials](sf:typeBEulerianPolynomial) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
