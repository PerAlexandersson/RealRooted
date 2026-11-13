module

public import RealRooted.CombinatorialExamples.Eulerian
public import RealRooted.CombinatorialExamples.EulerianStatistic
public import RealRooted.CombinatorialExamples.TypeBEulerian
public import RealRooted.GeneralizedEulerian
public import RealRooted.GeneralizedEulerian.EvalNeg
public import RealRooted.GeneralizedEulerian.GeneratingFunction
public import RealRooted.MaWang.DerivativeStep

/-!
# Eulerian polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "eulerian"
formalized = "2026-07-10"
tags = []
references = [
  "Brenti1994",
]
authors = ["Frobenius", "Brenti"]
years = [1910, 1994]

[[definitions]]
name = "RealRooted.eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Shifted Eulerian polynomials P_n = t A_{n+1}"

[[definitions]]
name = "RealRooted.typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Type B Eulerian polynomials"

[[definitions]]
name = "RealRooted.generalizedEulerian"
module = "RealRooted.GeneralizedEulerian"
label = "Generalized Eulerian polynomials"

[[theorems]]
name = "RealRooted.isRealRooted_eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Eulerian polynomials are real-rooted"

[[theorems]]
name = "RealRooted.interlaces_eulerianTilde_succ"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Consecutive Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.isRealRooted_typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Type B Eulerian polynomials are real-rooted"

[[theorems]]
name = "RealRooted.interlaces_typeBEulerian_succ"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Consecutive type B Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.generalizedEulerian_splits"
module = "RealRooted.GeneralizedEulerian"
label = "For c > 0, E_n^{(c)} is real-rooted"

[[theorems]]
name = "RealRooted.interlaces_generalizedEulerian_succ"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "For c > 0, E_n^{(c)} interlaces E_{n+1}^{(c)}"
headline = true

[[theorems]]
name = "RealRooted.eulerianTilde_eq_X_mul_generalizedEulerian_one"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "The shifted Eulerian polynomial P_n equals t E_n^{(1)}"

[[theorems]]
name = "RealRooted.typeBEulerian_eq_generalizedEulerian_two"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "The type B Eulerian polynomial B_n equals E_n^{(2)}"

[[theorems]]
name = "RealRooted.GeneralizedEulerian.coeff_generalizedEulerian_one_eq_sum"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "Alternating-sum formula for the coefficients of E_n^{(1)}"

[[theorems]]
name = "RealRooted.genPoly_univ_descentCount"
module = "RealRooted.CombinatorialExamples.EulerianStatistic"
label = "The descent polynomial of permutations of n+1 letters is E_n^{(1)}"

[[theorems]]
name = "RealRooted.isRealRooted_genPoly_univ_descentCount"
module = "RealRooted.CombinatorialExamples.EulerianStatistic"
label = "The descent polynomial of permutations of n+1 letters is real-rooted"

[[theorems]]
name = "RealRooted.eval_neg_generalizedEulerian_one_pos"
module = "RealRooted.GeneralizedEulerian.EvalNeg"
label = "E_n^{(1)}(-q) > 0 whenever q > 0 and q 2^(n+1) ≤ 1"
-->

<!-- realrooted-catalog-content -->
# Eulerian polynomials

The Eulerian polynomials, the type $B$ Eulerian polynomials and a one-parameter family containing
both are real-rooted, and consecutive members interlace.

## Results

For real $c$, the *generalized Eulerian polynomials* are $E^{(c)}_0=1$ and
$$
E^{(c)}_{n+1}=\bigl(1+(cn+1)t\bigr)E^{(c)}_n+c\,t(1-t)\bigl(E^{(c)}_n\bigr)'.
$$

**Theorem (generalized Eulerian polynomials).** For $c>0$ and $n\ge0$, $E^{(c)}_n$ is nonzero
and real-rooted, and $E^{(c)}_n\ll E^{(c)}_{n+1}$.

**Eulerian polynomials ($c=1$).** Let $A_n(t)=\sum_{\sigma\in\mathfrak
S_n}t^{\operatorname{des}\sigma}$. Then $E^{(1)}_n=A_{n+1}$. Hence $A_{n+1}$ is real-rooted and
$A_{n+1}\ll A_{n+2}$. The shifted polynomials $P_n=tE^{(1)}_n$ satisfy $P_0=t$ and
$P_{n+1}=t\bigl((n+2)P_n+(1-t)P_n'\bigr)$, and are real-rooted with $P_n\ll P_{n+1}$. For $j\ge0$,
$$
[t^j]\,E^{(1)}_n=\sum_{i=0}^{j+1}(-1)^{j+1-i}\binom{n+2}{j+1-i}\,i^{\,n+1}.
$$

**Type $B$ Eulerian polynomials ($c=2$).** The polynomials $B_n=E^{(2)}_n$ are given by
$B_0=1$ and $B_{n+1}=\bigl(1+(2n+1)t\bigr)B_n+2t(1-t)B_n'$. They are real-rooted, and
$B_n\ll B_{n+1}$.

Since $E^{(1)}_n$ is a Pólya frequency polynomial with constant coefficient $1$ and linear
coefficient $2^{n+1}-n-2$, we have $E^{(1)}_n(-q)>0$ for $q>0$ with $q\,2^{n+1}\le1$.

## References

- F. G. Frobenius, “Über die Bernoullischen Zahlen und die Eulerschen Polynome,”
  *Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften* (1910), 809–847,
  for the Eulerian recurrence and its real-rootedness.
- [@Brenti1994], for type $B$.

See also [Eulerian polynomials](sf:eulerianPolynomial) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

Human statements:

* Eulerian polynomials:
  sf:eulerianPolynomial
* Eulerian Sturm sequence example:
  sf:ex:eulerianSturm
* Type `B` Eulerian polynomials:
  sf:typeBEulerianPolynomial

Classical origin: F. G. Frobenius, "Über die Bernoullischen Zahlen und die
Eulerschen Polynome", Sitzungsberichte der Königlich Preussischen Akademie der
Wissenschaften (1910), 809--847.

This module exposes the checked ordinary and type `B` Eulerian real-rootedness
and interlacing statements, together with the corresponding Sturm-prefix API.
-/
