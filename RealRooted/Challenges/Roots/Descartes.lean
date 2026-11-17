module

import RealRooted.CubicDiscriminant
import RealRooted.Mathlib.Algebra.Polynomial.BudanFourier
import RealRooted.RootCounting.Descartes
import RealRooted.RootCounting.Sturm
import RealRooted.RootVieta.Newton

/-!
# Counting real roots: Descartes, Budan–Fourier and Sturm

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "counting-real-roots"
formalized = "2026-09-27"
references = [
  "Sylvester1853",
]
authors = ["Descartes", "Budan", "Fourier", "Sturm", "Hermite", "Sylvester"]
years = [1637, 1807, 1820, 1829, 1853]

[[definitions]]
name = "Polynomial.positiveRootCount"
module = "RealRooted.RootCounting.Descartes"
label = "Number of positive roots, with multiplicity"

[[definitions]]
name = "Polynomial.signedRemainderSequence"
module = "RealRooted.Mathlib.Algebra.Polynomial.Sturm"
label = "Signed remainder sequence"

[[definitions]]
name = "Polynomial.hermiteMatrix"
module = "RealRooted.RootVieta.Newton"
label = "Hermite matrix of power sums of the roots"

[[theorems]]
name = "Polynomial.descartes_rule_of_signs"
module = "RealRooted.RootCounting.Descartes"
label = "Descartes: positive roots are at most the coefficient sign changes, with even difference"
symcat = "descartesRuleOfSigns"

[[theorems]]
name = "Polynomial.descartes_rule_of_signs_negative"
module = "RealRooted.RootCounting.Descartes"
label = "Descartes' rule of signs for negative roots"

[[theorems]]
name = "Polynomial.budan_fourier"
module = "RealRooted.Mathlib.Algebra.Polynomial.BudanFourier"
label = "Budan–Fourier: sign changes of derivatives bound the roots in (a, b]"

[[theorems]]
name = "RealRooted.distinctRootCountIoo_eq_distinctSturmVariations_sub"
module = "RealRooted.RootCounting.Sturm"
label = "Sturm: sign changes of the Sturm sequence count the distinct roots in (a, b)"
headline = true
symcat = "sturmRootCounting"

[[theorems]]
name = "RealRooted.splits_iff_distinctSturmVariations_sub_eq_natDegree"
module = "RealRooted.RootCounting.Sturm"
label = "A Sturm test for real-rootedness"

[[theorems]]
name = "Polynomial.splits_iff_hermiteMatrix_posSemidef"
module = "RealRooted.RootVieta.Newton"
label = "Hermite–Sylvester: a monic p is real-rooted iff its Hermite matrix is PSD"
symcat = "hermiteSylvesterTheorem"

[[theorems]]
name = "RealRooted.cubicDiscr_nonneg_iff_splits_of_natDegree_le_three"
module = "RealRooted.CubicDiscriminant"
label = "A real polynomial of degree at most three is real-rooted iff its discriminant is ≥ 0"
-->

<!-- realrooted-catalog-content -->
# Counting real roots: Descartes, Budan–Fourier and Sturm

Sign changes bound or count the real roots of a polynomial. Descartes' rule bounds the positive
roots by the sign changes of the coefficients, Budan–Fourier bounds the roots in an interval by
those of the derivatives, and Sturm's theorem counts the distinct roots exactly. Sturm's theorem
and the Hermite–Sylvester criterion give finite tests for real-rootedness.

## Results

For a list of reals let $V$ be its number of sign changes, zeros omitted.

**Theorem (Descartes' rule of signs).** Let $p$ be a real polynomial with coefficient sequence
$c$. The number of positive roots of $p$, counted with multiplicity, is at most $V(c)$, and the
difference is even. Applied to $p(-x)$, the same holds for the negative roots.

**Theorem (Budan–Fourier).** Let $p\ne0$ have degree $n$, put
$V(x)=V\bigl(p(x),p'(x),\dotsc,p^{(n)}(x)\bigr)$ and let $a<b$. The number of roots of $p$ in
$(a,b]$, counted with multiplicity, is at most $V(a)-V(b)$, and the difference is even.

The *Sturm sequence* of $p$ is the signed Euclidean remainder sequence of $p$ and $p'$. Let
$V_p(x)$ be the number of sign changes of the Sturm sequence of the squarefree part of $p$ at
$x$.

**Theorem (Sturm).** Let $p\ne0$ and $a<b$ with $p(b)\ne0$. The number of distinct real roots
of $p$ in $(a,b)$ is $V_p(a)-V_p(b)$. Consequently, if every real root of $p$ lies in $(a,b)$,
then $p$ is real-rooted if and only if $V_p(a)-V_p(b)$ is the degree of the squarefree part of
$p$.

**Theorem (Hermite–Sylvester).** [@Sylvester1853] Let $p$ be a monic real polynomial of degree
$n$ with power sums $s_k=\sum_zz^k$ over its complex roots, with multiplicity. Then $p$ is
real-rooted if and only if the Hankel matrix $(s_{i+j})_{0\le i,j<n}$ is positive
semidefinite.

**Proposition (degree at most three).** A real polynomial of degree at most three is real-rooted
if and only if its discriminant is nonnegative.

## Use

Sturm's theorem and the Hermite–Sylvester criterion decide whether one explicit polynomial is
real-rooted, such as a base case or a counterexample; infinite families need
[interlacing](rr:interlacing).

## References

R. Descartes, *La Géométrie* (1637); F. D. Budan, *Nouvelle méthode pour la résolution des
équations numériques* (1807); J. Fourier, *Analyse des équations déterminées* (1831);
J. C. F. Sturm, “Mémoire sur la résolution des équations numériques,” *Bulletin des Sciences de
Férussac* 11 (1829), 419–422; C. Hermite, “Remarques sur le théorème de M. Sturm,” *C. R.
Acad. Sci. Paris* 36 (1853), 52–54; [@Sylvester1853]. See also
[Descartes' rule of signs](sf:descartesRuleOfSigns),
[Sturm root counting](sf:sturmRootCounting) and the
[Hermite–Sylvester theorem](sf:hermiteSylvesterTheorem) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
