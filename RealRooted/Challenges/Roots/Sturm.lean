module

import RealRooted.CubicDiscriminant
import RealRooted.RootCounting.Sturm
import RealRooted.RootVieta.Newton

/-!
# Sturm root-counting challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "sturm-root-counting"
formalized = "2026-09-27"
tags = []
references = [
  "Sylvester1853",
]
authors = ["Sturm", "Hermite", "Sylvester"]
years = [1829, 1853]

[[definitions]]
name = "Polynomial.signedRemainderSequence"
module = "RealRooted.Mathlib.Algebra.Polynomial.Sturm"
label = "Signed remainder sequence"

[[definitions]]
name = "RealRooted.sturmVariations"
module = "RealRooted.RootCounting.Sturm"
label = "Sign variations of the Sturm sequence"

[[definitions]]
name = "RealRooted.sturmSquarefreePart"
module = "RealRooted.RootCounting.Sturm"
label = "Squarefree part"

[[definitions]]
name = "RealRooted.distinctSturmVariations"
module = "RealRooted.RootCounting.Sturm"
label = "Sign variations of the squarefree Sturm sequence"

[[definitions]]
name = "RealRooted.distinctRootCountIoo"
module = "RealRooted.RootCounting.Sturm"
label = "Number of distinct roots in an interval"

[[definitions]]
name = "Polynomial.hermiteMatrix"
module = "RealRooted.RootVieta.Newton"
label = "Hermite matrix of Newton power sums"

[[theorems]]
name = "RealRooted.distinctRootCountIoo_eq_distinctSturmVariations_sub"
module = "RealRooted.RootCounting.Sturm"
label = "Sturm's theorem"

[[theorems]]
name = "RealRooted.splits_iff_distinctSturmVariations_sub_eq_natDegree"
module = "RealRooted.RootCounting.Sturm"
label = "A Sturm test for real-rootedness"

[[theorems]]
name = "Polynomial.splits_iff_hermiteMatrix_posSemidef"
module = "RealRooted.RootVieta.Newton"
label = "Hermite–Sylvester: real-rooted iff the Hermite matrix is PSD"
headline = true
symcat = "hermiteSylvesterTheorem"

[[theorems]]
name = "RealRooted.cubicDiscr_nonneg_iff_splits_of_natDegree_le_three"
module = "RealRooted.CubicDiscriminant"
label = "A real polynomial of degree at most three splits iff its discriminant is nonnegative"
-->

<!-- realrooted-catalog-content -->
# Sturm root counting

Sign changes of the signed Euclidean remainder sequence count the distinct real roots of a
polynomial in an interval, and a Hermite matrix test decides real-rootedness.

## Results

For a real polynomial $p$, the *Sturm sequence* is the signed Euclidean remainder sequence of $p$
and $p'$; its *sign variation* at $x$ is the number of sign changes of its values at $x$, zero
values omitted. For arbitrary $p$ we apply it to its radical (the
squarefree part, with the repeated factors removed), and write $V_p(x)$ for the resulting variation.

**Theorem (Sturm).** Let $p\ne0$ and $a<b$ with $p(b)\ne0$. Then the number of distinct real
roots of $p$ in the open interval $(a,b)$ is $V_p(a)-V_p(b)$.

**Theorem (real-rootedness by sign changes).** Let $p\ne0$ and $a<b$, and suppose every real
root of $p$ lies in $(a,b)$. Then $p$ is real-rooted if and only if $V_p(a)-V_p(b)$ equals the
degree of the squarefree part of $p$.

**Hermite–Sylvester criterion** [@Sylvester1853]. Let $f$ be a monic real polynomial of degree
$n$ and $s_k=\sum_zz^k$ the power sums of its complex roots, counted with multiplicity. Put
$H_f=(s_{i+j})_{0\le i,j\le n-1}$. Then $f$ is real-rooted if and only if $H_f$ is positive
semidefinite.

**Proposition (degree at most three).** A real polynomial of degree at most three is real-rooted
if and only if its cubic discriminant is nonnegative.

## References

J. C. F. Sturm, “Mémoire sur la résolution des équations numériques,” *Bulletin
des Sciences de Férussac* 11 (1829), 419–422; C. Hermite, “Remarques sur le
théorème de M. Sturm,” *Comptes rendus de l’Académie des sciences* 36 (1853),
52–54. See [@Sylvester1853], the root-counting overview on
[symmetricfunctions.com][sturm-overview], and the
[Hermite–Sylvester theorem][hermite-sylvester] there.

[sturm-overview]: sf:sturmRootCounting
[hermite-sylvester]: sf:hermiteSylvesterTheorem
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.RootCounting.Sturm` and `RealRooted.RootVieta.Newton`.
-/
