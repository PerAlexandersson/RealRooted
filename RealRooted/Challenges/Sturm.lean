import RealRooted.RootCounting.Sturm
import RealRooted.RootVieta.Newton

/-!
# Sturm root-counting challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "sturm-root-counting"
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
-->

<!-- realrooted-catalog-content -->
# Sturm root counting

Evaluate the signed Euclidean remainder sequence of a polynomial and its
derivative at the two endpoints of an interval, omit zero values, and count
sign changes. The drop in sign changes is exactly the number of distinct real
roots in the open interval.

Repeated factors are removed by a canonical squarefree normalization. If the
interval contains every root, the same count tests whether all roots are real.

**Hermite–Sylvester criterion.** Let $f$ be a monic real polynomial of degree
$n$, and let $s_k = \sum_z z^k$ be the Newton power sums of its complex roots,
counted with multiplicity. The Hermite matrix is
$H_f = (s_{i+j})_{0 \le i, j \le n-1}$. Then $f$ is real-rooted if and only if
$H_f$ is positive semidefinite.

## References

J. C. F. Sturm, “Mémoire sur la résolution des équations numériques,”
*Bulletin des Sciences de Férussac* 11 (1829), 419–422;
C. Hermite, “Remarques sur le théorème de M. Sturm,” *Comptes rendus de
l’Académie des sciences* 36 (1853), 52–54;
J. J. Sylvester, “On a theory of the syzygetic relations of two rational
integral functions,” *Philosophical Transactions of the Royal Society of
London* 143 (1853), 407–548. See also the root-counting
overview on [symmetricfunctions.com][sturm-overview] and the
[Hermite–Sylvester theorem][hermite-sylvester] there.

[sturm-overview]: https://www.symmetricfunctions.com/realRootedInterlacing.htm#sturmRootCounting
[hermite-sylvester]: https://www.symmetricfunctions.com/realRooted.htm#hermiteSylvesterTheorem
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.RootCounting.Sturm` and `RealRooted.RootVieta.Newton`.
-/
