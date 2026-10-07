import RealRooted.RootCounting.Descartes
import RealRooted.Mathlib.Algebra.Polynomial.BudanFourier

/-!
# Descartes' rule of signs challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "descartes-rule-of-signs"
authors = ["Descartes", "Budan", "Fourier"]
years = [1637, 1807, 1820]

[[definitions]]
name = "Polynomial.positiveRootCount"
module = "RealRooted.RootCounting.Descartes"
label = "Number of positive roots"

[[definitions]]
name = "Polynomial.negativeRootCount"
module = "RealRooted.RootCounting.Descartes"
label = "Number of negative roots"

[[theorems]]
name = "Polynomial.descartes_rule_of_signs"
module = "RealRooted.RootCounting.Descartes"
label = "Descartes' rule of signs"

[[theorems]]
name = "Polynomial.descartes_rule_of_signs_negative"
module = "RealRooted.RootCounting.Descartes"
label = "Descartes' rule of signs for negative roots"

[[theorems]]
name = "Polynomial.budan_fourier"
module = "RealRooted.Mathlib.Algebra.Polynomial.BudanFourier"
label = "Budan–Fourier theorem"
-->

<!-- realrooted-catalog-content -->
# Descartes' rule of signs

The number of positive real roots of a polynomial, counted with multiplicity,
is at most the number of sign changes in its nonzero coefficients. The
difference is even. Replacing $X$ by $-X$ gives the corresponding statement
for negative roots.

**Budan–Fourier theorem.** For a nonzero real polynomial $p$ of degree $n$ and
a real $x$, let $V(x)$ be the number of sign changes in
$p(x), p'(x), \dotsc, p^{(n)}(x)$, ignoring zeros. If $a < b$, the number of
roots of $p$ in $(a, b]$, counted with multiplicity, is at most
$V(a) - V(b)$, and the difference is even. Letting $a = 0$ and $b \to \infty$
recovers Descartes' rule.

## References

R. Descartes, *La Géométrie*, 1637. F. D. Budan, *Nouvelle méthode pour la
résolution des équations numériques*, 1807; J. Fourier, *Analyse des
équations déterminées*, 1831. See also the
[contextual account on symmetricfunctions.com][descartes-context].

[descartes-context]: https://www.symmetricfunctions.com/realRooted.htm#descartesRuleOfSigns
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.RootCounting.Descartes` and `RealRooted.Mathlib.Algebra.Polynomial.BudanFourier`.
-/
