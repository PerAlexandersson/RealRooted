module

import RealRooted.RootCounting.Descartes
import RealRooted.Mathlib.Algebra.Polynomial.BudanFourier

/-!
# Descartes' rule of signs

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "descartes-rule-of-signs"
formalized = "2026-09-27"
references = []
tags = []
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
headline = true
symcat = "descartesRuleOfSigns"

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

The number of positive roots of a real polynomial, counted with multiplicity, is at most the
number of sign changes in its coefficients, and the difference is even.

## Results

**Theorem (Descartes' rule of signs).** For a real polynomial $p$, let $V(p)$ be the number of
sign changes in the sequence of its coefficients, ignoring zeros. Then the number of positive
roots of $p$ is at most $V(p)$, and $V(p)$ minus this number is even. Applying this to $p(-x)$
gives the same statement for negative roots.

**Theorem (Budan–Fourier).** Let $p\ne0$ be a real polynomial of degree $n$ and let $V(x)$ be
the number of sign changes in $p(x),p'(x),\dotsc,p^{(n)}(x)$, ignoring zeros. For $a<b$, the
number of roots of $p$ in $(a,b]$, counted with multiplicity, is at most $V(a)-V(b)$, and
$V(a)-V(b)$ minus this number is even.

## Use

Taking $a=0$ and $b$ large recovers Descartes' rule.

## References

R. Descartes, *La Géométrie*, 1637. F. D. Budan, *Nouvelle méthode pour la
résolution des équations numériques*, 1807; J. Fourier, *Analyse des
équations déterminées*, 1831. See also the
[contextual account on symmetricfunctions.com][descartes-context].

[descartes-context]: sf:descartesRuleOfSigns
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.RootCounting.Descartes` and `RealRooted.Mathlib.Algebra.Polynomial.BudanFourier`.
-/
