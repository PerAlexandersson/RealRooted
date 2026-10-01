import RealRooted.RootCounting.Descartes

/-!
# Descartes' rule of signs challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "descartes-rule-of-signs"
authors = ["Descartes"]
years = [1637]

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
-->

<!-- realrooted-catalog-content -->
# Descartes' rule of signs

The number of positive real roots of a polynomial, counted with multiplicity,
is at most the number of sign changes in its nonzero coefficients. The
difference is even. Replacing `X` by `-X` gives the corresponding statement
for negative roots.

## References

R. Descartes, *La Géométrie*, 1637. See also the
[contextual account on symmetricfunctions.com][descartes-context].

[descartes-context]: https://www.symmetricfunctions.com/realRooted.htm#descartesRuleOfSigns
<!-- /realrooted-catalog-content -->

This module exposes the reusable theorem implementation in
`RealRooted.RootCounting.Descartes`.
-/

namespace RealRooted
namespace Challenges
namespace Descartes

export Polynomial
  (positiveRootCount
    negativeRootCount
    descartes_rule_of_signs
    descartes_rule_of_signs_negative)

end Descartes
end Challenges
end RealRooted
