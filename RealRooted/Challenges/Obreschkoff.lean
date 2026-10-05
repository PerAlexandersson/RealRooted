import RealRooted.ObreschkoffConverse

/-!
# Obreschkoff challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "obreschkoff"
authors = ["Obreschkoff", "Dedieu"]
years = [1963, 1992]

[[definitions]]
name = "RealRooted.AllComboRealRooted"
module = "RealRooted.AllCombo"
label = "Every real combination is real-rooted"

[[theorems]]
name = "RealRooted.Challenges.Obreschkoff.allCombinationsRealRooted_of_interlaces"
label = "Interlacing gives a real-rooted pencil"

[[theorems]]
name = "RealRooted.Challenges.Obreschkoff.interlaces_or_reverse_of_allCombinationsRealRooted"
label = "A real-rooted pencil gives interlacing"
-->

<!-- realrooted-catalog-content -->
# Obreschkoff’s theorem

Two interlacing polynomials generate a real-rooted pencil: every real linear
combination $\alpha f + \beta g$ splits over $\mathbb R$. Conversely, let $f$
and $g$ be nonzero real-rooted polynomials with $\deg g = \deg f + 1$ or
$\deg g = \deg f$. If every real linear combination of $f$ and $g$ splits,
then $f$ and $g$ interlace in one of the two orientations.

## References

N. Obreschkoff, *Verteilung und Berechnung der Nullstellen reeller
Polynome*, VEB Deutscher Verlag der Wissenschaften, 1963; J.-P. Dedieu,
“Obreschkoff’s theorem revisited,” *Journal of Pure and Applied Algebra* 81
(1992), 269–278.  See the
[contextual statement on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#obreschkoffDedieu).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#obreschkoffDedieu

Original references include N. Obreschkoff, *Verteilung und Berechnung der
Nullstellen reeller Polynome* (1963), and J.-P. Dedieu, "Obreschkoff's theorem
revisited: what convex sets are contained in the set of hyperbolic polynomials?",
J. Pure Appl. Algebra 81 (1992), 269--278.

This module exposes the checked forward and converse Obreschkoff directions.
The continuity and common-root analysis remains in
`RealRooted.ObreschkoffConverse`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Obreschkoff

/-- If `f` interlaces `g`, then every real linear combination is real-rooted
or zero. -/
theorem allCombinationsRealRooted_of_interlaces {f g : ℝ[X]} (hfg : StrictInterl f g) :
    AllComboRealRooted f g :=
  RealRooted.allComboRealRooted_of_strictInterl hfg

/-- Converse Obreschkoff theorem in the degree-aware orientation used by
`StrictInterl`. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted {f g : ℝ[X]}
    (hf : f ≠ 0) (hf_splits : f.Splits) (hg : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    StrictInterl f g ∨ StrictInterl g f :=
  RealRooted.strictInterl_of_allComboRealRooted hf hf_splits hg hg_splits hall hdeg

end Obreschkoff
end Challenges
end RealRooted
