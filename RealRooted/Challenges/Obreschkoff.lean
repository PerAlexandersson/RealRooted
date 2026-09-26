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

[[definitions]]
name = "RealRooted.HasPosLeadingCoeff"
module = "RealRooted.Basic.Coefficients"

[[theorems]]
name = "RealRooted.Challenges.Obreschkoff.allCombinationsRealRooted_of_interlaces"

[[theorems]]
name = "RealRooted.Challenges.Obreschkoff.interlaces_or_reverse_of_allCombinationsRealRooted"

[[theorems]]
name = """RealRooted.Challenges.Obreschkoff.\
interlaces_or_reverse_of_allCombinationsRealRooted_posLeading"""
-->

<!-- realrooted-catalog-content -->
# Obreschkoff’s theorem

Two interlacing polynomials generate a real-rooted pencil. Conversely, a
real-rooted pencil with the stated degree hypotheses forces one of the two
interlacing orientations.

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
theorem allCombinationsRealRooted_of_interlaces :
    ∀ {f g : ℝ[X]}, StrictInterl f g → AllComboRealRooted f g :=
  RealRooted.allComboRealRooted_of_strictInterl

/-- Converse Obreschkoff theorem in the degree-aware orientation used by
`StrictInterl`. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted :
    ∀ {f g : ℝ[X]},
      (f ≠ 0 ∧ f.Splits) →
      (g ≠ 0 ∧ g.Splits) →
      AllComboRealRooted f g →
      f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree →
      StrictInterl f g ∨ StrictInterl g f :=
  fun hf hg => RealRooted.strictInterl_of_allComboRealRooted hf.1 hf.2 hg.1 hg.2

/-- Converse direction for polynomials with positive leading coefficients. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted_posLeading {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf_splits : f.Splits)
    (hg_pos : HasPosLeadingCoeff g) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    StrictInterl f g ∨ StrictInterl g f :=
  interlaces_or_reverse_of_allCombinationsRealRooted
    ⟨hf_pos.ne_zero, hf_splits⟩ ⟨hg_pos.ne_zero, hg_splits⟩ hall hdeg

end Obreschkoff
end Challenges
end RealRooted
