import RealRooted.ObreschkoffConverse

/-!
# Obreschkoff challenge entry point

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

/-- Challenge-facing name for a real pencil whose every member is real-rooted
or zero. -/
abbrev RealPencilRealRooted (f g : ℝ[X]) : Prop :=
  AllComboRealRooted f g

/-- Challenge-facing name for proper position/interlacing in the current
orientation. -/
abbrev ProperPosition (f g : ℝ[X]) : Prop :=
  Prec f g

/-- Challenge-facing name for a nonzero real-split polynomial. -/
abbrev NonzeroSplitPolynomial (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits

/-- If `f` interlaces `g`, then every real linear combination is real-rooted
or zero. -/
theorem allCombinationsRealRooted_of_interlaces :
    ∀ {f g : ℝ[X]}, ProperPosition f g → RealPencilRealRooted f g :=
  RealRooted.allComboRealRooted_of_prec

/-- Converse Obreschkoff theorem in the degree-aware orientation used by
`Prec`. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted :
    ∀ {f g : ℝ[X]},
      NonzeroSplitPolynomial f →
      NonzeroSplitPolynomial g →
      RealPencilRealRooted f g →
      f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree →
      ProperPosition f g ∨ ProperPosition g f :=
  fun hf hg => RealRooted.prec_of_allComboRealRooted hf.1 hf.2 hg.1 hg.2

/-- Positive-leading-coefficient wrapper for the converse direction. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted_posLeading {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf_splits : f.Splits)
    (hg_pos : HasPosLeadingCoeff g) (hg_splits : g.Splits)
    (hall : RealPencilRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    ProperPosition f g ∨ ProperPosition g f :=
  interlaces_or_reverse_of_allCombinationsRealRooted
    ⟨hf_pos.ne_zero, hf_splits⟩ ⟨hg_pos.ne_zero, hg_splits⟩ hall hdeg

end Obreschkoff
end Challenges
end RealRooted
