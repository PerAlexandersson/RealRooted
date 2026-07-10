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

/-- If `f` interlaces `g`, then every real linear combination is real-rooted
or zero. -/
theorem allCombinationsRealRooted_of_interlaces {f g : ℝ[X]}
    (hfg : Prec f g) :
    AllComboRealRooted f g :=
  RealRooted.allComboRealRooted_of_prec hfg

/-- Converse Obreschkoff theorem in the degree-aware orientation used by
`Prec`. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f :=
  RealRooted.prec_of_allComboRealRooted hf_ne hf_splits hg_ne hg_splits hall hdeg

/-- Positive-leading-coefficient wrapper for the converse direction. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted_posLeading {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf_splits : f.Splits)
    (hg_pos : HasPosLeadingCoeff g) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f :=
  RealRooted.prec_of_allComboRealRooted
    hf_pos.ne_zero hf_splits hg_pos.ne_zero hg_splits hall hdeg

end Obreschkoff
end Challenges
end RealRooted
