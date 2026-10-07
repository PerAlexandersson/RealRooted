import RealRooted.HermiteBiehler.StablePencil
import RealRooted.ObreschkoffConverse.DegreeGap
import RealRooted.OperatorPreservesInterlacing

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

[[theorems]]
name = "RealRooted.Challenges.Obreschkoff.allCombinationsRealRooted_iff_interlaces_or_reverse"
label = "Obreschkoff’s theorem as an equivalence"

[[theorems]]
name = "RealRooted.natDegree_close_of_allComboRealRooted"
module = "RealRooted.ObreschkoffConverse.DegreeGap"
label = "A real-rooted pencil of nonzero polynomials has degrees differing by at most one"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_bivariatePencil_iff_strictInterl"
module = "RealRooted.HermiteBiehler.StablePencil"
label = "Interlacing as stability of the bivariate pencil f(z) + w g(z)"
-->

<!-- realrooted-catalog-content -->
# Obreschkoff’s theorem

Two interlacing polynomials generate a real-rooted pencil: every real linear
combination $\alpha f + \beta g$ splits over $\mathbb R$. Conversely, if
every real linear combination of $f$ and $g$ splits, then $f$ and $g$
interlace in one of the two orientations, where either polynomial may be zero.
No degree hypothesis is needed: if every real linear combination of nonzero
polynomials $f$ and $g$ splits, then $|\deg f - \deg g| \le 1$.

Hence, for real polynomials $f$ and $g$ that are zero or real-rooted, every
real linear combination of $f$ and $g$ splits if and only if $f$ and $g$
interlace in one of the two orientations.

The pencil also has a stable form. Let $f \ne 0$ and $g \ne 0$ have
nonnegative coefficients, with $f$ nonconstant. Then the bivariate polynomial
$f(z) + w\,g(z)$ has no zero with $z$ and $w$ both in the open upper half-plane
if and only if $g$ and $f$ strictly interlace. One direction specializes at
$w = i$ and uses the Hermite–Biehler theorem.

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

This module exposes the checked forward and converse Obreschkoff directions
and their combination as an equivalence. The continuity and common-root
analysis remains in `RealRooted.ObreschkoffConverse`.
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

/-- Converse Obreschkoff theorem: if every real linear combination of `f` and
`g` is real-rooted, then `f` and `g` interlace in one of the two orientations,
where either polynomial may be zero. -/
theorem interlaces_or_reverse_of_allCombinationsRealRooted {f g : ℝ[X]}
    (hall : AllComboRealRooted f g) :
    Interl f g ∨ Interl g f :=
  RealRooted.interl_or_reverse_of_allComboRealRooted hall

private theorem allComboRealRooted_of_interl {f g : ℝ[X]} (hf : f.Splits)
    (hg : g.Splits) (hfg : Interl f g) : AllComboRealRooted f g := by
  rcases hfg with rfl | rfl | hfg
  · intro α β
    simpa using hg.C_mul β
  · intro α β
    simpa using hf.C_mul α
  · exact RealRooted.allComboRealRooted_of_strictInterl hfg

/-- Obreschkoff's theorem: two polynomials, each zero or real-rooted, generate
a real-rooted pencil if and only if they interlace in one of the two
orientations. -/
theorem allCombinationsRealRooted_iff_interlaces_or_reverse {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) :
    AllComboRealRooted f g ↔ Interl f g ∨ Interl g f := by
  refine ⟨interlaces_or_reverse_of_allCombinationsRealRooted, ?_⟩
  rintro (hfg | hgf)
  · exact allComboRealRooted_of_interl hf hg hfg
  · exact allComboRealRooted_comm (allComboRealRooted_of_interl hg hf hgf)

end Obreschkoff
end Challenges
end RealRooted
