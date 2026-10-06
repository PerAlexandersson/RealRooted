import RealRooted.PosCombo
import RealRooted.Wagner

/-!
# Nonpositive-root forms of Wagner's lemma

Reusable theorem-facing forms of Wagner's three interlacing transports under
the standard hypothesis of nonpositive real roots and positive leading
coefficient. Challenge and tactic frontends depend on this module rather than
on one another.
-/

open Polynomial

namespace RealRooted
namespace Wagner

/-- A polynomial splits over the reals, has only nonpositive roots, and has
positive leading coefficient. -/
def HasNonposRootsPosLeading (p : ℝ[X]) : Prop :=
  p.Splits ∧ (∀ r ∈ p.roots, r ≤ 0) ∧ HasPosLeadingCoeff p

/-- If `f` and `g` both interlace `h`, then `f + g` interlaces `h`. -/
theorem commonRight_add {f g h : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hfh : StrictInterl f h) (hgh : StrictInterl g h) :
    StrictInterl (f + g) h :=
  RealRooted.StrictInterl.add_of_right_of_posLeadingCoeff hfh hgh hf.2.2 hg.2.2

/-- If `h` interlaces both `f` and `g`, then `h` interlaces `f + g`. -/
theorem commonLeft_add {f g h : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hhf : StrictInterl h f) (hhg : StrictInterl h g) :
    StrictInterl h (f + g) :=
  hhf.add_of_left hhg hf.2.2 hg.2.2

/-- `f` interlaces `g` if and only if `g` interlaces `X * f`.  This covers both
`g.natDegree = f.natDegree + 1` and `g.natDegree = f.natDegree`. -/
theorem mulX_iff {f g : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g) :
    StrictInterl f g ↔ StrictInterl g (X * f) :=
  strictInterl_iff_mul_X_of_roots_nonpos hf.2.1 hg.2.1

end Wagner
end RealRooted
