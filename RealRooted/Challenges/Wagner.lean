import RealRooted.Wagner.NonpositiveRoots

/-!
# Wagner challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#wagnerLemma

Original publication: D. G. Wagner, "Total positivity of Hadamard products",
J. Math. Anal. Appl. 163 (1992), 459--483.

This module exposes checked challenge-facing forms of Wagner's lemma.  The
root-list analysis and common-sum infrastructure remain in `RealRooted.Wagner*`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Wagner

/-- Human-style hypothesis from Wagner's lemma: real roots are nonpositive and
the leading coefficient is positive. -/
abbrev HasNonposRootsPosLeading (p : ℝ[X]) : Prop :=
  RealRooted.Wagner.HasNonposRootsPosLeading p

/-- Wagner (1): if `f` and `g` both interlace `h`, then `f + g` interlaces
`h`. -/
theorem commonRight_add {f g h : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hfh : StrictInterl f h) (hgh : StrictInterl g h) :
    StrictInterl (f + g) h :=
  RealRooted.Wagner.commonRight_add hf hg hfh hgh

/-- Wagner (2): if `h` interlaces both `f` and `g`, then `h` interlaces
`f + g`.

This is the human statement from the catalog.  The current checked theorem in
`RealRooted.WagnerLeftSum` proves a stronger-shaped internal step with explicit
coprime and splitting hypotheses; this challenge-facing theorem records the
clean target. -/
theorem commonLeft_add {f g h : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hhf : StrictInterl h f) (hhg : StrictInterl h g) :
    StrictInterl h (f + g) :=
  RealRooted.Wagner.commonLeft_add hf hg hhf hhg

/-- Checked two-summand common-left form currently available in the core
Wagner module. -/
theorem commonLeft_add_checked :
    ∀ {f g h : ℝ[X]},
      (hhf : StrictInterl h f) → (hhg : StrictInterl h g) →
      (hf_pos : HasPosLeadingCoeff f) → (hg_pos : HasPosLeadingCoeff g) →
      (hfg_ne : (f + g) ≠ 0) → (hfg_splits : (f + g).Splits) →
      (hcop : IsCoprime f g) →
      StrictInterl h (f + g) :=
  RealRooted.Wagner.commonLeft_add_checked

/-- Wagner (3): `f` interlaces `g` if and only if `g` interlaces `X * f`.

This is the Lean orientation of the catalog statement
`g \interl f` iff `f \interl t g`: here `f` is the shorter polynomial and
`g` is the longer one. -/
theorem mulX_iff {f g : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g (X * f) :=
  RealRooted.Wagner.mulX_iff hf hg hdeg

end Wagner
end Challenges
end RealRooted
