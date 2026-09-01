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
abbrev HasNonposRootsPosLeading (p : ℝ[X]) : Prop :=
  p.Splits ∧ (∀ r ∈ p.roots, r ≤ 0) ∧ HasPosLeadingCoeff p

/-- If `f` and `g` both interlace `h`, then `f + g` interlaces `h`. -/
theorem commonRight_add {f g h : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hfh : Prec f h) (hgh : Prec g h) :
    Prec (f + g) h :=
  RealRooted.prec_add_of_prec_right_of_posLeadingCoeff hfh hgh hf.2.2 hg.2.2

/-- If `h` interlaces both `f` and `g`, then `h` interlaces `f + g`. -/
theorem commonLeft_add {f g h : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hhf : Prec h f) (hhg : Prec h g) :
    Prec h (f + g) := by
  have hprec : Prec h ([f, g].sum) := by
    grind [RealRooted.prec_sum_left_of_common_left_signed]
  grind

/-- The checked two-summand common-left form with explicit algebraic
hypotheses. -/
theorem commonLeft_add_checked :
    ∀ {f g h : ℝ[X]},
      (hhf : Prec h f) → (hhg : Prec h g) →
      (hf_pos : HasPosLeadingCoeff f) → (hg_pos : HasPosLeadingCoeff g) →
      (hfg_ne : (f + g) ≠ 0) → (hfg_splits : (f + g).Splits) →
      (hcop : IsCoprime f g) →
      Prec h (f + g) :=
  RealRooted.prec_add_of_prec_left

/-- `f` interlaces `g` if and only if `g` interlaces `X * f`, provided their
degrees differ by one. -/
theorem mulX_iff {f g : ℝ[X]}
    (hf : HasNonposRootsPosLeading f)
    (hg : HasNonposRootsPosLeading g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) :=
  RealRooted.prec_iff_prec_mul_X_of_roots_nonpos
    hf.1 hg.1 hf.2.2 hg.2.2 hf.2.1 hg.2.1 hdeg

end Wagner
end RealRooted
