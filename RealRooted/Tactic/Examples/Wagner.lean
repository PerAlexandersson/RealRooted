import RealRooted.Tactic.Wagner

open Polynomial

namespace RealRooted
namespace Tactic

example {f g h : ℝ[X]}
    (hf : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading g)
    (hh : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading h)
    (hfh : Prec f h) (hgh : Prec g h) :
    Prec (f + g) h := by
  rr_wagner_common_right_add using
    left := hf,
    right := hg,
    common := hh,
    left_interlaces_common := hfh,
    right_interlaces_common := hgh

example {f g h : ℝ[X]}
    (hf : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading g)
    (hh : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading h)
    (hhf : Prec h f) (hhg : Prec h g) :
    Prec h (f + g) := by
  rr_wagner_common_left_add using
    left := hf,
    right := hg,
    common := hh,
    common_interlaces_left := hhf,
    common_interlaces_right := hhg

example {f g : ℝ[X]}
    (hf : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Challenges.Wagner.HasNonposRootsPosLeading g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) := by
  rr_wagner_mulX_iff using
    shorter := hf,
    longer := hg,
    degree := hdeg

end Tactic
end RealRooted
