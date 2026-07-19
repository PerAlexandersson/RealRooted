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

example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (H n))
    (hFH : ∀ n : Nat, Prec (F n) (H n))
    (hGH : ∀ n : Nat, Prec (G n) (H n)) :
    ∀ n : Nat, Prec (F n + G n) (H n) := by
  rr_wagner_common_right_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    left_interlaces_common := hFH,
    right_interlaces_common := hGH

example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n)) :
    ∀ n : Nat, Prec (H n) (F n + G n) := by
  rr_wagner_common_left_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    common_interlaces_left := hHF,
    common_interlaces_right := hHG

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hdeg : ∀ n : Nat, (F n).natDegree + 1 = (G n).natDegree) :
    ∀ n : Nat, Prec (F n) (G n) ↔ Prec (G n) (X * F n) := by
  rr_wagner_mulX_iff_sequence using
    shorter := hF,
    longer := hG,
    degree := hdeg

end Tactic
end RealRooted
