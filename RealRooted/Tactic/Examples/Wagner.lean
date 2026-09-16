import RealRooted.Tactic.Wagner

open Polynomial

namespace RealRooted
namespace Tactic

example {f g h : ℝ[X]}
    (hf : RealRooted.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Wagner.HasNonposRootsPosLeading g)
    (_hh : RealRooted.Wagner.HasNonposRootsPosLeading h)
    (hfh : StrictInterl f h) (hgh : StrictInterl g h) :
    StrictInterl (f + g) h := by
  rr_wagner_common_right_add using
    left := hf,
    right := hg,
    common := _hh,
    left_interlaces_common := hfh,
    right_interlaces_common := hgh

example {f g h : ℝ[X]}
    (hf : RealRooted.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Wagner.HasNonposRootsPosLeading g)
    (_hh : RealRooted.Wagner.HasNonposRootsPosLeading h)
    (hhf : StrictInterl h f) (hhg : StrictInterl h g) :
    StrictInterl h (f + g) := by
  rr_wagner_common_left_add using
    left := hf,
    right := hg,
    common := _hh,
    common_interlaces_left := hhf,
    common_interlaces_right := hhg

example {f g : ℝ[X]}
    (hf : RealRooted.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Wagner.HasNonposRootsPosLeading g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g (X * f) := by
  rr_wagner_mulX_iff using
    shorter := hf,
    longer := hg,
    degree := hdeg

example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (H n))
    (hFH : ∀ n : Nat, StrictInterl (F n) (H n))
    (hGH : ∀ n : Nat, StrictInterl (G n) (H n)) :
    ∀ n : Nat, StrictInterl (F n + G n) (H n) := by
  rr_wagner_common_right_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    left_interlaces_common := hFH,
    right_interlaces_common := hGH

example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, StrictInterl (H n) (F n))
    (hHG : ∀ n : Nat, StrictInterl (H n) (G n)) :
    ∀ n : Nat, StrictInterl (H n) (F n + G n) := by
  rr_wagner_common_left_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    common_interlaces_left := hHF,
    common_interlaces_right := hHG

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hdeg : ∀ n : Nat, (F n).natDegree + 1 = (G n).natDegree) :
    ∀ n : Nat, StrictInterl (F n) (G n) ↔ StrictInterl (G n) (X * F n) := by
  rr_wagner_mulX_iff_sequence using
    shorter := hF,
    longer := hG,
    degree := hdeg

example {f g h : ℝ[X]} (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    StrictInterl (f + g) h := by
  rr_wagner_common_right_add_pos_lc using
    left_interlaces_common := hfh,
    right_interlaces_common := hgh,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g h : ℝ[X]} (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    StrictInterl (f + g) h := by
  rr_wagner_common_right_add_pos_lc

example {f g : ℝ[X]} (r : ℝ)
    (h : StrictInterl ((X - C r) * f) ((X - C r) * g)) : StrictInterl f g := by
  rr_prec_cancel_common_linear_factor using
    root := r,
    multiplied_interlacing := h

example {f g : ℝ[X]} (r : ℝ)
    (h : StrictInterl ((X - C r) * f) ((X - C r) * g)) : StrictInterl f g := by
  rr_prec_cancel_common_linear_factor using root := r

example {d f g : ℝ[X]} (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (h : StrictInterl f g) : StrictInterl (d * f) (d * g) := by
  rr_prec_mul_common_factor using
    factor_nonzero := hd_ne,
    factor_splits := hd_splits,
    base_interlacing := h

example {d f g : ℝ[X]} (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (h : StrictInterl f g) : StrictInterl (d * f) (d * g) := by
  rr_prec_mul_common_factor

end Tactic
end RealRooted
