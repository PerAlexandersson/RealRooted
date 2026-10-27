import RealRooted.Tactic.Wagner

open Polynomial

namespace RealRooted
namespace Tactic

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
  rr_strict_interl_cancel_common_linear_factor using
    root := r,
    multiplied_interlacing := h

example {f g : ℝ[X]} (r : ℝ)
    (h : StrictInterl ((X - C r) * f) ((X - C r) * g)) : StrictInterl f g := by
  rr_strict_interl_cancel_common_linear_factor using root := r

example {d f g : ℝ[X]} (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (h : StrictInterl f g) : StrictInterl (d * f) (d * g) := by
  rr_strict_interl_mul_common_factor using
    factor_nonzero := hd_ne,
    factor_splits := hd_splits,
    base_interlacing := h

example {d f g : ℝ[X]} (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (h : StrictInterl f g) : StrictInterl (d * f) (d * g) := by
  rr_strict_interl_mul_common_factor

end Tactic
end RealRooted
