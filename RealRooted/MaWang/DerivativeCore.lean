module

public import RealRooted.MaWang.Weak
import RealRooted.MaWang.Strong
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

public section

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Derivative specialization of the Liu--Wang mixed theorem in the degree `+1`
case. The hypothesis is the strict root-sign condition naturally obtained from
`F(r) = v(r) f'(r)`. -/
theorem strictInterl_of_step_succ {f u v : ℝ[X]} (hf : f.Splits)
    (hdegf : 1 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    StrictInterl f (u * f + v * f.derivative) := by
  refine strictInterl_of_interlaces_eval_mul_neg_succ
    (interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf)
    (hf_pos.derivative (by lia)) hF_pos hdeg ?_
  intro r hr
  simpa only [eval_mul_derivative_eq_of_isRoot hr] using hroot_sign r hr

end RealRooted.MaWangInternal
