import RealRooted.LiuWang.General

open Polynomial

namespace RealRooted.MaWangInternal

/-- Degree-bounded structured Liu--Wang theorem in the weak-sign regime, for a successor-degree
interlacer `g`.  This is the special case `Interlaces g f` of
`RealRooted.LiuWang.strictInterl_mul_add_mul_of_eval_nonpos`. -/
theorem strictInterl_of_interlaces_evalCoeff_nonpos
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) :=
  LiuWang.strictInterl_mul_add_mul_of_eval_nonpos hgf.toStrictInterl hg_pos hF_pos hdeg_lo
    hdeg_hi hb_nonpos

end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (strictInterl_of_interlaces_evalCoeff_nonpos)

end RealRooted
