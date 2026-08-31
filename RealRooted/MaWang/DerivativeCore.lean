import RealRooted.MaWang.Weak

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Derivative specialization of the Liu--Wang mixed theorem in the degree `+1`
case. The hypothesis is the strict root-sign condition naturally obtained from
`F(r) = v(r) f'(r)`. -/
theorem prec_ma_wang_succ {f u v : ℝ[X]} (hf : f.Splits)
    (hdegf : 1 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  refine prec_of_interlaces_eval_mul_neg_succ hder hf'_pos hF_pos hdeg ?_
  intro r hr
  rw [eval_mul_derivative_eq_of_isRoot hr]
  simp_all

/-- Derivative specialization of the Liu--Wang mixed theorem in the same-degree
case. The hypothesis is the strict root-sign condition naturally obtained from
`F(r) = v(r) f'(r)`. -/
theorem prec_ma_wang_same {f u v : ℝ[X]} (hf : f.Splits)
    (hdegf : 1 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  refine prec_of_interlaces_eval_mul_neg_same hder hf'_pos hF_pos hdeg ?_
  intro r hr
  rw [eval_mul_derivative_eq_of_isRoot hr]
  simp_all

/-- Derivative specialization of the Liu--Wang mixed theorem allowing either the
same-degree or degree `+1` outcome. -/
theorem prec_ma_wang {f u v : ℝ[X]} (hf : f.Splits)
    (hdegf : 1 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  have hcases :
      (u * f + v * f.derivative).natDegree = f.natDegree ∨
        (u * f + v * f.derivative).natDegree = f.natDegree + 1 := by
    lia
  cases hcases with
  | inl hsame =>
      exact prec_ma_wang_same hf hdegf hsame hF_pos hf_pos hroot_sign
  | inr hsucc =>
      exact prec_ma_wang_succ hf hdegf hsucc hF_pos hf_pos hroot_sign

end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (prec_ma_wang_succ prec_ma_wang_same prec_ma_wang)

end RealRooted
