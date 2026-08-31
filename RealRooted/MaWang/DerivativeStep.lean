import RealRooted.MaWang
import RealRooted.SignEvaluation

/-!
# Ma--Wang derivative steps

The reusable one-step weak Ma--Wang criteria. Sequence closure and tactic
elaboration live in separate modules.
-/

open Polynomial

namespace RealRooted

/-- Weak Ma--Wang derivative step using the Liu--Wang sign criterion.  This is
useful when the derivative coefficient can vanish at endpoint roots, so the
strict Ma--Wang sign condition is too strong. -/
theorem prec_mw_derivative_of_nonpos_of_pos_natDegree {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 1 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  exact
    prec_of_interlaces_evalCoeff_nonpos
      (f := f) (g := f.derivative) (a := u) (b := v)
      hder hf'_pos hF_pos hdeg_lo hdeg_hi hv_nonpos

/-- Compatibility wrapper for the original degree-two weak Ma--Wang API. -/
theorem prec_mw_derivative_of_nonpos {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) :=
  prec_mw_derivative_of_nonpos_of_pos_natDegree hf (by lia)
    hdeg_lo hdeg_hi hF_pos hf_pos hv_nonpos

/-- Ma--Wang derivative step where the target leading-coefficient and degree
side goals are supplied through a normalized recurrence identity. -/
theorem prec_mw_derivative_of_nonpos_of_recurrence {f F u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hrec : F = u * f + v * f.derivative)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf
    (by simpa only [hrec] using hdeg_lo)
    (by simpa only [hrec] using hdeg_hi)
    (by simpa only [hrec] using hF_pos)
    hf_pos hv_nonpos

theorem prec_mw_derivative_X_mul_of_nonneg_on_roots {f u q : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * q) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    Prec f (u * f + (X * q) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr => eval_X_mul_nonpos_of_nonpos_of_nonneg
      (hf_roots r hr) (hq_nonneg r hr))

theorem prec_mw_derivative_C_mul_X_mul_of_nonneg_on_roots {f u q : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * X * q) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    Prec f (u * f + (C c * X * q) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        hc (hf_roots r hr) (hq_nonneg r hr))

theorem prec_mw_derivative_X_mul_one_add_X_of_roots_in_Icc {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 + X)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ 0) :
    Prec f (u * f + (X * (1 + X)) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr => eval_X_mul_one_add_X_nonpos_of_mem_Icc
      (hroot_lo r hr) (hroot_hi r hr))

theorem prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
    {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X * (1 + X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff (u * f + (-(C c) * X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ -1) :
    Prec f (u * f + (-(C c) * X * (1 + X)) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        hc (hroot_hi r hr))

theorem prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval
    {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤
        (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff
        (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ -(1 / 2 : ℝ)) :
    Prec f (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
        (hroot_lo r hr) (hroot_hi r hr))

theorem prec_mw_derivative_neg_const {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + C (-c) * f.derivative).natDegree)
    (hdeg_hi : (u * f + C (-c) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + C (-c) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    Prec f (u * f + C (-c) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun _ _ => eval_C_neg_nonpos_of_nonneg hc)

theorem prec_mw_derivative_neg_C_mul_X_sq {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C c) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    Prec f (u * f + (-(C c) * X ^ 2) * f.derivative) :=
  prec_mw_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun _ _ => eval_neg_C_mul_X_sq_nonpos_of_nonneg hc)

end RealRooted
