import RealRooted.MaWang
import RealRooted.SignEvaluation

/-!
# Ma--Wang derivative steps

The reusable one-step weak Ma--Wang criteria. Sequence closure and tactic
elaboration live in separate modules.
-/

open Polynomial

namespace RealRooted.MaWang

/-- Weak Ma--Wang derivative step using the Liu--Wang sign criterion.  This is
useful when the derivative coefficient can vanish at endpoint roots, so the
strict Ma--Wang sign condition is too strong. -/
theorem strictInterl_derivative_of_nonpos_of_pos_natDegree {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 1 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  exact
    strictInterl_of_interlaces_evalCoeff_nonpos
      (f := f) (g := f.derivative) (a := u) (b := v)
      hder hf'_pos hF_pos hdeg_lo hdeg_hi hv_nonpos

/-- Weak Ma--Wang derivative step with no degree hypothesis on `f`.

For `1 ≤ f.natDegree` this is
`strictInterl_derivative_of_nonpos_of_pos_natDegree`.  For a constant `f`,
`F = u * f + v * f'` has degree at most one by `hdeg_hi`, so a nonzero `F`
splits and the constant `f` is interlaced by it trivially. -/
theorem strictInterl_derivative_of_nonpos_of_splits {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative) := by
  rcases Nat.eq_zero_or_pos f.natDegree with hdeg0 | hdegf
  · have hF0 : u * f + v * f.derivative ≠ 0 := hF_pos.ne_zero
    rcases Nat.lt_or_ge (u * f + v * f.derivative).natDegree 1 with hF | hF
    · have hFdeg0 : (u * f + v * f.derivative).natDegree = 0 := by lia
      refine ⟨⟨hf_pos.ne_zero, hf⟩, ⟨hF0, Splits.of_natDegree_eq_zero hFdeg0⟩,
        [], [], by simp, by simp, ?_, ?_, Or.inr ⟨rfl, trivial⟩⟩
      · rw [eq_C_of_natDegree_eq_zero hdeg0, roots_C, Multiset.coe_nil]
      · rw [eq_C_of_natDegree_eq_zero hFdeg0, roots_C, Multiset.coe_nil]
    · exact StrictInterl.of_degree_zero_right_of_degree_one hf_pos.ne_zero hf hF0
        (isRealRooted_of_degree_one (by lia)).2 hdeg0 (by lia)
  · exact strictInterl_derivative_of_nonpos_of_pos_natDegree hf hdegf
      hdeg_lo hdeg_hi hF_pos hf_pos hv_nonpos

/-- Compatibility wrapper for the original degree-two weak Ma--Wang API. -/
theorem strictInterl_derivative_of_nonpos {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_pos_natDegree hf (by lia)
    hdeg_lo hdeg_hi hF_pos hf_pos hv_nonpos

/-- Ma--Wang derivative step where the target leading-coefficient and degree
side goals are supplied through a normalized recurrence identity. -/
theorem strictInterl_derivative_of_nonpos_of_recurrence {f F u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hrec : F = u * f + v * f.derivative)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf
    (by simpa only [hrec] using hdeg_lo)
    (by simpa only [hrec] using hdeg_hi)
    (by simpa only [hrec] using hF_pos)
    hf_pos hv_nonpos

theorem strictInterl_derivative_X_mul_of_nonneg_on_roots {f u q : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * q) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    StrictInterl f (u * f + (X * q) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr => eval_X_mul_nonpos_of_nonpos_of_nonneg
      (hf_roots r hr) (hq_nonneg r hr))

theorem strictInterl_derivative_C_mul_X_mul_of_nonneg_on_roots {f u q : ℝ[X]} {c : ℝ}
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
    StrictInterl f (u * f + (C c * X * q) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        hc (hf_roots r hr) (hq_nonneg r hr))

theorem strictInterl_derivative_X_mul_one_add_X_of_roots_in_Icc {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 + X)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ 0) :
    StrictInterl f (u * f + (X * (1 + X)) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr => eval_X_mul_one_add_X_nonpos_of_mem_Icc
      (hroot_lo r hr) (hroot_hi r hr))

theorem strictInterl_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
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
    StrictInterl f (u * f + (-(C c) * X * (1 + X)) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        hc (hroot_hi r hr))

theorem strictInterl_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval
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
    StrictInterl f (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
        (hroot_lo r hr) (hroot_hi r hr))

theorem strictInterl_derivative_neg_const {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + C (-c) * f.derivative).natDegree)
    (hdeg_hi : (u * f + C (-c) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + C (-c) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    StrictInterl f (u * f + C (-c) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun _ _ => eval_C_neg_nonpos_of_nonneg hc)

theorem strictInterl_derivative_neg_C_mul_X_sq {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C c) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    StrictInterl f (u * f + (-(C c) * X ^ 2) * f.derivative) :=
  strictInterl_derivative_of_nonpos hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun _ _ => eval_neg_C_mul_X_sq_nonpos_of_nonneg hc)

/-- Ma--Wang derivative step where the target leading-coefficient and degree
side goals are supplied through a normalized recurrence identity.  No degree
hypothesis on `f` is needed. -/
theorem strictInterl_derivative_of_nonpos_of_recurrence_of_splits {f F u v : ℝ[X]}
    (hf : f.Splits)
    (hrec : F = u * f + v * f.derivative)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf
    (by simpa only [hrec] using hdeg_lo)
    (by simpa only [hrec] using hdeg_hi)
    (by simpa only [hrec] using hF_pos)
    hf_pos hv_nonpos

/-- Version of `strictInterl_derivative_X_mul_of_nonneg_on_roots`
without a degree hypothesis. -/
theorem strictInterl_derivative_X_mul_of_nonneg_on_roots_of_splits {f u q : ℝ[X]}
    (hf : f.Splits)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * q) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    StrictInterl f (u * f + (X * q) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr => eval_X_mul_nonpos_of_nonpos_of_nonneg
      (hf_roots r hr) (hq_nonneg r hr))

/-- Version of `strictInterl_derivative_C_mul_X_mul_of_nonneg_on_roots`
without a degree hypothesis. -/
theorem strictInterl_derivative_C_mul_X_mul_of_nonneg_on_roots_of_splits
    {f u q : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * X * q) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    StrictInterl f (u * f + (C c * X * q) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        hc (hf_roots r hr) (hq_nonneg r hr))

/-- Version of `strictInterl_derivative_X_mul_one_add_X_of_roots_in_Icc`
without a degree hypothesis. -/
theorem strictInterl_derivative_X_mul_one_add_X_of_roots_in_Icc_of_splits
    {f u : ℝ[X]}
    (hf : f.Splits)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 + X)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ 0) :
    StrictInterl f (u * f + (X * (1 + X)) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr => eval_X_mul_one_add_X_nonpos_of_mem_Icc
      (hroot_lo r hr) (hroot_hi r hr))

/-- Version of `strictInterl_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one`
without a degree hypothesis. -/
theorem strictInterl_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one_of_splits
    {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
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
    StrictInterl f (u * f + (-(C c) * X * (1 + X)) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        hc (hroot_hi r hr))

/-- Version of `strictInterl_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval`
without a degree hypothesis. -/
theorem strictInterl_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval_of_splits
    {f u : ℝ[X]}
    (hf : f.Splits)
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
    StrictInterl f (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun r hr =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
        (hroot_lo r hr) (hroot_hi r hr))

/-- Version of `strictInterl_derivative_neg_const`
without a degree hypothesis. -/
theorem strictInterl_derivative_neg_const_of_splits {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdeg_lo : f.natDegree ≤ (u * f + C (-c) * f.derivative).natDegree)
    (hdeg_hi : (u * f + C (-c) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + C (-c) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    StrictInterl f (u * f + C (-c) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun _ _ => eval_C_neg_nonpos_of_nonneg hc)

/-- Version of `strictInterl_derivative_neg_C_mul_X_sq`
without a degree hypothesis. -/
theorem strictInterl_derivative_neg_C_mul_X_sq_of_splits {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C c) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    StrictInterl f (u * f + (-(C c) * X ^ 2) * f.derivative) :=
  strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos
    (fun _ _ => eval_neg_C_mul_X_sq_nonpos_of_nonneg hc)

end RealRooted.MaWang

namespace RealRooted

@[deprecated (since := "2026-10-05")]
alias strictInterl_mw_derivative_of_nonpos_of_pos_natDegree :=
  MaWang.strictInterl_derivative_of_nonpos_of_pos_natDegree

@[deprecated (since := "2026-10-05")]
alias strictInterl_mw_derivative_of_nonpos := MaWang.strictInterl_derivative_of_nonpos

@[deprecated (since := "2026-10-05")]
alias strictInterl_mw_derivative_of_nonpos_of_recurrence :=
  MaWang.strictInterl_derivative_of_nonpos_of_recurrence

@[deprecated (since := "2026-10-05")]
alias strictInterl_mw_derivative_C_mul_X_mul_of_nonneg_on_roots :=
  MaWang.strictInterl_derivative_C_mul_X_mul_of_nonneg_on_roots

@[deprecated (since := "2026-10-05")]
alias strictInterl_mw_derivative_X_mul_one_add_X_of_roots_in_Icc :=
  MaWang.strictInterl_derivative_X_mul_one_add_X_of_roots_in_Icc

@[deprecated (since := "2026-10-05")]
alias strictInterl_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one :=
  MaWang.strictInterl_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one

end RealRooted
