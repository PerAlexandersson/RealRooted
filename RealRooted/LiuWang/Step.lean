import RealRooted.GeneralizedLiuWang
import RealRooted.RootBounds
import RealRooted.SignEvaluation

/-!
# Liu--Wang single-step theorem backend

Reusable two-polynomial Liu--Wang criteria and polynomial sign certificates.
-/

open Polynomial

namespace RealRooted

private lemma oneNonneg : 0 ≤ (1 : ℝ) :=
  by norm_num

private lemma oneNonnegSeq : ∀ _ : Nat, 0 ≤ (1 : ℝ) :=
  fun _ => oneNonneg

/-- Two-polynomial Liu--Wang wrapper with no tail summands.  This is the
common recurrence shape `F = a*f + b*g`, where `g` interlaces `f` and `b` has
the correct sign at the roots of `f`. -/
theorem prec_lw_two_of_nonpos {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  simpa [polynomialWeightedSum] using
    (prec_generalizedLiuWang_of_no_common
      (l := ([] : List (ℝ[X] × ℝ[X])))
      hgf hg_pos (by simp) (by simp) (by simp)
      (by simpa [polynomialWeightedSum] using hF_pos)
      (by simpa [polynomialWeightedSum] using hdeg_lo)
      (by simpa [polynomialWeightedSum] using hdeg_hi)
      hno hb_nonpos)

/-- Liu--Wang step where the target leading-coefficient and degree side goals
are supplied through a normalized recurrence identity. -/
theorem prec_lw_two_of_nonpos_of_recurrence {f g F a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hrec : F = a * f + b * g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_succ : f.natDegree + 1 = F.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) :=
  prec_lw_two_of_nonpos hgf hg_pos
    (by rw [← hrec]; exact hF_pos)
    (by rw [← hrec, ← hdeg_succ]; lia)
    (by rw [← hrec, ← hdeg_succ])
    hno hb_nonpos

/-- Strict two-polynomial Liu--Wang wrapper with no tail summands. -/
theorem prec_lw_two_strict_of_neg {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  simpa [polynomialWeightedSum] using
    (prec_generalizedLiuWang_strict
      (l := ([] : List (ℝ[X] × ℝ[X])))
      hgf hg_pos (by simp) (by simp) (by simp)
      (by simpa [polynomialWeightedSum] using hF_pos)
      (by simpa [polynomialWeightedSum] using hdeg_lo)
      (by simpa [polynomialWeightedSum] using hdeg_hi)
      hno hb_neg)

/-- Strict same-degree two-polynomial Liu--Wang wrapper. -/
theorem prec_lw_two_strict_same_of_neg {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  simpa [polynomialWeightedSum] using
    (prec_generalizedLiuWang_strict_same
      (l := ([] : List (ℝ[X] × ℝ[X])))
      hgf hg_pos (by simp) (by simp) (by simp)
      (by simpa [polynomialWeightedSum] using hF_pos)
      (by simpa [polynomialWeightedSum] using hdeg)
      hno hb_neg)

/-- Strict successor-degree two-polynomial Liu--Wang wrapper. -/
theorem prec_lw_two_strict_succ_of_neg {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  simpa [polynomialWeightedSum] using
    (prec_generalizedLiuWang_strict_succ
      (l := ([] : List (ℝ[X] × ℝ[X])))
      hgf hg_pos (by simp) (by simp) (by simp)
      (by simpa [polynomialWeightedSum] using hF_pos)
      (by simpa [polynomialWeightedSum] using hdeg)
      hno hb_neg)

/-- Strict two-polynomial Liu--Wang wrapper with an explicit degree branch. -/
theorem prec_lw_two_strict_branch_of_neg {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdegree :
      (a * f + b * g).natDegree = f.natDegree ∨
        (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  rcases hdegree with hsame | hsucc
  · exact prec_lw_two_strict_same_of_neg hgf hg_pos hF_pos hsame hno hb_neg
  · exact prec_lw_two_strict_succ_of_neg hgf hg_pos hF_pos hsucc hno hb_neg

/-- Positive `t`-lag Liu--Wang step, using an explicit nonpositive-root
certificate for the current polynomial. -/
theorem prec_lw_positive_t_lag_of_roots_nonpos {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr => eval_C_mul_X_nonpos_of_nonneg_of_nonpos hc (hf_roots r hr))

/-- Positive unit-`t` lag, accepting the normalized algebraic form `X * g`. -/
theorem prec_lw_positive_X_lag_of_roots_nonpos {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + X * g) := by
  simpa using
    (prec_lw_positive_t_lag_of_roots_nonpos
      (c := 1) hgf hg_pos hf_roots oneNonneg
      (by simpa using hF_pos)
      (by simpa using hdeg_lo)
      (by simpa using hdeg_hi)
      hno)

/-- Affine half-line lag `c t - a`, using an explicit nonpositive-root
certificate for the current polynomial. -/
theorem prec_lw_C_mul_X_sub_C_lag_of_roots_nonpos
    {f g A : ℝ[X]} {c a : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (ha : 0 ≤ a)
    (hF_pos : HasPosLeadingCoeff (A * f + (C c * X - C a) * g))
    (hdeg_lo : f.natDegree ≤ (A * f + (C c * X - C a) * g).natDegree)
    (hdeg_hi : (A * f + (C c * X - C a) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (C c * X - C a) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_C_mul_X_sub_C_nonpos_of_nonneg_of_nonneg_of_nonpos
        hc ha (hf_roots r hr))

/-- Positive `t`-lag Liu--Wang step, using nonnegative coefficients to get
the nonpositive-root certificate. -/
theorem prec_lw_positive_t_lag_of_nonneg_coeffs {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X) * g) :=
  prec_lw_positive_t_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hc hF_pos hdeg_lo hdeg_hi hno

/-- Positive `t`-lag Liu--Wang step with recurrence-derived target
leading-coefficient and degree side goals. -/
theorem prec_lw_positive_t_lag_of_nonneg_coeffs_of_recurrence
    {f g F a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hrec : F = a * f + (C c * X) * g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_succ : f.natDegree + 1 = F.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X) * g) :=
  prec_lw_positive_t_lag_of_nonneg_coeffs hgf hg_pos hf_nonneg hc
    (by rw [← hrec]; exact hF_pos)
    (by rw [← hrec, ← hdeg_succ]; lia)
    (by rw [← hrec, ← hdeg_succ])
    hno

/-- Affine half-line lag `c t - a`, deriving the root half-line certificate
from nonnegative coefficients of the current row. -/
theorem prec_lw_C_mul_X_sub_C_lag_of_nonneg_coeffs
    {f g A : ℝ[X]} {c a : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (ha : 0 ≤ a)
    (hF_pos : HasPosLeadingCoeff (A * f + (C c * X - C a) * g))
    (hdeg_lo : f.natDegree ≤ (A * f + (C c * X - C a) * g).natDegree)
    (hdeg_hi : (A * f + (C c * X - C a) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (C c * X - C a) * g) :=
  prec_lw_C_mul_X_sub_C_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hc ha hF_pos hdeg_lo hdeg_hi hno

/-- Positive affine lag `c(a+t)`, using an explicit upper root bound
`r <= -a` for the current polynomial.  This is the shifted-root-location
version of the positive `t` lag. -/
theorem prec_lw_positive_affine_lag_of_roots_upper
    {f g A : ℝ[X]} {c a : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ -a)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (A * f + (C c * (C a + X)) * g))
    (hdeg_lo : f.natDegree ≤ (A * f + (C c * (C a + X)) * g).natDegree)
    (hdeg_hi : (A * f + (C c * (C a + X)) * g).natDegree ≤
      f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (C c * (C a + X)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg hc (hf_roots r hr))

/-- Unit positive affine lag `a+t`, using an explicit upper root bound
`r <= -a` for the current polynomial. -/
theorem prec_lw_C_add_X_lag_of_roots_upper
    {f g A : ℝ[X]} {a : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ -a)
    (hF_pos : HasPosLeadingCoeff (A * f + (C a + X) * g))
    (hdeg_lo : f.natDegree ≤ (A * f + (C a + X) * g).natDegree)
    (hdeg_hi : (A * f + (C a + X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (C a + X) * g) := by
  simpa using
    (prec_lw_positive_affine_lag_of_roots_upper
      (c := 1) hgf hg_pos hf_roots oneNonneg
      (by simpa using hF_pos)
      (by simpa using hdeg_lo)
      (by simpa using hdeg_hi)
      hno)

/-- Positive `t Q(t)` lag, using an explicit nonpositive-root certificate for
the current polynomial and nonnegativity of `Q` at those roots. -/
theorem prec_lw_positive_X_mul_lag_of_roots_nonpos {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * q) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg (hf_roots r hr) (hq_nonneg r hr))

/-- Positive `c t Q(t)` lag, using an explicit nonpositive-root certificate
and nonnegativity of `Q` at current roots. -/
theorem prec_lw_positive_C_mul_X_mul_lag_of_roots_nonpos {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X * q) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X * q) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        hc (hf_roots r hr) (hq_nonneg r hr))

/-- Positive `t Q(t)` lag, deriving the nonpositive-root certificate from
nonnegative coefficients. -/
theorem prec_lw_positive_X_mul_lag_of_nonneg_coeffs {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * q) * g) :=
  prec_lw_positive_X_mul_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hq_nonneg hF_pos hdeg_lo hdeg_hi hno

/-- Positive `c t Q(t)` lag, deriving the nonpositive-root certificate from
nonnegative coefficients. -/
theorem prec_lw_positive_C_mul_X_mul_lag_of_nonneg_coeffs
    {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X * q) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X * q) * g) :=
  prec_lw_positive_C_mul_X_mul_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hc hq_nonneg hF_pos hdeg_lo hdeg_hi hno

/-- Family E `t R(t)` Liu--Wang step with an explicit half-line root
certificate.  This is a named alias for the existing `X * q` product-lag
wrapper, using `q` as the factor `R`. -/
theorem prec_lw_tR_lag_of_roots_nonpos {f g a R : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hR_nonneg : ∀ r, f.IsRoot r → 0 ≤ R.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * R) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * R) * g).natDegree)
    (hdeg_hi : (a * f + (X * R) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * R) * g) :=
  prec_lw_positive_X_mul_lag_of_roots_nonpos
    hgf hg_pos hf_roots hR_nonneg hF_pos hdeg_lo hdeg_hi hno

/-- Family E `t R(t)` Liu--Wang step, deriving the half-line root bound from
nonnegative coefficients of the current row. -/
theorem prec_lw_tR_lag_of_nonneg_coeffs {f g a R : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hR_nonneg : ∀ r, f.IsRoot r → 0 ≤ R.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * R) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * R) * g).natDegree)
    (hdeg_hi : (a * f + (X * R) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * R) * g) :=
  prec_lw_positive_X_mul_lag_of_nonneg_coeffs
    hgf hg_pos hf_nonneg hR_nonneg hF_pos hdeg_lo hdeg_hi hno

/-- Family E `t(1-t)` Liu--Wang step with an explicit half-line root
certificate. -/
theorem prec_lw_X_mul_one_sub_X_lag_of_roots_nonpos {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * (1 - X)) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * (1 - X)) * g).natDegree)
    (hdeg_hi : (a * f + (X * (1 - X)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * (1 - X)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r hr => eval_X_mul_one_sub_X_nonpos_of_nonpos (hf_roots _ hr))

/-- Family E `t(1-t)` Liu--Wang step, deriving the half-line root bound from
nonnegative coefficients of the current row. -/
theorem prec_lw_X_mul_one_sub_X_lag_of_nonneg_coeffs {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * (1 - X)) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * (1 - X)) * g).natDegree)
    (hdeg_hi : (a * f + (X * (1 - X)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * (1 - X)) * g) :=
  prec_lw_X_mul_one_sub_X_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hF_pos hdeg_lo hdeg_hi hno

/-- Family E `t(a-bt)` Liu--Wang step with an explicit half-line root
certificate. -/
theorem prec_lw_X_mul_C_sub_C_mul_X_lag_of_roots_nonpos
    {f g A : ℝ[X]} {a b : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (A * f + (X * (C a - C b * X)) * g))
    (hdeg_lo : f.natDegree ≤ (A * f + (X * (C a - C b * X)) * g).natDegree)
    (hdeg_hi :
      (A * f + (X * (C a - C b * X)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (X * (C a - C b * X)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_X_mul_C_sub_C_mul_X_nonpos_of_nonneg_of_nonneg_of_nonpos
        ha hb (hf_roots r hr))

/-- Family E `t(a-bt)` Liu--Wang step, deriving the half-line root bound from
nonnegative coefficients of the current row. -/
theorem prec_lw_X_mul_C_sub_C_mul_X_lag_of_nonneg_coeffs
    {f g A : ℝ[X]} {a b : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hF_pos : HasPosLeadingCoeff (A * f + (X * (C a - C b * X)) * g))
    (hdeg_lo : f.natDegree ≤ (A * f + (X * (C a - C b * X)) * g).natDegree)
    (hdeg_hi :
      (A * f + (X * (C a - C b * X)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (X * (C a - C b * X)) * g) :=
  prec_lw_X_mul_C_sub_C_mul_X_lag_of_roots_nonpos hgf hg_pos ha hb
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hF_pos hdeg_lo hdeg_hi hno

/-- Family E `c t(a-bt)` Liu--Wang step with an explicit half-line root
certificate. -/
theorem prec_lw_C_mul_X_mul_C_sub_C_mul_X_lag_of_roots_nonpos
    {f g A : ℝ[X]} {c a b : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (A * f + (C c * X * (C a - C b * X)) * g))
    (hdeg_lo :
      f.natDegree ≤ (A * f + (C c * X * (C a - C b * X)) * g).natDegree)
    (hdeg_hi :
      (A * f + (C c * X * (C a - C b * X)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (C c * X * (C a - C b * X)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_C_mul_X_mul_C_sub_C_mul_X_nonpos hc ha hb (hf_roots r hr))

/-- Family E `c t(a-bt)` Liu--Wang step, deriving the half-line root bound
from nonnegative coefficients of the current row. -/
theorem prec_lw_C_mul_X_mul_C_sub_C_mul_X_lag_of_nonneg_coeffs
    {f g A : ℝ[X]} {c a b : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hF_pos : HasPosLeadingCoeff (A * f + (C c * X * (C a - C b * X)) * g))
    (hdeg_lo :
      f.natDegree ≤ (A * f + (C c * X * (C a - C b * X)) * g).natDegree)
    (hdeg_hi :
      (A * f + (C c * X * (C a - C b * X)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (C c * X * (C a - C b * X)) * g) :=
  prec_lw_C_mul_X_mul_C_sub_C_mul_X_lag_of_roots_nonpos hgf hg_pos hc ha hb
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hF_pos hdeg_lo hdeg_hi hno

/-- Globally nonpositive negative-square lag Liu--Wang step. -/
theorem prec_lw_negative_square_lag {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c) * q ^ 2) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c) * q ^ 2) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c) * q ^ 2) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c) * q ^ 2) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_C_mul_sq_nonpos_of_nonneg hc)

/-- Globally nonpositive monic-quadratic lag Liu--Wang step, proved by a
discriminant certificate.  This covers negative-definite shapes such as
`-(t^2+2t+4)` without first rewriting them as a square plus a constant. -/
theorem prec_lw_negative_monic_quadratic_lag {f g a : ℝ[X]} {b c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdisc : b ^ 2 ≤ 4 * c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(X ^ 2 + C b * X + C c)) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(X ^ 2 + C b * X + C c)) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(X ^ 2 + C b * X + C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(X ^ 2 + C b * X + C c)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_monic_quadratic_nonpos_of_discrim_nonpos hdisc)

/-- Globally nonpositive quadratic lag Liu--Wang step, proved by a
discriminant certificate.  This covers non-monic shapes such as
`-(2t^2-t+1)`. -/
theorem prec_lw_negative_quadratic_lag {f g A : ℝ[X]} {a b c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 ≤ a)
    (hc : 0 ≤ c)
    (hdisc : b ^ 2 ≤ 4 * a * c)
    (hF_pos : HasPosLeadingCoeff (A * f + (-(C a * X ^ 2 + C b * X + C c)) * g))
    (hdeg_lo :
      f.natDegree ≤ (A * f + (-(C a * X ^ 2 + C b * X + C c)) * g).natDegree)
    (hdeg_hi :
      (A * f + (-(C a * X ^ 2 + C b * X + C c)) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (A * f + (-(C a * X ^ 2 + C b * X + C c)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_quadratic_nonpos_of_discrim_nonpos ha hc hdisc)

/-- Globally nonpositive negative-constant lag Liu--Wang step.  This is weaker
than the Favard route for orthogonal-polynomial recurrences, but it is a useful
two-polynomial sign-test path. -/
theorem prec_lw_negative_const_lag {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c)) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c)) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c)) * g) :=
  prec_lw_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_C_nonpos_of_nonneg hc)

/-- Globally nonpositive negative-constant lag, accepting the normalized
coefficient form `C (-c) * g`. -/
theorem prec_lw_negative_const_lag_C_neg {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + C (-c) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + C (-c) * g).natDegree)
    (hdeg_hi : (a * f + C (-c) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + C (-c) * g) := by
  simpa using
    (prec_lw_negative_const_lag hgf hg_pos hc
      (by simpa using hF_pos)
      (by simpa using hdeg_lo)
      (by simpa using hdeg_hi)
      hno)

end RealRooted
