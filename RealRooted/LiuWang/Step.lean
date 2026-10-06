import RealRooted.GeneralizedLiuWang
import RealRooted.RootBounds
import RealRooted.SignEvaluation

/-!
# Liu--Wang single-step theorem backend

Reusable two-polynomial Liu--Wang criteria and polynomial sign certificates.
-/

open Polynomial

namespace RealRooted.LiuWang

private lemma oneNonneg : 0 ≤ (1 : ℝ) :=
  by norm_num

/-- Two-polynomial Liu--Wang wrapper with no tail summands.  This is the
common recurrence shape `F = a*f + b*g`, where `g` interlaces `f` and `b` has
the correct sign at the roots of `f`. -/
theorem strictInterl_two_of_nonpos {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) := by
  simpa [polynomialWeightedSum] using
    (strictInterl_generalizedLiuWang_of_no_common
      (l := ([] : List (ℝ[X] × ℝ[X])))
      hgf hg_pos (by simp) (by simp) (by simp)
      (by simpa [polynomialWeightedSum] using hF_pos)
      (by simpa [polynomialWeightedSum] using hdeg_lo)
      (by simpa [polynomialWeightedSum] using hdeg_hi)
      hno hb_nonpos)

/-- Liu--Wang step where the target leading-coefficient and degree side goals
are supplied through a normalized recurrence identity. -/
theorem strictInterl_two_of_nonpos_of_recurrence {f g F a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hrec : F = a * f + b * g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_succ : f.natDegree + 1 = F.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) :=
  strictInterl_two_of_nonpos hgf hg_pos
    (by rw [← hrec]; exact hF_pos)
    (by rw [← hrec, ← hdeg_succ]; lia)
    (by rw [← hrec, ← hdeg_succ])
    hno hb_nonpos

/-- Strict two-polynomial Liu--Wang wrapper with an explicit degree branch. -/
theorem strictInterl_two_strict_branch_of_neg {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdegree :
      (a * f + b * g).natDegree = f.natDegree ∨
        (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    StrictInterl f (a * f + b * g) := by
  rcases hdegree with hsame | hsucc
  · exact MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_same hgf hg_pos hF_pos hsame
      hno hb_neg
  · exact MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_succ hgf hg_pos hF_pos hsucc
      hno hb_neg

/-- Positive `t`-lag Liu--Wang step, using an explicit nonpositive-root
certificate for the current polynomial. -/
theorem strictInterl_positive_t_lag_of_roots_nonpos {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (C c * X) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr => eval_C_mul_X_nonpos_of_nonneg_of_nonpos hc (hf_roots r hr))

/-- Positive unit-`t` lag, accepting the normalized algebraic form `X * g`. -/
theorem strictInterl_positive_X_lag_of_roots_nonpos {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + X * g) := by
  simpa using
    (strictInterl_positive_t_lag_of_roots_nonpos
      (c := 1) hgf hg_pos hf_roots oneNonneg
      (by simpa using hF_pos)
      (by simpa using hdeg_lo)
      (by simpa using hdeg_hi)
      hno)

/-- Positive `t`-lag Liu--Wang step, using nonnegative coefficients to get
the nonpositive-root certificate. -/
theorem strictInterl_positive_t_lag_of_nonneg_coeffs {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (C c * X) * g) :=
  strictInterl_positive_t_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hc hF_pos hdeg_lo hdeg_hi hno

/-- Positive `t`-lag Liu--Wang step with recurrence-derived target
leading-coefficient and degree side goals. -/
theorem strictInterl_positive_t_lag_of_nonneg_coeffs_of_recurrence
    {f g F a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hrec : F = a * f + (C c * X) * g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_succ : f.natDegree + 1 = F.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (C c * X) * g) :=
  strictInterl_positive_t_lag_of_nonneg_coeffs hgf hg_pos hf_nonneg hc
    (by rw [← hrec]; exact hF_pos)
    (by rw [← hrec, ← hdeg_succ]; lia)
    (by rw [← hrec, ← hdeg_succ])
    hno

/-- Positive `t Q(t)` lag, using an explicit nonpositive-root certificate for
the current polynomial and nonnegativity of `Q` at those roots. -/
theorem strictInterl_positive_X_mul_lag_of_roots_nonpos {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (X * q) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg (hf_roots r hr) (hq_nonneg r hr))

/-- Positive `c t Q(t)` lag, using an explicit nonpositive-root certificate
and nonnegativity of `Q` at current roots. -/
theorem strictInterl_positive_C_mul_X_mul_lag_of_roots_nonpos {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X * q) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (C c * X * q) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        hc (hf_roots r hr) (hq_nonneg r hr))

/-- Positive `t Q(t)` lag, deriving the nonpositive-root certificate from
nonnegative coefficients. -/
theorem strictInterl_positive_X_mul_lag_of_nonneg_coeffs {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (X * q) * g) :=
  strictInterl_positive_X_mul_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hq_nonneg hF_pos hdeg_lo hdeg_hi hno

/-- Positive `c t Q(t)` lag, deriving the nonpositive-root certificate from
nonnegative coefficients. -/
theorem strictInterl_positive_C_mul_X_mul_lag_of_nonneg_coeffs
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
    StrictInterl f (a * f + (C c * X * q) * g) :=
  strictInterl_positive_C_mul_X_mul_lag_of_roots_nonpos hgf hg_pos
    (roots_nonpos_of_interlaces_of_nonneg_coeffs hgf hf_nonneg)
    hc hq_nonneg hF_pos hdeg_lo hdeg_hi hno

/-- Globally nonpositive negative-square lag Liu--Wang step. -/
theorem strictInterl_negative_square_lag {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c) * q ^ 2) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c) * q ^ 2) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c) * q ^ 2) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (-(C c) * q ^ 2) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_C_mul_sq_nonpos_of_nonneg hc)

/-- Globally nonpositive monic-quadratic lag Liu--Wang step, proved by a
discriminant certificate.  This covers negative-definite shapes such as
`-(t^2+2t+4)` without first rewriting them as a square plus a constant. -/
theorem strictInterl_negative_monic_quadratic_lag {f g a : ℝ[X]} {b c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdisc : b ^ 2 ≤ 4 * c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(X ^ 2 + C b * X + C c)) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(X ^ 2 + C b * X + C c)) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(X ^ 2 + C b * X + C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (-(X ^ 2 + C b * X + C c)) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_monic_quadratic_nonpos_of_discrim_nonpos hdisc)

/-- Globally nonpositive quadratic lag Liu--Wang step, proved by a
discriminant certificate.  This covers non-monic shapes such as
`-(2t^2-t+1)`. -/
theorem strictInterl_negative_quadratic_lag {f g A : ℝ[X]} {a b c : ℝ}
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
    StrictInterl f (A * f + (-(C a * X ^ 2 + C b * X + C c)) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_quadratic_nonpos_of_discrim_nonpos ha hc hdisc)

/-- Globally nonpositive negative-constant lag Liu--Wang step.  This is weaker
than the Favard route for orthogonal-polynomial recurrences, but it is a useful
two-polynomial sign-test path. -/
theorem strictInterl_negative_const_lag {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c)) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c)) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + (-(C c)) * g) :=
  strictInterl_two_of_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi hno
    (fun _r _hr => eval_neg_C_nonpos_of_nonneg hc)

/-- Globally nonpositive negative-constant lag, accepting the normalized
coefficient form `C (-c) * g`. -/
theorem strictInterl_negative_const_lag_C_neg {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + C (-c) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + C (-c) * g).natDegree)
    (hdeg_hi : (a * f + C (-c) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + C (-c) * g) := by
  simpa using
    (strictInterl_negative_const_lag hgf hg_pos hc
      (by simpa using hF_pos)
      (by simpa using hdeg_lo)
      (by simpa using hdeg_hi)
      hno)

end RealRooted.LiuWang
