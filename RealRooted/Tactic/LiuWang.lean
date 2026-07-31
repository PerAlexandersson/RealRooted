import RealRooted.GeneralizedLiuWang
import RealRooted.Tactic.Finish
import RealRooted.Tactic.RootBounds
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.SideGoals

/-!
# Generalized Liu-Wang tactic

Dispatcher tactics:

```lean
rr_liu_wang
rr_liu_wang_strict
```

Primary target:
finite weighted sums where one or more previous polynomials interlace a common
base polynomial, and the coefficient polynomials have the required sign at
the roots of the base.

The tactics apply `prec_generalizedLiuWang_of_no_common` or the strict
finite-family variants after the user supplies the distinguished interlacer
and remaining summands.

First intended regression examples:

- clean Family E three-term recurrences;
- selected Family G/Jacobi-like recurrences;
- `LiuWangBenchmark` after the basic shape is stable.
-/

open Polynomial

namespace RealRooted

private lemma oneNonneg : 0 ≤ (1 : ℝ) :=
  rr_side_nonneg_term

private lemma oneNonnegSeq : ∀ _ : Nat, 0 ≤ (1 : ℝ) :=
  fun _ => oneNonneg

syntax (name := rr_lw_recurrence_seq) "rr_lw_recurrence_seq " term : term

syntax (name := rr_lw_recurrence_mul_assoc_seq) "rr_lw_recurrence_mul_assoc_seq " term : term

syntax (name := rr_lw_simpa) "rr_lw_simpa " term : term

syntax (name := rr_lw_simpa_mul_assoc) "rr_lw_simpa_mul_assoc " term : term

macro_rules
  | `(rr_lw_recurrence_seq $hrec:term) =>
      `(fun n => by simpa using $hrec n)
  | `(rr_lw_recurrence_mul_assoc_seq $hrec:term) =>
      `(fun n => by simpa only [mul_assoc] using $hrec n)
  | `(rr_lw_simpa $h:term) =>
      `(by simpa using $h)
  | `(rr_lw_simpa_mul_assoc $h:term) =>
      `(by simpa [mul_assoc] using $h)

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
    (by
      rr_recurrence_simpa using recurrence := hrec, certificate := hF_pos)
    (by
      rr_recurrence_degree using recurrence := hrec, degree := hdeg_succ)
    (by
      rr_recurrence_degree using recurrence := hrec, degree := hdeg_succ)
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
    (by
      rr_recurrence_simpa using recurrence := hrec, certificate := hF_pos)
    (by
      rr_recurrence_degree using recurrence := hrec, degree := hdeg_succ)
    (by
      rr_recurrence_degree using recurrence := hrec, degree := hdeg_succ)
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

/-- Sequence-level Liu--Wang induction for a lag coefficient that is
nonpositive at all roots of the current row. -/
theorem prec_lw_nonpos_lag_sequence {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  simpa [← hrec n] using
    prec_lw_two_of_nonpos_of_recurrence (hprev.toInterlaces (hdeg_succ n))
      (hpos n) (hrec n)
      (hpos (n + 2)) (hdeg_succ (n + 1)) (hno n) (hB_nonpos n)

/-- Certificate package for strict-degree nonpositive-lag Liu--Wang
sequence induction.

This is the first generic state layer for high-volume generated recurrence
shells: sequence-specific files provide the data once, and tactic endpoints can
project either the `Prec` chain or rowwise real-rootedness from the package. -/
structure LwNonposLagSequenceState (P A B : Nat → ℝ[X]) where
  hbase : Prec (P 0) (P 1)
  hpos : ∀ n : Nat, HasPosLeadingCoeff (P n)
  hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0
  hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n
  hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree
  hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r

namespace LwNonposLagSequenceState

/-- Build a nonpositive-lag state from a plain lag-sign certificate. -/
theorem of_nonpos {P A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A B where
  hbase := hbase
  hpos := hpos
  hB_nonpos := hB_nonpos
  hrec := hrec
  hdeg_succ := hdeg_succ
  hno := hno

/-- Project the consecutive `Prec` chain from a nonpositive-lag state. -/
theorem prec_sequence {P A B : Nat → ℝ[X]}
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_lw_nonpos_lag_sequence h.hbase h.hpos h.hB_nonpos
    h.hrec h.hdeg_succ h.hno

/-- Project rowwise real-rootedness from a nonpositive-lag state. -/
theorem isRealRooted {P A B : Nat → ℝ[X]}
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (h.prec_sequence n).1

/-- Project rowwise nonzero certificates from a nonpositive-lag state. -/
theorem ne_zero_sequence {P A B : Nat → ℝ[X]}
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (h.isRealRooted n).1

/-- Project rowwise splitting from a nonpositive-lag state. -/
theorem splits_sequence {P A B : Nat → ℝ[X]}
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, (P n).Splits :=
  fun n => (h.isRealRooted n).2

/-- Project consecutive interlacing from a nonpositive-lag state. -/
theorem interlaces_sequence {P A B : Nat → ℝ[X]}
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) :=
  interlaces_of_prec_chain h.prec_sequence h.hdeg_succ

/-- Transport a nonpositive-lag state across pointwise equality of lag indices. -/
theorem of_B_congr {P A B B' : Nat → ℝ[X]}
    (h : LwNonposLagSequenceState P A B) (hB : ∀ n : Nat, B n = B' n) :
    LwNonposLagSequenceState P A B' where
  hbase := h.hbase
  hpos := h.hpos
  hB_nonpos := fun n r hr => by
    simpa [hB n] using h.hB_nonpos n r hr
  hrec := fun n => by
    simpa [hB n] using h.hrec n
  hdeg_succ := h.hdeg_succ
  hno := h.hno

end LwNonposLagSequenceState

/-- Certificate package for strict negative-lag Liu--Wang sequence induction
with an explicit same-degree/successor-degree branch.

This is the plateau-safe analogue of `LwNonposLagSequenceState`: the state
does not infer the degree pattern.  It carries the branch certificate and a
converter from the previous `Prec` certificate to the interlacing input needed
by the strict Liu--Wang step. -/
structure LwStrictBranchSequenceState (P A B : Nat → ℝ[X]) where
  hbase : Prec (P 0) (P 1)
  hpos : ∀ n : Nat, HasPosLeadingCoeff (P n)
  hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n
  hdegree : ∀ n : Nat,
    (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1
  hinter : ∀ n : Nat,
    Prec (P n) (P (n + 1)) → Interlaces (P n) (P (n + 1))
  hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r
  hB_neg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r < 0

namespace LwStrictBranchSequenceState

/-- Build a strict branch state from its explicit certificate fields. -/
theorem of_branch {P A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hinter : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Interlaces (P n) (P (n + 1)))
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)
    (hB_neg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r < 0) :
    LwStrictBranchSequenceState P A B where
  hbase := hbase
  hpos := hpos
  hrec := hrec
  hdegree := hdegree
  hinter := hinter
  hno := hno
  hB_neg := hB_neg

/-- Project the consecutive `Prec` chain from a strict branch state. -/
theorem prec_sequence {P A B : Nat → ℝ[X]}
    (h : LwStrictBranchSequenceState P A B) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_degree_branches h.hbase h.hdegree ?_ ?_
  · intro n hdeg hprev
    have htarget_pos :
        HasPosLeadingCoeff (A n * P (n + 1) + B n * P n) := by
      simpa [← h.hrec n] using h.hpos (n + 2)
    have hbranch :
        (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree ∨
          (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree + 1 := by
      left
      simpa [← h.hrec n] using hdeg
    have hstep :
        Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) :=
      prec_lw_two_strict_branch_of_neg (h.hinter n hprev) (h.hpos n)
        htarget_pos hbranch (h.hno n) (h.hB_neg n)
    simpa [← h.hrec n] using hstep
  · intro n hdeg hprev
    have htarget_pos :
        HasPosLeadingCoeff (A n * P (n + 1) + B n * P n) := by
      simpa [← h.hrec n] using h.hpos (n + 2)
    have hbranch :
        (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree ∨
          (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree + 1 := by
      right
      simpa [← h.hrec n] using hdeg
    have hstep :
        Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) :=
      prec_lw_two_strict_branch_of_neg (h.hinter n hprev) (h.hpos n)
        htarget_pos hbranch (h.hno n) (h.hB_neg n)
    simpa [← h.hrec n] using hstep

/-- Project rowwise real-rootedness from a strict branch state. -/
theorem isRealRooted {P A B : Nat → ℝ[X]}
    (h : LwStrictBranchSequenceState P A B) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (h.prec_sequence n).1

/-- Project rowwise nonzero certificates from a strict branch state. -/
theorem ne_zero_sequence {P A B : Nat → ℝ[X]}
    (h : LwStrictBranchSequenceState P A B) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (h.isRealRooted n).1

/-- Project rowwise splitting from a strict branch state. -/
theorem splits_sequence {P A B : Nat → ℝ[X]}
    (h : LwStrictBranchSequenceState P A B) :
    ∀ n : Nat, (P n).Splits :=
  fun n => (h.isRealRooted n).2

/-- Project consecutive interlacing from a strict branch state. -/
theorem interlaces_sequence {P A B : Nat → ℝ[X]}
    (h : LwStrictBranchSequenceState P A B) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) :=
  fun n => h.hinter n (h.prec_sequence n)

end LwStrictBranchSequenceState

/-- Sequence-level Liu--Wang induction where lag nonpositivity may use the
current row's real-rootedness certificate from the induction state. -/
theorem prec_lw_nonpos_lag_sequence_of_inductive_nonpos {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
      ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  simpa [← hrec n] using
    prec_lw_two_of_nonpos_of_recurrence (hprev.toInterlaces (hdeg_succ n))
      (hpos n) (hrec n)
      (hpos (n + 2)) (hdeg_succ (n + 1)) (hno n) (hB_nonpos n hprev.2.1)

namespace LwNonposLagSequenceState

/-- Build a nonpositive-lag state from an inductive lag-sign supplier.

This turns the rowwise real-rootedness-dependent sign certificate into the
plain sign field carried by `LwNonposLagSequenceState`. -/
theorem of_inductive_nonpos {P A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
      ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A B := by
  let hprec :=
    prec_lw_nonpos_lag_sequence_of_inductive_nonpos
      hbase hpos hB_nonpos hrec hdeg_succ hno
  exact
    { hbase := hbase
      hpos := hpos
      hB_nonpos := fun n r hr =>
        hB_nonpos n (hprec n).2.1 r hr
      hrec := hrec
      hdeg_succ := hdeg_succ
      hno := hno }

end LwNonposLagSequenceState

/-- Real-rootedness corollary for sequence-level nonpositive-lag
Liu--Wang induction. -/
theorem isRealRooted_of_lw_nonpos_lag_sequence {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_nonpos
    hbase hpos hB_nonpos hrec hdeg_succ hno).isRealRooted

/-- Real-rootedness corollary for sequence-level nonpositive-lag Liu--Wang
induction with an inductive lag-sign certificate. -/
theorem isRealRooted_of_lw_nonpos_lag_sequence_of_inductive_nonpos
    {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
      ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_inductive_nonpos
    hbase hpos hB_nonpos hrec hdeg_succ hno).isRealRooted

/-- Denominator-fused Liu--Wang induction for a scalar left factor.

This wrapper consumes the raw generated recurrence
`C d_n * P_{n+2} = C d_n * (A_n P_{n+1} + B_n P_n)` and cancels the
nonzero scalar denominator internally before applying the usual nonpositive-lag
sequence theorem. -/
theorem prec_lw_nonpos_lag_sequence_den {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_lw_nonpos_lag_sequence (A := A) hbase hpos hB_nonpos
    (fun n => eq_of_C_mul_eq_C_mul (hden n) (hraw n)) hdeg_succ hno

namespace LwNonposLagSequenceState

/-- Build a nonpositive-lag state from a scalar-denominator recurrence. -/
theorem of_den {P A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A B where
  hbase := hbase
  hpos := hpos
  hB_nonpos := hB_nonpos
  hrec := fun n => eq_of_C_mul_eq_C_mul (hden n) (hraw n)
  hdeg_succ := hdeg_succ
  hno := hno

end LwNonposLagSequenceState

/-- Real-rootedness corollary for denominator-fused nonpositive-lag
Liu--Wang induction. -/
theorem isRealRooted_of_lw_nonpos_lag_sequence_den {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_den
    hbase hpos hB_nonpos hden hraw hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for globally nonpositive negative-constant lags. -/
theorem of_negative_const_lag {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => -(C (c n))) where
  hbase := hbase
  hpos := hpos
  hB_nonpos := fun n _ _ => eval_neg_C_nonpos_of_nonneg (hc n)
  hrec := hrec
  hdeg_succ := hdeg_succ
  hno := hno

/-- Build a state for globally nonpositive normalized `C (-c_n)` lags. -/
theorem of_negative_const_C_neg_lag {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (-(c n))) where
  hbase := hbase
  hpos := hpos
  hB_nonpos := fun n _ _ => eval_C_neg_nonpos_of_nonneg (hc n)
  hrec := hrec
  hdeg_succ := hdeg_succ
  hno := hno

end LwNonposLagSequenceState

/-- Sequence-level Liu--Wang induction for globally nonpositive negative
constant lag. -/
theorem prec_lw_negative_const_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_const_lag
    hbase hpos hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the negative-constant sequence wrapper. -/
theorem isRealRooted_of_lw_negative_const_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_const_lag
    hbase hpos hc hrec hdeg_succ hno).isRealRooted

/-- Sequence-level Liu--Wang induction for normalized `C (-c_n)` lag. -/
theorem prec_lw_negative_const_C_neg_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_const_C_neg_lag
    hbase hpos hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the normalized `C (-c_n)` lag wrapper. -/
theorem isRealRooted_of_lw_negative_const_C_neg_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_const_C_neg_lag
    hbase hpos hc hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for globally nonpositive negative-square lags. -/
theorem of_negative_square_lag {P A q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => -(C (c n)) * (q n) ^ 2) :=
  of_inductive_nonpos
    (B := fun n => -(C (c n)) * (q n) ^ 2) hbase hpos
    (fun n _ _ _ => eval_neg_C_mul_sq_nonpos_of_nonneg (hc n))
    hrec hdeg_succ hno

/-- Build a normalized negative-square state from a split scalar denominator. -/
theorem of_negative_square_lag_den_coeff
    {P A q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => -(C (c n)) * (q n) ^ 2) := by
  refine of_negative_square_lag hbase hpos hc ?_ hdeg_succ hno
  intro n
  have hnorm :
      P (n + 2) =
        A n * P (n + 1) + C (c n) * (-(q n) ^ 2 * P n) :=
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
  calc
    P (n + 2) = A n * P (n + 1) + C (c n) * (-(q n) ^ 2 * P n) := hnorm
    _ = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n := by ring

/-- Build a state for the literal unit negative-square lag `-q_n^2`. -/
theorem of_negative_square_lag_unit {P A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((q n) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => -((q n) ^ 2)) :=
  of_B_congr
    (of_negative_square_lag
      (c := fun _ => 1) hbase hpos oneNonnegSeq
      (fun n => by simpa using hrec n) hdeg_succ hno)
    (fun n => by simp)

/-- Build a state for globally nonpositive monic quadratic lags. -/
theorem of_negative_monic_quadratic_lag
    {P A : Nat → ℝ[X]} {b c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => -(X ^ 2 + C (b n) * X + C (c n))) :=
  of_inductive_nonpos
    (B := fun n => -(X ^ 2 + C (b n) * X + C (c n))) hbase hpos
    (fun n _ _ _ => eval_neg_monic_quadratic_nonpos_of_discrim_nonpos
      (hdisc n))
    hrec hdeg_succ hno

/-- Build a state for globally nonpositive non-monic quadratic lags. -/
theorem of_negative_quadratic_lag
    {P A : Nat → ℝ[X]} {a b c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * a n * c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (a n) * X ^ 2 + C (b n) * X + C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => -(C (a n) * X ^ 2 + C (b n) * X + C (c n))) :=
  of_inductive_nonpos
    (B := fun n => -(C (a n) * X ^ 2 + C (b n) * X + C (c n)))
    hbase hpos
    (fun n _ _ _ => eval_neg_quadratic_nonpos_of_discrim_nonpos
      (ha n) (hc n) (hdisc n))
    hrec hdeg_succ hno

/-- Build a normalized non-monic quadratic state from a scalar denominator. -/
theorem of_negative_quadratic_lag_den_coeff
    {P Araw : Nat → ℝ[X]} {araw braw craw a b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * a n * c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (ha_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = a n)
    (hb_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = b n)
    (hc_coeff : ∀ n : Nat, (d n)⁻¹ * craw n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        Araw n * P (n + 1) +
          (-(C (araw n) * X ^ 2 + C (braw n) * X + C (craw n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P (fun n => C ((d n)⁻¹) * Araw n)
      (fun n => -(C (a n) * X ^ 2 + C (b n) * X + C (c n))) := by
  refine
    of_negative_quadratic_lag
      (A := fun n => C ((d n)⁻¹) * Araw n)
      hbase hpos ha hc hdisc ?_ hdeg_succ hno
  intro n
  have hnorm :
      P (n + 2) =
        C (d n)⁻¹ *
          (Araw n * P (n + 1) +
            (-(C (araw n) * X ^ 2 + C (braw n) * X + C (craw n))) * P n) :=
    eq_C_inv_mul_of_C_mul_eq (hden n) (hraw n)
  calc
    P (n + 2) =
        C (d n)⁻¹ *
          (Araw n * P (n + 1) +
            (-(C (araw n) * X ^ 2 + C (braw n) * X + C (craw n))) * P n) :=
      hnorm
    _ =
        (C ((d n)⁻¹) * Araw n) * P (n + 1) +
          (-(C (a n) * X ^ 2 + C (b n) * X + C (c n))) * P n := by
      rw [← ha_coeff n, ← hb_coeff n, ← hc_coeff n]
      simp only [C_mul]
      ring_nf

end LwNonposLagSequenceState

/-- Sequence-level Liu--Wang induction for globally nonpositive negative-square
lag. -/
theorem prec_lw_negative_square_lag_sequence {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_square_lag
    hbase hpos hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the negative-square sequence wrapper. -/
theorem isRealRooted_of_lw_negative_square_lag_sequence {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_square_lag
    hbase hpos hc hrec hdeg_succ hno).isRealRooted

/-- Sequence-level negative-square lag with unit scalar coefficient.

This accepts the natural recurrence spelling `-q_n^2 P_n` without requiring a
visible `-(C 1) * q_n^2` coefficient. -/
theorem prec_lw_negative_square_lag_sequence_unit {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((q n) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_square_lag_unit
    hbase hpos hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for unit-coefficient negative-square lag. -/
theorem isRealRooted_of_lw_negative_square_lag_sequence_unit {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((q n) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_square_lag_unit
    hbase hpos hrec hdeg_succ hno).isRealRooted

/-- Denominator-fused negative-square Liu--Wang induction for split raw
coefficients.

This matches generated recurrences where the raw recurrence has
`C d_n * P_{n+2}` on the left, the current-row summand already multiplied by
`C d_n`, and the lag summand written as
`C b_n * (-(q_n)^2 * P_n)`.  The side condition
`d_n⁻¹ * b_n = c_n` gives the normalized negative-square coefficient. -/
theorem prec_lw_negative_square_lag_sequence_den_coeff {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_square_lag_den_coeff
    hbase hpos hc hden hcoeff hraw hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for split-coefficient denominator-fused
negative-square Liu--Wang induction. -/
theorem isRealRooted_of_lw_negative_square_lag_sequence_den_coeff
    {P : Nat → ℝ[X]} {A q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_square_lag_den_coeff
    hbase hpos hc hden hcoeff hraw hdeg_succ hno).isRealRooted

/-- Sequence-level Liu--Wang induction for a negative-definite monic quadratic
lag. -/
theorem prec_lw_negative_monic_quadratic_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {b c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_monic_quadratic_lag
    hbase hpos hdisc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the negative-definite monic quadratic
sequence wrapper. -/
theorem isRealRooted_of_lw_negative_monic_quadratic_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {b c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_monic_quadratic_lag
    hbase hpos hdisc hrec hdeg_succ hno).isRealRooted

/-- Sequence-level Liu--Wang induction for a globally nonpositive quadratic
lag with a non-monic leading coefficient. -/
theorem prec_lw_negative_quadratic_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {a b c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * a n * c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (a n) * X ^ 2 + C (b n) * X + C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_quadratic_lag
    hbase hpos ha hc hdisc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the non-monic negative quadratic sequence
wrapper. -/
theorem isRealRooted_of_lw_negative_quadratic_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a b c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * a n * c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (a n) * X ^ 2 + C (b n) * X + C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_quadratic_lag
    hbase hpos ha hc hdisc hrec hdeg_succ hno).isRealRooted

/-- Denominator-fused Liu--Wang induction for a raw split non-monic
quadratic lag.

This matches generated recurrences where a scalar factor `d_n` multiplies
`P_{n+2}`, while the lag summand is written with raw quadratic coefficients.
The three coefficient identities state that division by `d_n` gives the
normalized quadratic used for the sign certificate. -/
theorem prec_lw_negative_quadratic_lag_sequence_den_coeff {P : Nat → ℝ[X]}
    {Araw : Nat → ℝ[X]} {araw braw craw a b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * a n * c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (ha_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = a n)
    (hb_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = b n)
    (hc_coeff : ∀ n : Nat, (d n)⁻¹ * craw n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        Araw n * P (n + 1) +
          (-(C (araw n) * X ^ 2 + C (braw n) * X + C (craw n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
    hbase hpos ha hc hdisc hden ha_coeff hb_coeff hc_coeff
    hraw hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for denominator-fused raw split non-monic
quadratic Liu--Wang induction. -/
theorem isRealRooted_of_lw_negative_quadratic_lag_sequence_den_coeff
    {P : Nat → ℝ[X]} {Araw : Nat → ℝ[X]} {araw braw craw a b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hdisc : ∀ n : Nat, (b n) ^ 2 ≤ 4 * a n * c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (ha_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = a n)
    (hb_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = b n)
    (hc_coeff : ∀ n : Nat, (d n)⁻¹ * craw n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        Araw n * P (n + 1) +
          (-(C (araw n) * X ^ 2 + C (braw n) * X + C (craw n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
    hbase hpos ha hc hdisc hden ha_coeff hb_coeff hc_coeff
    hraw hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for a positive scalar multiple of the `X` lag. -/
theorem of_positive_t_lag {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * X) :=
  of_inductive_nonpos (B := fun n => C (c n) * X) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level positive `t`-lag Liu--Wang induction.

This is the reusable full proof shell for strict degree-increasing recurrences
of the form
`P_{n+2} = A_n P_{n+1} + c_n X P_n`.
The sequence-specific file supplies the base interlacing, recurrence identity,
coefficient/degree certificates, and no-common-root hypothesis. -/
theorem prec_lw_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary of the sequence-level positive `t`-lag
Liu--Wang induction. -/
theorem isRealRooted_of_lw_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for the unit `X` lag. -/
theorem of_positive_X_lag {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun _ => X) :=
  of_inductive_nonpos (B := fun _ => X) hbase hpos
    (fun n hsource r hr =>
      eval_X_nonpos_of_nonpos
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level positive unit-`X` lag induction.

This is the strict-degree version of recurrences such as
`P_{n+2}=A_n P_{n+1}+X P_n`, avoiding the local rewrite to
`(C 1 * X) * P_n`. -/
theorem prec_lw_positive_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_X_lag
    hbase hpos hnonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for sequence-level positive unit-`X` lag. -/
theorem isRealRooted_of_lw_positive_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_X_lag
    hbase hpos hnonneg hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for affine half-line lags `c_n X - a_n`. -/
theorem of_C_mul_X_sub_C_lag {P A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * X - C (a n)) :=
  of_inductive_nonpos (B := fun n => C (c n) * X - C (a n)) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_sub_C_nonpos_of_nonneg_of_nonneg_of_nonpos
        (hc n) (ha n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level affine half-line lag induction.

This packages the Family G6 shape
`P_{n+2}=A_n P_{n+1}+(c_n t-a_n)P_n`, where the current row has
nonnegative coefficients, hence all current roots are `<= 0`. -/
theorem prec_lw_C_mul_X_sub_C_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
    hbase hpos hnonneg hc ha hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the affine half-line lag induction. -/
theorem isRealRooted_of_lw_C_mul_X_sub_C_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
    hbase hpos hnonneg hc ha hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for positive shifted-affine lags from explicit root bounds. -/
theorem of_positive_affine_lag {P A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * (C (a n) + X)) :=
  { hbase := hbase
    hpos := hpos
    hB_nonpos := fun n r hr =>
      eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg (hc n)
        (hroot_upper n r hr)
    hrec := hrec
    hdeg_succ := hdeg_succ
    hno := hno }

/-- Build a shifted-affine state from nonnegative shifted-row coefficients. -/
theorem of_positive_affine_lag_shift_nonneg
    {P A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * (C (a n) + X)) :=
  of_inductive_nonpos
    (B := fun n => C (c n) * (C (a n) + X)) hbase hpos
    (fun n hsource _r hr =>
      eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg (hc n)
        (root_le_neg_of_realrooted_of_shift_nonneg_coeffs
          hsource (hshift_nonneg n) hr))
    hrec hdeg_succ hno

/-- Build a state for unit shifted-affine lags from explicit root bounds. -/
theorem of_C_add_X_lag {P A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (a n) + X) :=
  (of_positive_affine_lag (c := fun _ => 1) hbase hpos oneNonnegSeq
    hroot_upper (rr_lw_recurrence_seq hrec) hdeg_succ hno).of_B_congr
      (fun n => by simp)

/-- Build a unit shifted-affine state from nonnegative shifted-row coefficients. -/
theorem of_C_add_X_lag_shift_nonneg
    {P A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (a n) + X) :=
  (of_positive_affine_lag_shift_nonneg (c := fun _ => 1)
    hbase hpos oneNonnegSeq hshift_nonneg
    (rr_lw_recurrence_seq hrec) hdeg_succ hno).of_B_congr
      (fun n => by simp)

end LwNonposLagSequenceState

/-- Sequence-level positive affine lag induction.

This packages the shifted-root-location G7 shape
`P_{n+2}=A_nP_{n+1}+c_n(a_n+t)P_n`.  The sequence-specific hypothesis is the
upper root bound `r <= -a_n` for roots of the current row. -/
theorem prec_lw_positive_affine_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_affine_lag
    hbase hpos hc hroot_upper hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the positive affine lag sequence wrapper. -/
theorem isRealRooted_of_lw_positive_affine_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_affine_lag
    hbase hpos hc hroot_upper hrec hdeg_succ hno).isRealRooted

/-- Sequence-level positive affine lag induction with automated shifted root
bound.

The certificate `HasNonnegCoeffs ((P (n+1)).comp (X-C(a_n)))`, together with
real-rootedness already obtained from the induction prefix, implies that every
root of `P (n+1)` is at most `-a_n`. -/
theorem prec_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
    hbase hpos hc hshift_nonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the shifted-coefficient positive affine
lag wrapper. -/
theorem isRealRooted_of_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
    hbase hpos hc hshift_nonneg hrec hdeg_succ hno).isRealRooted

/-- Sequence-level unit affine lag `a_n+t`. -/
theorem prec_lw_C_add_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_add_X_lag
    hbase hpos hroot_upper hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for sequence-level unit affine lag `a_n+t`. -/
theorem isRealRooted_of_lw_C_add_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_add_X_lag
    hbase hpos hroot_upper hrec hdeg_succ hno).isRealRooted

/-- Sequence-level unit affine lag `a_n+t` with automated shifted root
bound. -/
theorem prec_lw_C_add_X_lag_sequence_of_shift_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_add_X_lag_shift_nonneg
    hbase hpos hshift_nonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for sequence-level unit affine lag `a_n+t` with
automated shifted root bound. -/
theorem isRealRooted_of_lw_C_add_X_lag_sequence_of_shift_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_add_X_lag_shift_nonneg
    hbase hpos hshift_nonneg hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for lags controlled on the inner window `[-1,0]`. -/
theorem of_inner_window_lag_nonneg {P A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r → r ≤ 0 →
      (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A B :=
  of_inductive_nonpos hbase hpos
    (fun n hsource r hr =>
      hB_nonpos n r hr (hroot_lower n r hr)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

/-- Build a state for the inner-window lag `X * (1+X)`. -/
theorem of_X_mul_one_add_X_lag_nonneg {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun _ => X * (1 + X)) :=
  of_inner_window_lag_nonneg
    (B := fun _ => X * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi => eval_X_mul_one_add_X_nonpos_of_mem_Icc hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the inner-window lag `c_n X * (1+X)`. -/
theorem of_C_mul_X_mul_one_add_X_lag_nonneg
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * X * (1 + X)) :=
  of_inner_window_lag_nonneg
    (B := fun n => C (c n) * X * (1 + X)) hbase hpos hnonneg
    hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc (hc n) hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the inner-window lag `X * (1-X) * (1+X)`. -/
theorem of_X_mul_one_sub_X_mul_one_add_X_lag_nonneg {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun _ => X * (1 - X) * (1 + X)) :=
  of_inner_window_lag_nonneg
    (B := fun _ => X * (1 - X) * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi =>
      eval_X_mul_one_sub_X_mul_one_add_X_nonpos_of_mem_Icc hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the inner-window lag `c_n X * (1-X) * (1+X)`. -/
theorem of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (1 - X) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => C (c n) * X * (1 - X) * (1 + X)) :=
  of_inner_window_lag_nonneg
    (B := fun n => C (c n) * X * (1 - X) * (1 + X)) hbase hpos
    hnonneg hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_mul_one_sub_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
        (hc n) hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the expanded inner-window lag `X - X^3`. -/
theorem of_X_sub_X_pow_three_lag_nonneg {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X - X ^ 3) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun _ => X - X ^ 3) :=
  of_inner_window_lag_nonneg
    (B := fun _ => X - X ^ 3) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi => eval_X_sub_X_pow_three_nonpos_of_mem_Icc hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the expanded inner-window lag `c_n * (X - X^3)`. -/
theorem of_C_mul_X_sub_X_pow_three_lag_nonneg
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * (X - X ^ 3)) :=
  of_inner_window_lag_nonneg
    (B := fun n => C (c n) * (X - X ^ 3)) hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_sub_X_pow_three_nonpos_of_nonneg_of_mem_Icc (hc n) hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level Liu--Wang induction for lags controlled on the inner
window `[-1, 0]`.

The upper root bound `r <= 0` is derived from real-rootedness and nonnegative
coefficients of the current row.  The lower bound `-1 <= r` and the lag sign
certificate on the window are supplied by the sequence-specific proof. -/
theorem prec_lw_inner_window_lag_sequence_of_nonneg_coeffs {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r → r ≤ 0 →
      (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_inner_window_lag_nonneg
    hbase hpos hnonneg hroot_lower hB_nonpos hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the inner-window Liu--Wang induction. -/
theorem isRealRooted_of_lw_inner_window_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r → r ≤ 0 →
      (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_inner_window_lag_nonneg
    hbase hpos hnonneg hroot_lower hB_nonpos hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `X(1+X)` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `X(1+X)` inner-window lag. -/
theorem isRealRooted_of_lw_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `c_n X(1+X)` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `c_n X(1+X)` inner-window lag. -/
theorem isRealRooted_of_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `X(1-X)(1+X)` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `X(1-X)(1+X)` inner-window lag. -/
theorem isRealRooted_of_lw_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `c_n X(1-X)(1+X)` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (1 - X) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `c_n X(1-X)(1+X)` inner-window lag. -/
theorem isRealRooted_of_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (1 - X) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `X-X^3` lag controlled on the inner root window `[-1,0]`. -/
theorem prec_lw_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X - X ^ 3) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_X_sub_X_pow_three_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `X-X^3` inner-window lag. -/
theorem isRealRooted_of_lw_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X - X ^ 3) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_X_sub_X_pow_three_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `c_n (X-X^3)` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `c_n (X-X^3)` inner-window lag. -/
theorem isRealRooted_of_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for lags controlled on the explicit window `[-1,-1/2]`. -/
theorem of_interval_lag {P A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r →
      r ≤ -(1 / 2 : ℝ) → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A B :=
  { hbase := hbase
    hpos := hpos
    hB_nonpos := fun n r hr =>
      hB_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr)
    hrec := hrec
    hdeg_succ := hdeg_succ
    hno := hno }

/-- Build a state for the explicit-window lag `(1+X) * (1+2X)`. -/
theorem of_one_add_X_mul_one_add_two_mul_X_lag {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + ((1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun _ => (1 + X) * (1 + C (2 : ℝ) * X)) :=
  of_interval_lag
    (B := fun _ => (1 + X) * (1 + C (2 : ℝ) * X)) hbase hpos
    hroot_lower hroot_upper
    (fun _ _ _ hlo hhi =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the explicit-window lag `c_n(1+X) * (1+2X)`. -/
theorem of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => C (c n) * (1 + X) * (1 + C (2 : ℝ) * X)) :=
  of_interval_lag
    (B := fun n => C (c n) * (1 + X) * (1 + C (2 : ℝ) * X))
    hbase hpos hroot_lower hroot_upper
    (fun n _ _ hlo hhi =>
      eval_C_mul_one_add_X_mul_one_add_two_mul_X_nonpos_of_nonneg_of_mem_interval
        (hc n) hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level Liu--Wang induction for lags controlled on an explicit
root interval.  This is for windows narrower than the half-line, where both
bounds have to be supplied by the sequence-specific proof. -/
theorem prec_lw_interval_lag_sequence {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r →
      r ≤ -(1 / 2 : ℝ) → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_interval_lag
    hbase hpos hroot_lower hroot_upper hB_nonpos hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the explicit-interval Liu--Wang induction. -/
theorem isRealRooted_of_lw_interval_lag_sequence
    {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r →
      r ≤ -(1 / 2 : ℝ) → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_interval_lag
    hbase hpos hroot_lower hroot_upper hB_nonpos hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `(1+X)(1+2X)` lag on the explicit window
`[-1,-1/2]`. -/
theorem prec_lw_one_add_X_mul_one_add_two_mul_X_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + ((1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_one_add_X_mul_one_add_two_mul_X_lag
    hbase hpos hroot_lower hroot_upper hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `(1+X)(1+2X)` interval lag. -/
theorem isRealRooted_of_lw_one_add_X_mul_one_add_two_mul_X_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + ((1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_one_add_X_mul_one_add_two_mul_X_lag
    hbase hpos hroot_lower hroot_upper hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `c_n(1+X)(1+2X)` lag on the explicit window
`[-1,-1/2]`. -/
theorem prec_lw_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
    hbase hpos hc hroot_lower hroot_upper hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `c_n(1+X)(1+2X)` interval lag. -/
theorem isRealRooted_of_lw_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
    hbase hpos hc hroot_lower hroot_upper hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for inner-window negative affine lags. -/
theorem of_neg_C_mul_affine_inner_lag_nonneg
    {P A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hba : ∀ n : Nat, b n ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => -(C (c n)) * (C (a n) + C (b n) * X)) :=
  of_inner_window_lag_nonneg
    (B := fun n => -(C (c n)) * (C (a n) + C (b n) * X))
    hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo _ =>
      eval_neg_C_mul_C_add_C_mul_X_nonpos_of_nonneg_of_nonneg_of_le_of_ge_neg_one
        (hc n) (hb n) (hba n) hlo)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the inner-window lag `-c_n(1+X)`. -/
theorem of_neg_C_mul_one_add_X_lag_nonneg
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => -(C (c n)) * (1 + X)) :=
  of_inner_window_lag_nonneg
    (B := fun n => -(C (c n)) * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo _ =>
      eval_neg_C_mul_one_add_X_nonpos_of_nonneg_of_ge_neg_one (hc n) hlo)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a normalized `-c_n(1+X)` state from a scalar-denominator recurrence. -/
theorem of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
    {P A : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = -c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => -(C (c n)) * (1 + X)) := by
  refine
    of_neg_C_mul_one_add_X_lag_nonneg
      hbase hpos hnonneg hc hroot_lower ?_ hdeg_succ hno
  intro n
  have hraw' :
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + C (b n) * ((1 + X) * P n) := by
    simpa [mul_assoc] using hraw n
  have hnorm :
      P (n + 2) =
        A n * P (n + 1) + C (-c n) * ((1 + X) * P n) :=
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) hraw'
  calc
    P (n + 2) =
        A n * P (n + 1) + C (-c n) * ((1 + X) * P n) := hnorm
    _ = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n := by
      simp [Polynomial.C_neg, mul_assoc, mul_comm]

/-- Build a state for the tighter-window lag `-c_n(1+2X)`. -/
theorem of_neg_C_mul_one_add_two_mul_X_lag_nonneg
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => -(C (c n)) * (1 + C (2 : ℝ) * X)) :=
  of_inner_window_lag_nonneg
    (B := fun n => -(C (c n)) * (1 + C (2 : ℝ) * X))
    hbase hpos hnonneg
    (fun n r hr => by
      have hhalf := hroot_lower n r hr
      linarith)
    (fun n r hr _ _ =>
      eval_neg_C_mul_one_add_two_mul_X_nonpos_of_nonneg_of_ge_neg_half
        (hc n) (hroot_lower n r hr))
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level `-c_n(a_n+b_n X)` lag controlled on the inner root window
`[-1,0]`, in the common monotone-affine case `0 <= b_n <= a_n`. -/
theorem prec_lw_neg_C_mul_affine_inner_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hba : ∀ n : Nat, b n ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_neg_C_mul_affine_inner_lag_nonneg
    hbase hpos hnonneg hc hb hba hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for inner-window negative affine lags. -/
theorem isRealRooted_of_lw_neg_C_mul_affine_inner_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hba : ∀ n : Nat, b n ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_neg_C_mul_affine_inner_lag_nonneg
    hbase hpos hnonneg hc hb hba hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `-c_n(1+X)` lag controlled on `[-1,0]`. -/
theorem prec_lw_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `-c_n(1+X)` inner-window lag. -/
theorem isRealRooted_of_lw_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Denominator-fused `-c_n(1+X)` inner-window Liu--Wang induction.

The raw recurrence has a nonzero scalar denominator `d_n`, a current-row
summand already multiplied by `d_n`, and a raw affine lag coefficient
`b_n(1+X)`.  The side condition `d_n⁻¹ b_n = -c_n` gives the normalized
negative coefficient. -/
theorem prec_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = -c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
    (A := A) hbase hpos hnonneg hc hroot_lower hden hcoeff hraw
    hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the denominator-fused `-c_n(1+X)` lag. -/
theorem isRealRooted_of_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = -c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
    (A := A) hbase hpos hnonneg hc hroot_lower hden hcoeff hraw
    hdeg_succ hno).isRealRooted

/-- Sequence-level `-c_n(1+2X)` lag controlled on the tighter inner window
`[-1/2,0]`. -/
theorem prec_lw_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `-c_n(1+2X)` tighter-window lag. -/
theorem isRealRooted_of_lw_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for the inner-window lag `X^2 - 1`. -/
theorem of_X_sq_sub_one_lag_nonneg {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X ^ 2 - 1) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun _ => X ^ 2 - 1) :=
  of_inner_window_lag_nonneg
    (B := fun _ => X ^ 2 - 1) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi => eval_X_sq_sub_one_nonpos_of_mem_Icc hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

/-- Build a state for the inner-window lag `c_n(X^2 - 1)`. -/
theorem of_C_mul_X_sq_sub_one_lag_nonneg
    {P A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * (X ^ 2 - 1)) :=
  of_inner_window_lag_nonneg
    (B := fun n => C (c n) * (X ^ 2 - 1)) hbase hpos hnonneg
    hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_sq_sub_one_nonpos_of_nonneg_of_mem_Icc (hc n) hlo hhi)
    (rr_lw_recurrence_seq hrec) hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level `X^2-1` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X ^ 2 - 1) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_X_sq_sub_one_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `X^2-1` inner-window lag. -/
theorem isRealRooted_of_lw_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X ^ 2 - 1) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_X_sq_sub_one_lag_nonneg
    hbase hpos hnonneg hroot_lower hrec hdeg_succ hno).isRealRooted

/-- Sequence-level `c_n(X^2-1)` lag controlled on the inner root window
`[-1,0]`. -/
theorem prec_lw_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `c_n(X^2-1)` inner-window lag. -/
theorem isRealRooted_of_lw_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for positive lags of the form `X * Q_n`. -/
theorem of_positive_X_mul_lag {P A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => X * Q n) :=
  of_inductive_nonpos (B := fun n => X * Q n) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr)
        (hQ_nonneg n r hr))
    hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level `X Q_n` positive-lag Liu--Wang induction.

The current-row root bound `r <= 0` is derived internally from real-rootedness
and nonnegative coefficients.  The sequence-specific certificate is only the
remaining factor inequality `0 <= Q_n(r)` at roots of the current row. -/
theorem prec_lw_positive_X_mul_lag_sequence {P : Nat → ℝ[X]}
    {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_X_mul_lag
    hbase hpos hnonneg hQ_nonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for sequence-level `X Q_n` positive-lag
Liu--Wang induction. -/
theorem isRealRooted_of_lw_positive_X_mul_lag_sequence {P : Nat → ℝ[X]}
    {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_X_mul_lag
    hbase hpos hnonneg hQ_nonneg hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for positive lags of the form `c_n X Q_n`. -/
theorem of_positive_C_mul_X_mul_lag {P A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun n => C (c n) * X * Q n) :=
  of_inductive_nonpos (B := fun n => C (c n) * X * Q n) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        (hc n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr)
        (hQ_nonneg n r hr))
    hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level `c_n X Q_n` positive-lag Liu--Wang induction. -/
theorem prec_lw_positive_C_mul_X_mul_lag_sequence {P : Nat → ℝ[X]}
    {A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
    hbase hpos hnonneg hc hQ_nonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for sequence-level `c_n X Q_n` positive-lag
Liu--Wang induction. -/
theorem isRealRooted_of_lw_positive_C_mul_X_mul_lag_sequence {P : Nat → ℝ[X]}
    {A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
    hbase hpos hnonneg hc hQ_nonneg hrec hdeg_succ hno).isRealRooted

/-- Family E sequence wrapper for strict-degree `t R_n(t)` lag recurrences.

This is the high-yield `P_{n+2}=A_n P_{n+1}+t R_n(t) P_n` surface.  The
half-line root bound is derived from nonnegative coefficients; the
sequence-specific input is the focused certificate `0 <= R_n(r)` at roots of
the current row. -/
theorem prec_lw_tR_lag_sequence {P : Nat → ℝ[X]}
    {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_X_mul_lag
    hbase hpos hnonneg hR_nonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for strict-degree `t R_n(t)` lag recurrences. -/
theorem isRealRooted_of_lw_tR_lag_sequence {P : Nat → ℝ[X]}
    {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_X_mul_lag
    hbase hpos hnonneg hR_nonneg hrec hdeg_succ hno).isRealRooted

/-- Scalar Family E sequence wrapper for strict-degree
`c_n t R_n(t)` lag recurrences. -/
theorem prec_lw_c_tR_lag_sequence {P : Nat → ℝ[X]}
    {A R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hR_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
    hbase hpos hnonneg hc hR_nonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for strict-degree `c_n t R_n(t)` lag
recurrences. -/
theorem isRealRooted_of_lw_c_tR_lag_sequence {P : Nat → ℝ[X]}
    {A R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hR_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
    hbase hpos hnonneg hc hR_nonneg hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for the literal `X * (1 - X)` lag. -/
theorem of_X_mul_one_sub_X_lag {P A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A (fun _ => X * (1 - X)) :=
  of_inductive_nonpos (B := fun _ => X * (1 - X)) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_one_sub_X_nonpos_of_nonpos
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

/-- Build a state for the parameterized `X * (a_n - b_n X)` lag. -/
theorem of_X_mul_C_sub_C_mul_X_lag {P A : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => X * (C (a n) - C (b n) * X)) :=
  of_inductive_nonpos
    (B := fun n => X * (C (a n) - C (b n) * X)) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_C_sub_C_mul_X_nonpos_of_nonneg_of_nonneg_of_nonpos
        (ha n) (hb n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

/-- Build a state for the parameterized `c_n X * (a_n - b_n X)` lag. -/
theorem of_C_mul_X_mul_C_sub_C_mul_X_lag
    {P A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P A
      (fun n => C (c n) * X * (C (a n) - C (b n) * X)) :=
  of_inductive_nonpos
    (B := fun n => C (c n) * X * (C (a n) - C (b n) * X)) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_mul_C_sub_C_mul_X_nonpos
        (hc n) (ha n) (hb n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence wrapper for strict-degree Family E `t(1-t)` lag recurrences. -/
theorem prec_lw_X_mul_one_sub_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_X_mul_one_sub_X_lag
    hbase hpos hnonneg hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for strict-degree Family E `t(1-t)` lag
recurrences. -/
theorem isRealRooted_of_lw_X_mul_one_sub_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_X_mul_one_sub_X_lag
    hbase hpos hnonneg hrec hdeg_succ hno).isRealRooted

/-- Sequence wrapper for strict-degree Family E `t(a_n-b_n t)` lag
recurrences with nonnegative parameters. -/
theorem prec_lw_X_mul_C_sub_C_mul_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
    hbase hpos hnonneg ha hb hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for strict-degree Family E `t(a_n-b_n t)` lag
recurrences. -/
theorem isRealRooted_of_lw_X_mul_C_sub_C_mul_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
    hbase hpos hnonneg ha hb hrec hdeg_succ hno).isRealRooted

/-- Sequence wrapper for strict-degree Family E `c_n t(a_n-b_n t)` lag
recurrences with nonnegative parameters. -/
theorem prec_lw_C_mul_X_mul_C_sub_C_mul_X_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
    hbase hpos hnonneg hc ha hb hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for strict-degree Family E
`c_n t(a_n-b_n t)` lag recurrences. -/
theorem isRealRooted_of_lw_C_mul_X_mul_C_sub_C_mul_X_lag_sequence
    {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
    hbase hpos hnonneg hc ha hb hrec hdeg_succ hno).isRealRooted

namespace LwNonposLagSequenceState

/-- Build a state for positive `t`-lag with current coefficient `a_n X`. -/
theorem of_current_CX_positive_t_lag {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P (fun n => C (a n) * X)
      (fun n => C (c n) * X) :=
  of_positive_t_lag (A := fun n => C (a n) * X)
    hbase hpos hnonneg hc hrec hdeg_succ hno

/-- Build a state for positive `t`-lag with current coefficient `X`. -/
theorem of_current_X_positive_t_lag {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P (fun _ => X) (fun n => C (c n) * X) :=
  of_positive_t_lag (A := fun _ => X)
    hbase hpos hnonneg hc hrec hdeg_succ hno

/-- Build a state for positive `t`-lag with current coefficient `1 + X`. -/
theorem of_current_one_add_X_positive_t_lag {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    LwNonposLagSequenceState P (fun _ => (1 + X : ℝ[X]))
      (fun n => C (c n) * X) :=
  of_positive_t_lag (A := fun _ => (1 + X : ℝ[X]))
    hbase hpos hnonneg hc hrec hdeg_succ hno

end LwNonposLagSequenceState

/-- Sequence-level positive `t`-lag induction when the current-row coefficient
is also a scalar multiple of `X`.  This packages the scalar-current shapes
`t P_{n+1}+c_n t P_n` and `a_n t P_{n+1}+c_n t P_n`. -/
theorem prec_lw_current_CX_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_current_CX_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the scalar-`X` current positive `t`-lag
sequence wrapper. -/
theorem isRealRooted_of_lw_current_CX_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_current_CX_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).isRealRooted

/-- Sequence-level positive `t`-lag induction for the exact current factor
`X`.  This avoids normalizing unit-current generated recurrences to
`(C 1 * X) * P_{n+1}`. -/
theorem prec_lw_current_X_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_current_X_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the exact-`X` current positive `t`-lag
sequence wrapper. -/
theorem isRealRooted_of_lw_current_X_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_current_X_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).isRealRooted

/-- Sequence-level positive `t`-lag induction for current factor `1+X`. -/
theorem prec_lw_current_one_add_X_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  (LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).prec_sequence

/-- Real-rootedness corollary for the `1+X` current positive `t`-lag sequence
wrapper. -/
theorem isRealRooted_of_lw_current_one_add_X_positive_t_lag_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  (LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
    hbase hpos hnonneg hc hrec hdeg_succ hno).isRealRooted

namespace Tactic

syntax (name := rr_lw_coeff_nonneg) "rr_lw_coeff_nonneg" : tactic

macro_rules
  | `(tactic| rr_lw_coeff_nonneg) =>
      `(tactic| rr_side_nonneg)

syntax (name := rr_lw_coeff_nonneg_term) "rr_lw_coeff_nonneg_term" : term
syntax (name := rr_lw_coeff_nonneg_seq_term) "rr_lw_coeff_nonneg_seq_term" : term

macro_rules
  | `(rr_lw_coeff_nonneg_term) =>
      `(by rr_lw_coeff_nonneg)
  | `(rr_lw_coeff_nonneg_seq_term) =>
      `(by rr_side_nonneg_seq)

macro "rr_lw_active_nonneg_at " n:term : tactic =>
  `(tactic| rr_scalar_active_nonneg_at $n)

macro "rr_lw_active_nonneg_seq" : tactic =>
  `(tactic| intro n <;> rr_lw_active_nonneg_at n)

macro "rr_lw_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

macro "rr_lw_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

macro "rr_lw_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

syntax (name := rr_lw_refine_active_nonneg_seq)
  "rr_lw_refine_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_lw_refine_active_nonneg_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_lw_active_nonneg_seq)

syntax (name := rr_lw_exact_realrooted_active_nonneg_seq)
  "rr_lw_exact_realrooted_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_lw_exact_realrooted_active_nonneg_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_lw_active_nonneg_seq)

syntax (name := rr_lw_active_nonneg) "rr_lw_active_nonneg" : term
syntax (name := rr_lw_active_den_all_term) "rr_lw_active_den_all_term" : term
syntax (name := rr_lw_coeff_at_term) "rr_lw_coeff_at_term " term : term
syntax (name := rr_lw_coeff_all_term) "rr_lw_coeff_all_term" : term

macro_rules
  | `(rr_lw_active_nonneg) =>
      `(fun n => by rr_lw_active_nonneg_at n)
  | `(rr_lw_active_den_all_term) =>
      `(by rr_lw_active_den_all)
  | `(rr_lw_coeff_at_term $n:term) =>
      `(by rr_lw_coeff_at $n)
  | `(rr_lw_coeff_all_term) =>
      `(by rr_lw_coeff_all)

syntax (name := rr_lw_raw_recurrence_seq) "rr_lw_raw_recurrence_seq " term : term

macro_rules
  | `(rr_lw_raw_recurrence_seq $hraw:term) =>
      `(fun n => by
        simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using $hraw n)

macro "rr_lw_quadratic_discriminant_at " n:term : tactic =>
  `(tactic|
    solve
      | rr_lw_coeff_nonneg
      | nlinarith [sq_nonneg ($n : ℝ),
          sq_nonneg (($n : ℝ) + 1),
          sq_nonneg (($n : ℝ) + 2),
          show 0 ≤ ($n : ℝ) by positivity])

macro "rr_lw_negative_quadratic_side_at " n:term : tactic =>
  `(tactic|
    first
      | rr_lw_active_nonneg_at $n
      | rr_lw_quadratic_discriminant_at $n)

syntax (name := rr_lw_quadratic_discriminant) "rr_lw_quadratic_discriminant" : term
syntax (name := rr_lw_negative_quadratic_side) "rr_lw_negative_quadratic_side" : term

macro_rules
  | `(rr_lw_quadratic_discriminant) =>
      `(fun n => by rr_lw_quadratic_discriminant_at n)
  | `(rr_lw_negative_quadratic_side) =>
      `(fun n => by rr_lw_negative_quadratic_side_at n)

syntax (name := rr_liu_wang)
  "rr_liu_wang" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_named)
  "rr_liu_wang" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_nonpos" ":=" term :
  tactic

syntax (name := rr_liu_wang_strict)
  "rr_liu_wang_strict" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_strict_named)
  "rr_liu_wang_strict" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_liu_wang_strict_same)
  "rr_liu_wang_strict_same" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_strict_same_named)
  "rr_liu_wang_strict_same" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_liu_wang_strict_succ)
  "rr_liu_wang_strict_succ" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_strict_succ_named)
  "rr_liu_wang_strict_succ" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_liu_wang_two_named)
  "rr_liu_wang_two" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_nonpos" ":=" term :
  tactic

syntax (name := rr_liu_wang_two_strict_named)
  "rr_liu_wang_two_strict" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_liu_wang_two_strict_same_named)
  "rr_liu_wang_two_strict_same" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_liu_wang_two_strict_succ_named)
  "rr_liu_wang_two_strict_succ" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_liu_wang_two_strict_branch_named)
  "rr_liu_wang_two_strict_branch" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_branch" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_named)
  "rr_lw_positive_t" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_auto_named)
  "rr_lw_positive_t_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_named)
  "rr_lw_positive_X" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_unit_alias_named)
  "rr_lw_positive_X" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_unit_named)
  "rr_lw_positive_X_unit" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_nonneg_named)
  "rr_lw_positive_t_nonneg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_nonneg_auto_named)
  "rr_lw_positive_t_nonneg_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_mul_named)
  "rr_lw_positive_X_mul" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_named)
  "rr_lw_positive_C_mul_X_mul" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_mul_nonneg_named)
  "rr_lw_positive_X_mul_nonneg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_nonneg_named)
  "rr_lw_positive_C_mul_X_mul_nonneg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_nonneg_auto_named)
  "rr_lw_positive_C_mul_X_mul_nonneg_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_named)
  "rr_lw_negative_square" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_auto_named)
  "rr_lw_negative_square_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_monic_quadratic_named)
  "rr_lw_negative_monic_quadratic" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "discriminant" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_monic_quadratic_auto_named)
  "rr_lw_negative_monic_quadratic_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_named)
  "rr_lw_negative_quadratic" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_auto_named)
  "rr_lw_negative_quadratic_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_named)
  "rr_lw_negative_const" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_auto_named)
  "rr_lw_negative_const_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_named)
  "rr_lw_negative_const_C_neg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_auto_named)
  "rr_lw_negative_const_C_neg_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_step_named)
  "rr_lw_nonpos_lag_step" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "lag_nonpos" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_named)
  "rr_lw_nonpos_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_realrooted_named)
  "rr_lw_nonpos_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_nonzero_named)
  "rr_lw_nonpos_lag_sequence_nonzero" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_splits_named)
  "rr_lw_nonpos_lag_sequence_splits" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_interlaces_named)
  "rr_lw_nonpos_lag_sequence_interlaces" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_inductive_nonpos_named)
  "rr_lw_nonpos_lag_sequence_inductive_nonpos" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_inductive_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_inductive_nonpos_realrooted_named)
  "rr_lw_nonpos_lag_sequence_inductive_nonpos_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_inductive_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_inductive_nonpos_nonzero_named)
  "rr_lw_nonpos_lag_sequence_inductive_nonpos_nonzero" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_inductive_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_inductive_nonpos_splits_named)
  "rr_lw_nonpos_lag_sequence_inductive_nonpos_splits" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_inductive_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_inductive_nonpos_interlaces_named)
  "rr_lw_nonpos_lag_sequence_inductive_nonpos_interlaces" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_inductive_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_state_named)
  "rr_lw_nonpos_lag_state" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_state_realrooted_named)
  "rr_lw_nonpos_lag_state_realrooted" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_state_nonzero_named)
  "rr_lw_nonpos_lag_state_nonzero" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_state_splits_named)
  "rr_lw_nonpos_lag_state_splits" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_state_interlaces_named)
  "rr_lw_nonpos_lag_state_interlaces" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_sequence_state_named)
  "rr_lw_strict_branch_sequence_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_branch" ":=" term ","
    "interlacer" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_sequence_named)
  "rr_lw_strict_branch_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_branch" ":=" term ","
    "interlacer" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_sequence_realrooted_named)
  "rr_lw_strict_branch_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_branch" ":=" term ","
    "interlacer" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_sequence_nonzero_named)
  "rr_lw_strict_branch_sequence_nonzero" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_branch" ":=" term ","
    "interlacer" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_sequence_splits_named)
  "rr_lw_strict_branch_sequence_splits" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_branch" ":=" term ","
    "interlacer" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_sequence_interlaces_named)
  "rr_lw_strict_branch_sequence_interlaces" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_branch" ":=" term ","
    "interlacer" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_state_named)
  "rr_lw_strict_branch_state" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_state_realrooted_named)
  "rr_lw_strict_branch_state_realrooted" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_state_nonzero_named)
  "rr_lw_strict_branch_state_nonzero" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_state_splits_named)
  "rr_lw_strict_branch_state_splits" " using "
    "state" ":=" term :
  tactic

syntax (name := rr_lw_strict_branch_state_interlaces_named)
  "rr_lw_strict_branch_state_interlaces" " using "
    "state" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_nonpos_lag_state_nonzero using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.ne_zero_sequence $hstate)
  | `(tactic|
      rr_lw_nonpos_lag_state_splits using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.splits_sequence $hstate)

macro_rules
  | `(tactic|
      rr_lw_nonpos_lag_sequence_nonzero using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).ne_zero_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_splits using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).splits_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_interlaces using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).interlaces_sequence)

macro_rules
  | `(tactic|
      rr_lw_nonpos_lag_sequence_inductive_nonpos using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_inductive_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_inductive_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_inductive_nonpos_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_inductive_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_inductive_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_nonpos_lag_sequence_inductive_nonpos_nonzero using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_inductive_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_inductive_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).ne_zero_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_inductive_nonpos_splits using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_inductive_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_inductive_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).splits_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_inductive_nonpos_interlaces using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_inductive_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_inductive_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).interlaces_sequence)

macro_rules
  | `(tactic|
      rr_lw_strict_branch_sequence_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_branch := $hdegree:term,
        interlacer := $hinter:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        exact RealRooted.LwStrictBranchSequenceState.of_branch
          $hbase $hpos $hrec $hdegree $hinter $hno $hb_neg)
  | `(tactic|
      rr_lw_strict_branch_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_branch := $hdegree:term,
        interlacer := $hinter:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        exact
          (RealRooted.LwStrictBranchSequenceState.of_branch
            $hbase $hpos $hrec $hdegree $hinter $hno $hb_neg).prec_sequence)
  | `(tactic|
      rr_lw_strict_branch_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_branch := $hdegree:term,
        interlacer := $hinter:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwStrictBranchSequenceState.of_branch
            $hbase $hpos $hrec $hdegree $hinter $hno $hb_neg).isRealRooted))
  | `(tactic|
      rr_lw_strict_branch_sequence_nonzero using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_branch := $hdegree:term,
        interlacer := $hinter:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        exact
          (RealRooted.LwStrictBranchSequenceState.of_branch
            $hbase $hpos $hrec $hdegree $hinter $hno
            $hb_neg).ne_zero_sequence)
  | `(tactic|
      rr_lw_strict_branch_sequence_splits using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_branch := $hdegree:term,
        interlacer := $hinter:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        exact
          (RealRooted.LwStrictBranchSequenceState.of_branch
            $hbase $hpos $hrec $hdegree $hinter $hno
            $hb_neg).splits_sequence)
  | `(tactic|
      rr_lw_strict_branch_sequence_interlaces using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_branch := $hdegree:term,
        interlacer := $hinter:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        exact
          (RealRooted.LwStrictBranchSequenceState.of_branch
            $hbase $hpos $hrec $hdegree $hinter $hno
            $hb_neg).interlaces_sequence)
  | `(tactic|
      rr_lw_strict_branch_state using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwStrictBranchSequenceState.prec_sequence $hstate)
  | `(tactic|
      rr_lw_strict_branch_state_realrooted using
        state := $hstate:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LwStrictBranchSequenceState.isRealRooted $hstate))
  | `(tactic|
      rr_lw_strict_branch_state_nonzero using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwStrictBranchSequenceState.ne_zero_sequence $hstate)
  | `(tactic|
      rr_lw_strict_branch_state_splits using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwStrictBranchSequenceState.splits_sequence $hstate)
  | `(tactic|
      rr_lw_strict_branch_state_interlaces using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwStrictBranchSequenceState.interlaces_sequence
          $hstate)

syntax (name := rr_lw_global_nonpos_state_auto_named)
  "rr_lw_global_nonpos_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_state_den_auto_named)
  "rr_lw_global_nonpos_state_den_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_auto_named)
  "rr_lw_global_nonpos_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_realrooted_auto_named)
  "rr_lw_global_nonpos_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_nonzero_auto_named)
  "rr_lw_global_nonpos_sequence_nonzero_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_interlaces_auto_named)
  "rr_lw_global_nonpos_sequence_interlaces_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_den_auto_named)
  "rr_lw_global_nonpos_sequence_den_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_den_realrooted_auto_named)
  "rr_lw_global_nonpos_sequence_den_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_den_nonzero_auto_named)
  "rr_lw_global_nonpos_sequence_den_nonzero_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_global_nonpos_sequence_den_interlaces_auto_named)
  "rr_lw_global_nonpos_sequence_den_interlaces_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_global_nonpos_sequence_nonzero_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hrec $hdeg_succ $hno).ne_zero_sequence)
  | `(tactic|
      rr_lw_global_nonpos_sequence_interlaces_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hrec $hdeg_succ $hno).interlaces_sequence)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_nonzero_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_nonzero_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_nonzero_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hden $hraw $hdeg_succ $hno).ne_zero_sequence)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_interlaces_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_interlaces_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_interlaces_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hden $hraw $hdeg_succ $hno).interlaces_sequence)

syntax (name := rr_lw_nonpos_lag_sequence_den_named)
  "rr_lw_nonpos_lag_sequence_den" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_den_realrooted_named)
  "rr_lw_nonpos_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_den_nonzero_named)
  "rr_lw_nonpos_lag_sequence_den_nonzero" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_den_splits_named)
  "rr_lw_nonpos_lag_sequence_den_splits" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_nonpos_lag_sequence_den_interlaces_named)
  "rr_lw_nonpos_lag_sequence_den_interlaces" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den_nonzero using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
            $hbase $hpos $hB $hden $hraw $hdeg_succ $hno).ne_zero_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den_splits using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
            $hbase $hpos $hB $hden $hraw $hdeg_succ $hno).splits_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den_interlaces using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
            $hbase $hpos $hB $hden $hraw $hdeg_succ $hno).interlaces_sequence)

syntax (name := rr_lw_negative_const_state_named)
  "rr_lw_negative_const_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_state_auto_named)
  "rr_lw_negative_const_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_state_named)
  "rr_lw_negative_const_C_neg_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_state_auto_named)
  "rr_lw_negative_const_C_neg_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_sequence_named)
  "rr_lw_negative_const_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_sequence_auto_named)
  "rr_lw_negative_const_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_sequence_realrooted_named)
  "rr_lw_negative_const_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_sequence_realrooted_auto_named)
  "rr_lw_negative_const_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_sequence_named)
  "rr_lw_negative_const_C_neg_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_sequence_auto_named)
  "rr_lw_negative_const_C_neg_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_sequence_realrooted_named)
  "rr_lw_negative_const_C_neg_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_const_C_neg_sequence_realrooted_auto_named)
  "rr_lw_negative_const_C_neg_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_named)
  "rr_lw_negative_square_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_auto_named)
  "rr_lw_negative_square_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_unit_named)
  "rr_lw_negative_square_state_unit" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_named)
  "rr_lw_negative_square_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_auto_named)
  "rr_lw_negative_square_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_realrooted_named)
  "rr_lw_negative_square_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_realrooted_auto_named)
  "rr_lw_negative_square_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_unit_named)
  "rr_lw_negative_square_sequence_unit" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_realrooted_unit_named)
  "rr_lw_negative_square_sequence_realrooted_unit" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_named)
  "rr_lw_negative_square_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_split_named)
  "rr_lw_negative_square_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_split_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_named)
  "rr_lw_negative_square_sequence_den_coeff_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_active_named)
  "rr_lw_negative_square_sequence_den_coeff_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_split_named)
  "rr_lw_negative_square_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_split_active_named)
  "rr_lw_negative_square_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_split_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_split_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_active_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split_active_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_den_coeff_named)
  "rr_lw_negative_square_state_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_den_coeff_split_named)
  "rr_lw_negative_square_state_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_den_coeff_auto_named)
  "rr_lw_negative_square_state_den_coeff_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_den_coeff_auto_active_named)
  "rr_lw_negative_square_state_den_coeff_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_den_coeff_auto_split_named)
  "rr_lw_negative_square_state_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_square_state_den_coeff_auto_split_active_named)
  "rr_lw_negative_square_state_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_monic_quadratic_sequence_named)
  "rr_lw_negative_monic_quadratic_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_monic_quadratic_sequence_realrooted_named)
  "rr_lw_negative_monic_quadratic_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_monic_quadratic_sequence_auto_named)
  "rr_lw_negative_monic_quadratic_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_monic_quadratic_sequence_realrooted_auto_named)
  "rr_lw_negative_monic_quadratic_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_named)
  "rr_lw_negative_quadratic_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_realrooted_named)
  "rr_lw_negative_quadratic_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_auto_named)
  "rr_lw_negative_quadratic_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_realrooted_auto_named)
  "rr_lw_negative_quadratic_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_state_named)
  "rr_lw_negative_quadratic_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_state_auto_named)
  "rr_lw_negative_quadratic_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_auto_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_auto_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_state_den_coeff_split_named)
  "rr_lw_negative_quadratic_state_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_state_den_coeff_auto_split_named)
  "rr_lw_negative_quadratic_state_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_state_den_coeff_auto_split_scalar_named)
  "rr_lw_negative_quadratic_state_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_named)
  "rr_lw_positive_t_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_auto_named)
  "rr_lw_positive_t_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_realrooted_named)
  "rr_lw_positive_t_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_realrooted_auto_named)
  "rr_lw_positive_t_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_state_named)
  "rr_lw_positive_t_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_state_auto_named)
  "rr_lw_positive_t_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_lag_step_named)
  "rr_lw_positive_t_lag_step" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "source_nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_lag_sequence_named)
  "rr_lw_positive_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_lag_sequence_realrooted_named)
  "rr_lw_positive_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_lag_state_named)
  "rr_lw_positive_X_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_state_named)
  "rr_lw_C_mul_X_sub_C_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_state_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_named)
  "rr_lw_positive_affine_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_auto_named)
  "rr_lw_positive_affine_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_named)
  "rr_lw_positive_affine_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_auto_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_shift_nonneg_named)
  "rr_lw_positive_affine_lag_sequence_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_sequence_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_state_named)
  "rr_lw_positive_affine_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_state_auto_named)
  "rr_lw_positive_affine_lag_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_state_shift_nonneg_named)
  "rr_lw_positive_affine_lag_state_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_state_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_state_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_named)
  "rr_lw_C_add_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_realrooted_named)
  "rr_lw_C_add_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_shift_nonneg_named)
  "rr_lw_C_add_X_lag_sequence_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg_named)
  "rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_state_named)
  "rr_lw_C_add_X_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_state_shift_nonneg_named)
  "rr_lw_C_add_X_lag_state_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_sub_X_pow_three_lag_sequence_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_add_X_lag_state_nonneg_named)
  "rr_lw_X_one_add_X_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_sub_X_one_add_X_lag_state_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_sub_X_pow_three_lag_state_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_state_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_state_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_state_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_state_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_state_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_state_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_state_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_state_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_state_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_inner_window_lag_sequence_named)
  "rr_lw_inner_window_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("xOneAddX" <|> "xOneSubXOneAddX" <|> "xSubXPowThree" <|>
        "cMulXOneAddX" <|> "cMulXOneSubXOneAddX" <|> "cMulXSubXPowThree" <|>
        "cMulXSqSubOne") :
  tactic

syntax (name := rr_lw_inner_window_lag_sequence_realrooted_named)
  "rr_lw_inner_window_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("xOneAddX" <|> "xOneSubXOneAddX" <|> "xSubXPowThree" <|>
        "cMulXOneAddX" <|> "cMulXOneSubXOneAddX" <|> "cMulXSubXPowThree" <|>
        "cMulXSqSubOne") :
  tactic

syntax (name := rr_lw_interval_lag_sequence_named)
  "rr_lw_interval_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("oneAddXOneAddTwoX" <|> "cMulOneAddXOneAddTwoX") :
  tactic

syntax (name := rr_lw_interval_lag_sequence_realrooted_named)
  "rr_lw_interval_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("oneAddXOneAddTwoX" <|> "cMulOneAddXOneAddTwoX") :
  tactic

syntax (name := rr_lw_one_add_X_one_add_two_X_lag_sequence_interval_named)
  "rr_lw_one_add_X_one_add_two_X_lag_sequence_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_named)
  "rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_one_add_X_one_add_two_X_lag_state_interval_named)
  "rr_lw_one_add_X_one_add_two_X_lag_state_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_state_interval_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_state_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax
  (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_state_interval_auto_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_state_interval_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg_named)
  "rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "slope_nonneg" ":=" term ","
    "slope_le_const" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "slope_nonneg" ":=" term ","
    "slope_le_const" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_affine_inner_lag_state_nonneg_named)
  "rr_lw_neg_C_mul_affine_inner_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "slope_nonneg" ":=" term ","
    "slope_le_const" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_state_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_state_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_state_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax
  (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_state_nonneg_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_state_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_state_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_negative_inner_lag_sequence_named)
  "rr_lw_negative_inner_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("negOneAddX" <|> "negOneAddTwoX") :
  tactic

syntax (name := rr_lw_negative_inner_lag_sequence_realrooted_named)
  "rr_lw_negative_inner_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("negOneAddX" <|> "negOneAddTwoX") :
  tactic

syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_sq_sub_one_lag_state_nonneg_named)
  "rr_lw_X_sq_sub_one_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_state_nonneg_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_state_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_state_nonneg_auto_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_state_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_mul_sequence_named)
  "rr_lw_positive_X_mul_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_mul_sequence_realrooted_named)
  "rr_lw_positive_X_mul_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_sequence_named)
  "rr_lw_positive_C_mul_X_mul_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_sequence_auto_named)
  "rr_lw_positive_C_mul_X_mul_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_sequence_realrooted_named)
  "rr_lw_positive_C_mul_X_mul_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto_named)
  "rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_mul_state_named)
  "rr_lw_positive_X_mul_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_state_named)
  "rr_lw_positive_C_mul_X_mul_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_C_mul_X_mul_state_auto_named)
  "rr_lw_positive_C_mul_X_mul_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_tR_lag_sequence_named)
  "rr_lw_tR_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_tR_lag_sequence_realrooted_named)
  "rr_lw_tR_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_c_tR_lag_sequence_named)
  "rr_lw_c_tR_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_c_tR_lag_sequence_auto_named)
  "rr_lw_c_tR_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_c_tR_lag_sequence_realrooted_named)
  "rr_lw_c_tR_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_c_tR_lag_sequence_realrooted_auto_named)
  "rr_lw_c_tR_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_sub_X_lag_sequence_named)
  "rr_lw_X_one_sub_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_sub_X_lag_sequence_realrooted_named)
  "rr_lw_X_one_sub_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_auto_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_sub_X_lag_state_named)
  "rr_lw_X_one_sub_X_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_C_sub_C_mul_X_lag_state_named)
  "rr_lw_X_C_sub_C_mul_X_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_C_sub_C_mul_X_lag_state_auto_named)
  "rr_lw_X_C_sub_C_mul_X_lag_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_state_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_state_auto_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_CX_sequence_named)
  "rr_lw_current_CX_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_CX_sequence_auto_named)
  "rr_lw_current_CX_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_CX_sequence_realrooted_named)
  "rr_lw_current_CX_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_CX_sequence_realrooted_auto_named)
  "rr_lw_current_CX_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_X_sequence_named)
  "rr_lw_current_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_X_sequence_auto_named)
  "rr_lw_current_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_X_sequence_realrooted_named)
  "rr_lw_current_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_X_sequence_realrooted_auto_named)
  "rr_lw_current_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_one_add_X_sequence_named)
  "rr_lw_current_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_one_add_X_sequence_auto_named)
  "rr_lw_current_one_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_one_add_X_sequence_realrooted_named)
  "rr_lw_current_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_one_add_X_sequence_realrooted_auto_named)
  "rr_lw_current_one_add_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_CX_state_named)
  "rr_lw_current_CX_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_CX_state_auto_named)
  "rr_lw_current_CX_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_X_state_named)
  "rr_lw_current_X_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_X_state_auto_named)
  "rr_lw_current_X_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_one_add_X_state_named)
  "rr_lw_current_one_add_X_state" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_current_one_add_X_state_auto_named)
  "rr_lw_current_one_add_X_state_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_exact_or_simpa)
  "rr_lw_exact_or_simpa" term ", " term :
  tactic

syntax (name := rr_lw_exact_or_simpa_mul_assoc)
  "rr_lw_exact_or_simpa_mul_assoc" term ", " term :
  tactic

macro_rules
  | `(tactic| rr_lw_exact_or_simpa $hdirect:term, $hnormalized:term) =>
      `(tactic|
        rr_first_exact_or_simpa $hdirect, $hnormalized)
  | `(tactic| rr_lw_exact_or_simpa_mul_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc $hdirect, $hnormalized)
  | `(tactic|
      rr_liu_wang using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg_lo:term, $hdeg_hi:term, $hno:term, $hb_nonpos:term) =>
      `(tactic|
        simpa using
          (RealRooted.prec_generalizedLiuWang_of_no_common
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_nonpos)))
  | `(tactic|
      rr_liu_wang using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_liu_wang using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg_lo,
          $hdeg_hi, $hno, $hb_nonpos)
  | `(tactic|
      rr_liu_wang_strict using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg_lo:term, $hdeg_hi:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        simpa using
          (RealRooted.prec_generalizedLiuWang_strict
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_strict using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_liu_wang_strict using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg_lo,
          $hdeg_hi, $hno, $hb_neg)
  | `(tactic|
      rr_liu_wang_strict_same using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        simpa using
          (RealRooted.prec_generalizedLiuWang_strict_same
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_strict_same using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_liu_wang_strict_same using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg,
          $hno, $hb_neg)
  | `(tactic|
      rr_liu_wang_strict_succ using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        simpa using
          (RealRooted.prec_generalizedLiuWang_strict_succ
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_strict_succ using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_liu_wang_strict_succ using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg,
          $hno, $hb_neg)
  | `(tactic|
      rr_liu_wang_two using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_two_of_nonpos
            $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hno $hb_nonpos),
          (RealRooted.prec_lw_two_of_nonpos
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno
            (rr_lw_simpa $hb_nonpos)))
  | `(tactic|
      rr_liu_wang_two_strict using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_two_strict_of_neg
            $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hno $hb_neg),
          (RealRooted.prec_lw_two_strict_of_neg
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_two_strict_same using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_two_strict_same_of_neg
            $hgf $hg_pos $hF_pos $hdeg $hno $hb_neg),
          (RealRooted.prec_lw_two_strict_same_of_neg
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_two_strict_succ using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_two_strict_succ_of_neg
            $hgf $hg_pos $hF_pos $hdeg $hno $hb_neg),
          (RealRooted.prec_lw_two_strict_succ_of_neg
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_two_strict_branch using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_branch := $hdegree:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_two_strict_branch_of_neg
            $hgf $hg_pos $hF_pos $hdegree $hno $hb_neg),
          (RealRooted.prec_lw_two_strict_branch_of_neg
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdegree)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_lw_positive_t using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_positive_t_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_t_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_t_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_t using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          roots_nonpos := $hf_roots,
          coeff_nonneg := rr_lw_coeff_nonneg_term,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_positive_X using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        have _rr_lw_unit_coeff_nonneg : 0 ≤ (1 : ℝ) := $hc
        ; rr_lw_positive_X using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          roots_nonpos := $hf_roots,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_positive_X using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_positive_X_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_X_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_X_unit using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_X using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          roots_nonpos := $hf_roots,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_positive_t_nonneg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_positive_t_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_t_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_t_nonneg_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_t_nonneg using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          nonneg_coeffs := $hf_nonneg,
          coeff_nonneg := rr_lw_coeff_nonneg_term,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_positive_X_mul using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.prec_lw_positive_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.prec_lw_positive_C_mul_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_C_mul_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_X_mul_nonneg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.prec_lw_positive_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_nonneg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.prec_lw_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_nonneg_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.prec_lw_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg rr_lw_coeff_nonneg_term $hQ
            $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg rr_lw_coeff_nonneg_term $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_square using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_square_lag
            $hgf $hg_pos $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_square_lag
            $hgf $hg_pos $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_square_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_square_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_square_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_monic_quadratic using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        discriminant := $hdisc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_monic_quadratic_lag
            $hgf $hg_pos $hdisc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_monic_quadratic_lag
            $hgf $hg_pos $hdisc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_monic_quadratic_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_monic_quadratic_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_monic_quadratic_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_quadratic using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_quadratic_lag
            $hgf $hg_pos $ha $hc $hdisc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_quadratic_lag
            $hgf $hg_pos $ha $hc $hdisc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_quadratic_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_quadratic_lag
            $hgf $hg_pos
            rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term
            $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_quadratic_lag
            $hgf $hg_pos
            rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_const_lag
            $hgf $hg_pos $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_const_lag
            $hgf $hg_pos $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_const_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_const_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const_C_neg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_const_lag_C_neg
            $hgf $hg_pos $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_const_lag_C_neg
            $hgf $hg_pos $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const_C_neg_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_negative_const_lag_C_neg
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.prec_lw_negative_const_lag_C_neg
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_nonpos_lag_step using
        interlaces := $hInter:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        lag_nonpos := $hB:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_two_of_nonpos_of_recurrence
            $hInter $hg_pos $hrec $hF_pos $hdeg_succ $hno $hB),
          (RealRooted.prec_lw_two_of_nonpos_of_recurrence
            $hInter $hg_pos
            (rr_lw_simpa $hrec)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_succ)
            $hno
            (rr_lw_simpa $hB)))
  | `(tactic|
      rr_lw_nonpos_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_nonpos
            $hbase $hpos $hB $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_nonpos_lag_state using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.prec_sequence $hstate)
  | `(tactic|
      rr_lw_nonpos_lag_state_realrooted using
        state := $hstate:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LwNonposLagSequenceState.isRealRooted $hstate))
  | `(tactic|
      rr_lw_nonpos_lag_state_interlaces using
        state := $hstate:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.interlaces_sequence $hstate)
  | `(tactic|
      rr_lw_global_nonpos_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_nonpos
          (B := $B) $hbase $hpos (by
            intro n r hr
            rr_sign) $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_global_nonpos_state_den_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_state_den_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_state_den_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_den
          (B := $B) $hbase $hpos (by
            intro n r hr
            rr_sign) $hden $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_nonpos
          (B := $B) $hbase $hpos (by
            intro n r hr
            rr_sign) $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_global_nonpos_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_nonpos
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
          (B := $B) $hbase $hpos (by
            intro n r hr
            rr_sign) $hden $hraw $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        have hrr :=
          ((RealRooted.LwNonposLagSequenceState.of_den
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hden $hraw $hdeg_succ $hno).isRealRooted);
        rr_exact_realrooted_sequence_or_projection hrr)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_den
            $hbase $hpos $hB $hden $hraw $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_den
            $hbase $hpos $hB $hden $hraw $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_const_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_const_lag
            $hbase $hpos $hc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_const_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_const_lag
            $hbase $hpos rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_const_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_const_lag
            $hbase $hpos $hc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_const_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_const_lag
            $hbase $hpos rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_const_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_const_lag
          $hbase $hpos $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_const_lag
          $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_const_C_neg_lag
            $hbase $hpos $hc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_const_C_neg_lag
            $hbase $hpos rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_const_C_neg_lag
            $hbase $hpos $hc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_const_C_neg_lag
            $hbase $hpos rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_const_C_neg_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_const_C_neg_lag
          $hbase $hpos $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_C_neg_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_const_C_neg_lag
          $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag
            $hbase $hpos $hc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag
            $hbase $hpos rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag
            $hbase $hpos $hc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_square_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag
            $hbase $hpos rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_square_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_square_lag
          $hbase $hpos $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_square_lag
          $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_unit using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag_unit
            $hbase $hpos $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_realrooted_unit using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag_unit
            $hbase $hpos $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_square_state_unit using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_square_lag_unit
          $hbase $hpos $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (c := $c) $hbase $hpos $hc $hden $hcoeff $hraw
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hc $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (c := $c) $hbase $hpos rr_lw_active_nonneg $hden $hcoeff $hraw
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_active_nonneg $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (c := $c) $hbase $hpos $hc $hden $hcoeff $hraw
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hc $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (c := $c) $hbase $hpos rr_lw_active_nonneg $hden $hcoeff $hraw
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_active_nonneg $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_monic_quadratic_lag
            $hbase $hpos $hdisc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_monic_quadratic_lag
            $hbase $hpos $hdisc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_monic_quadratic_lag
            $hbase $hpos rr_lw_quadratic_discriminant
            $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_monic_quadratic_lag
            $hbase $hpos rr_lw_quadratic_discriminant
            $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_quadratic_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag
            $hbase $hpos $ha $hc $hdisc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag
            $hbase $hpos $ha $hc $hdisc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_quadratic_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag
            $hbase $hpos rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag
            $hbase $hpos rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          leading_nonneg := $ha,
          constant_nonneg := $hc,
          discriminant := $hdisc,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $ha $hc $hdisc $hden $ha_coeff $hb_coeff $hc_coeff
            $hraw $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            $hden $ha_coeff $hb_coeff $hc_coeff $hraw
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          leading_nonneg := $ha,
          constant_nonneg := $hc,
          discriminant := $hdisc,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $ha $hc $hdisc $hden $ha_coeff $hb_coeff $hc_coeff
            $hraw $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            $hden $ha_coeff $hb_coeff $hc_coeff $hraw
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_t_lag_step using
        interlaces := $hInter:term,
        interlacer_pos_lc := $hg_pos:term,
        source_nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.prec_lw_positive_t_lag_of_nonneg_coeffs_of_recurrence
            $hInter $hg_pos $hf_nonneg $hc $hrec $hF_pos $hdeg_succ $hno),
          (RealRooted.prec_lw_positive_t_lag_of_nonneg_coeffs_of_recurrence
            $hInter $hg_pos
            (rr_lw_simpa $hf_nonneg)
            (rr_lw_simpa $hc)
            (rr_lw_simpa $hrec)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_succ)
            $hno))
  | `(tactic|
      rr_lw_positive_t_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_positive_t_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_positive_t_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_t_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg
            $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_t_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_t_lag
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_t_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_t_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_positive_X_lag
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_positive_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_X_lag
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_X_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_X_lag
          $hbase $hpos $hnonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
            $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
            $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
          $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_C_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg rr_lw_active_nonneg
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_positive_affine_lag
            $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_positive_affine_lag
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_affine_lag
            $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_positive_affine_lag
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
            $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
            $hbase $hpos ?_ $hshift_nonneg $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
            $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
            $hbase $hpos ?_ $hshift_nonneg $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_add_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_add_X_lag
            $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_add_X_lag
            $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_add_X_lag_shift_nonneg
            $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_add_X_lag_shift_nonneg
            $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_X_sub_X_pow_three_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_X_sub_X_pow_three_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneAddX) =>
      `(tactic|
        rr_lw_X_one_add_X_lag_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneAddX) =>
      `(tactic|
        rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneSubXOneAddX) =>
      `(tactic|
        rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneSubXOneAddX) =>
      `(tactic|
        rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xSubXPowThree) =>
      `(tactic|
        rr_lw_X_sub_X_pow_three_lag_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xSubXPowThree) =>
      `(tactic|
        rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneSubXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneSubXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSubXPowThree) =>
      `(tactic|
        rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSubXPowThree) =>
      `(tactic|
        rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSqSubOne) =>
      `(tactic|
        rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSqSubOne) =>
      `(tactic|
        rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := oneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_one_add_X_one_add_two_X_lag_sequence_interval using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := oneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulOneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulOneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_one_add_X_one_add_two_X_lag_sequence_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos $hroot_lower $hroot_upper $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos $hroot_lower $hroot_upper $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos $hc $hroot_lower $hroot_upper $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos ?_ $hroot_lower $hroot_upper $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos $hc $hroot_lower $hroot_upper $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos ?_ $hroot_lower $hroot_upper $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        slope_nonneg := $hb:term,
        slope_le_const := $hba:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_neg_C_mul_affine_inner_lag_nonneg
            $hbase $hpos $hnonneg $hc $hb $hba $hroot_lower $hrec
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        slope_nonneg := $hb:term,
        slope_le_const := $hba:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_affine_inner_lag_nonneg
            $hbase $hpos $hnonneg $hc $hb $hba $hroot_lower $hrec
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec
            $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec
            $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          coeff_nonneg := $hc,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower
            $hden $hcoeff $hraw $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
            (c := $c) $hbase $hpos $hnonneg ?_ $hroot_lower
            $hden $hcoeff $hraw $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          coeff_nonneg := $hc,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower
            $hden $hcoeff $hraw $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
            (c := $c) $hbase $hpos $hnonneg ?_ $hroot_lower
            $hden $hcoeff $hraw $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_negative_inner_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_inner_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_inner_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddTwoX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower_half := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_inner_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddTwoX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower_half := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_X_mul_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact
          ((RealRooted.LwNonposLagSequenceState.of_positive_X_mul_lag
            $hbase $hpos $hnonneg $hQ $hrec $hdeg_succ $hno).prec_sequence),
          ((RealRooted.LwNonposLagSequenceState.of_positive_X_mul_lag
            $hbase $hpos $hnonneg $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_positive_X_mul_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_X_mul_lag
            $hbase $hpos $hnonneg $hQ $hrec $hdeg_succ $hno).isRealRooted),
          ((RealRooted.LwNonposLagSequenceState.of_positive_X_mul_lag
            $hbase $hpos $hnonneg $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact
          ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
            $hbase $hpos $hnonneg $hc $hQ $hrec $hdeg_succ $hno).prec_sequence),
          ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
            $hbase $hpos $hnonneg $hc $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        first
          | rr_lw_refine_active_nonneg_seq
              ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
                $hbase $hpos $hnonneg ?_ $hQ $hrec $hdeg_succ
                $hno).prec_sequence)
          | rr_lw_refine_active_nonneg_seq
              ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
                (hbase := $hbase) (hpos := $hpos) (hnonneg := $hnonneg)
                (hQ_nonneg := $hQ)
                (hrec := rr_lw_recurrence_mul_assoc_seq $hrec)
                (hdeg_succ := $hdeg_succ) (hno := $hno) (hc := ?_)).prec_sequence))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
            $hbase $hpos $hnonneg $hc $hQ $hrec $hdeg_succ $hno).isRealRooted),
          ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
            $hbase $hpos $hnonneg $hc $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (by
            rr_lw_refine_active_nonneg_seq
              ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
                $hbase $hpos $hnonneg ?_ $hQ $hrec $hdeg_succ
                $hno).isRealRooted)),
          (by
            rr_lw_refine_active_nonneg_seq
              ((RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
                (hbase := $hbase) (hpos := $hpos) (hnonneg := $hnonneg)
                (hQ_nonneg := $hQ)
                (hrec := rr_lw_recurrence_mul_assoc_seq $hrec)
                (hdeg_succ := $hdeg_succ) (hno := $hno) (hc := ?_)).isRealRooted)))
  | `(tactic|
      rr_lw_tR_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_X_mul_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_tR_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_X_mul_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff_nonneg := $hc,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff_nonneg := $hc,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_X_one_sub_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_X_mul_one_sub_X_lag
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_X_one_sub_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_X_mul_one_sub_X_lag
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg $ha $hb $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg $ha $hb $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg $hc $ha $hb $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg ?_ ?_ ?_ $hrec $hdeg_succ
            $hno).prec_sequence))
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg $hc $ha $hb $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          ((RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg ?_ ?_ ?_ $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_current_CX_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_current_CX_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_current_CX_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_current_CX_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_current_CX_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_current_CX_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_current_CX_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_current_CX_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
            $hno).isRealRooted))
  | `(tactic|
      rr_lw_current_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact
          ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).prec_sequence),
          ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
            $hbase $hpos $hnonneg $hc (rr_lw_recurrence_seq $hrec)
            $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_current_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        first
          | exact
              (RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
                $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec
                $hdeg_succ $hno).prec_sequence
          | rr_lw_refine_active_nonneg_seq
              ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
                $hbase $hpos $hnonneg ?_ (rr_lw_recurrence_seq $hrec)
                $hdeg_succ $hno).prec_sequence))
  | `(tactic|
      rr_lw_current_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).isRealRooted),
          ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
            $hbase $hpos $hnonneg $hc (rr_lw_recurrence_seq $hrec)
            $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_current_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
            $hno).isRealRooted),
          (by
            rr_lw_refine_active_nonneg_seq
              ((RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
                $hbase $hpos $hnonneg ?_ (rr_lw_recurrence_seq $hrec)
                $hdeg_succ $hno).isRealRooted)))
  | `(tactic|
      rr_lw_current_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).prec_sequence)
  | `(tactic|
      rr_lw_current_one_add_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          (RealRooted.LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
            $hno).prec_sequence)
  | `(tactic|
      rr_lw_current_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno).isRealRooted))
  | `(tactic|
      rr_lw_current_one_add_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          ((RealRooted.LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
            $hno).isRealRooted))

macro_rules
  | `(tactic|
      rr_lw_negative_square_state_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
          (c := $c) $hbase $hpos $hc $hden $hcoeff $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hc $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_state_den_coeff_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_state_den_coeff_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
          (c := $c) $hbase $hpos rr_lw_active_nonneg $hden $hcoeff $hraw
          $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_state_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_state_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_state_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_negative_square_lag_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_active_nonneg $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_negative_quadratic_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag
          $hbase $hpos $ha $hc $hdisc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag
          $hbase $hpos rr_lw_negative_quadratic_side
          rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_state_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $ha $hc $hdisc $hden $ha_coeff $hb_coeff $hc_coeff
            $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_state_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_state_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_state_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_state_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_state_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_negative_quadratic_lag_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            $hden $ha_coeff $hb_coeff $hc_coeff $hraw $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_state_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_nonneg
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower
            $hden $hcoeff $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_state_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_X_lag_den_coeff_nonneg
            (c := $c) $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
            $hden $hcoeff $hraw $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_state_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_neg_C_mul_one_add_two_mul_X_lag_nonneg
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
            $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_one_add_X_one_add_two_X_lag_state_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos $hroot_lower $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_state_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos $hc $hroot_lower $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_state_interval_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_C_mul_one_add_X_mul_one_add_two_mul_X_lag
            $hbase $hpos rr_lw_active_nonneg $hroot_lower $hroot_upper
            $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_neg_C_mul_affine_inner_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        slope_nonneg := $hb:term,
        slope_le_const := $hba:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_neg_C_mul_affine_inner_lag_nonneg
            $hbase $hpos $hnonneg $hc $hb $hba $hroot_lower $hrec
            $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_X_sq_sub_one_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_X_sq_sub_one_lag_nonneg
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_state_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_sq_sub_one_lag_nonneg
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
          $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_positive_affine_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_affine_lag
          $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_affine_lag
          $hbase $hpos rr_lw_active_nonneg $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_state_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
          $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_state_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_affine_lag_shift_nonneg
          $hbase $hpos rr_lw_active_nonneg $hshift_nonneg
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_add_X_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_add_X_lag
          $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_add_X_lag_state_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_add_X_lag_shift_nonneg
          $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_X_one_add_X_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_X_mul_one_add_X_lag_nonneg
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_X_sub_X_pow_three_lag_nonneg
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_state_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_add_X_lag_nonneg
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_state_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_nonneg
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
            $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_state_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_state_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_C_mul_X_sub_X_pow_three_lag_nonneg
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hroot_lower
          $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_positive_X_mul_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_X_mul_lag
          $hbase $hpos $hnonneg $hQ $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
          $hbase $hpos $hnonneg $hc $hQ $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_positive_C_mul_X_mul_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hQ $hrec
          $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_X_one_sub_X_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_X_mul_one_sub_X_lag
          $hbase $hpos $hnonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
          $hbase $hpos $hnonneg $ha $hb $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_X_mul_C_sub_C_mul_X_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg rr_lw_active_nonneg
          $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg $hc $ha $hb $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LwNonposLagSequenceState.of_C_mul_X_mul_C_sub_C_mul_X_lag
            $hbase $hpos $hnonneg rr_lw_active_nonneg rr_lw_active_nonneg
            rr_lw_active_nonneg $hrec $hdeg_succ $hno)

macro_rules
  | `(tactic|
      rr_lw_current_CX_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_current_CX_positive_t_lag
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_CX_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_current_CX_positive_t_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_X_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_X_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_current_X_positive_t_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_one_add_X_state using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_one_add_X_state_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LwNonposLagSequenceState.of_current_one_add_X_positive_t_lag
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ $hno)

end Tactic
end RealRooted
