import RealRooted.Tactic.LiuWang.SequenceNonpositive
import RealRooted.Tactic.LiuWang.SequencePositive

/-!
# Liu--Wang direct-step regression examples

Executable examples for the direct Liu--Wang dispatchers, helper syntax, and
one-step OEIS recurrence forms.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c := by rr_lw_coeff_nonneg

example {n : Nat} : 0 ≤ (n : ℝ) + 1 := by rr_lw_coeff_nonneg

example {n : Nat} (hn : 1 ≤ n) : 0 ≤ (n : ℝ) - 1 := by rr_lw_coeff_nonneg

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_lw_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_lw_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_lw_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_lw_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_lw_coeff_all_term

example {f g F a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hrec : F = a * f + b * g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : f.natDegree + 1 = F.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  rr_lw_nonpos_lag_step using
    interlaces := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    recurrence := hrec,
    degree_succ := hdeg,
    no_common_roots := hno,
    lag_nonpos := hb_nonpos

example {f g F a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hrec : F = a * f + (C c * X) * g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : f.natDegree + 1 = F.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X) * g) := by
  rr_lw_positive_t_lag_step using
    interlaces := hgf,
    interlacer_pos_lc := hg_pos,
    source_nonneg_coeffs := hf_nonneg,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    recurrence := hrec,
    degree_succ := hdeg,
    no_common_roots := hno

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg_lo, hdeg_hi, hno,
    hb_nonpos

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_nonpos := hb_nonpos

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg_lo, hdeg_hi, hno,
    hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg : (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_same using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg, hno, hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg : (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_same using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_succ using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg, hno, hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_succ using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  rr_liu_wang_two using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_nonpos := hb_nonpos

example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  rr_liu_wang_two_strict using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  rr_liu_wang_two_strict_same using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  rr_liu_wang_two_strict_succ using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

/-- Positive `t`-lag with the nonpositive-root certificate inferred from
nonnegative coefficients. -/
example {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X) * g) := by
  rr_lw_positive_t_nonneg using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Positive `t`-lag accepts the natural algebraic form `X * g`, not only
`(C 1 * X) * g`. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + X * g) := by
  rr_lw_positive_X using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Compatibility spelling for unit `X` lags that still supplies the trivial
coefficient certificate. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hunit : 0 ≤ (1 : ℝ))
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + X * g) := by
  rr_lw_positive_X using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    coeff_nonneg := hunit,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Explicit unit-`X` one-step alias for positive lags. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + X * g) := by
  rr_lw_positive_X_unit using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Negative-square lag with the global sign certificate handled by `rr_sign`. -/
example {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c) * q ^ 2) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c) * q ^ 2) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c) * q ^ 2) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c) * q ^ 2) * g) := by
  rr_lw_negative_square using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Negative-constant lag as a Liu--Wang sign-test route. -/
example {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c)) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c)) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c)) * g) := by
  rr_lw_negative_const using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Negative-constant lag accepts `C (-c) * g`, matching common recurrence
normalizations from fitted OEIS data. -/
example {f g : ℝ[X]} {α c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + C (-c) * g))
    (hdeg_lo : f.natDegree ≤ ((X - C α) * f + C (-c) * g).natDegree)
    (hdeg_hi : ((X - C α) * f + C (-c) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + C (-c) * g) := by
  rr_lw_negative_const_C_neg using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Local OEIS step shape `P_n = P_{n-1}+tP_{n-2}`.

For plateau degree sequences such as `A169803`, this one-step certificate is
used inside the branch/Wagner sequence shell rather than as a strict
degree-increment sequence proof by itself. -/
example {f g : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff ((1 : ℝ[X]) * f + (C (1 : ℝ) * X) * g))
    (hdeg_lo : f.natDegree ≤ ((1 : ℝ[X]) * f + (C (1 : ℝ) * X) * g).natDegree)
    (hdeg_hi :
      ((1 : ℝ[X]) * f + (C (1 : ℝ) * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 : ℝ[X]) * f + (C (1 : ℝ) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shapes `A008288`/`A035607`/`A102413`/`A122542`:
`P_n = (1+t)P_{n-1} + t P_{n-2}`. -/
example {f g : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos :
      HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + (C (1 : ℝ) * X) * g))
    (hdeg_lo :
      f.natDegree ≤ ((1 + X : ℝ[X]) * f + (C (1 : ℝ) * X) * g).natDegree)
    (hdeg_hi :
      ((1 + X : ℝ[X]) * f + (C (1 : ℝ) * X) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + (C (1 : ℝ) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shapes `A100862`/`A122848`: `P_n = (1+t)P_{n-1}+c_n t P_{n-2}`. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((1 + X) * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ ((1 + X) * f + (C c * X) * g).natDegree)
    (hdeg_hi : ((1 + X) * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X) * f + (C c * X) * g) := by
  rr_lw_positive_t using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A049403`: `P_n = t P_{n-1} + c_n t P_{n-2}`. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (X * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (X * f + (C c * X) * g).natDegree)
    (hdeg_hi : (X * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (X * f + (C c * X) * g) := by
  rr_lw_positive_t using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A079510`: `P_n = c_n t P_{n-1} + c_n t P_{n-2}`. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((C c * X) * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ ((C c * X) * f + (C c * X) * g).natDegree)
    (hdeg_hi : ((C c * X) * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((C c * X) * f + (C c * X) * g) := by
  rr_lw_positive_t using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step scalar `c t Q(t)` positive lag with an explicit factor
nonnegativity certificate. -/
example {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X * q) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X * q) * g) := by
  rr_lw_positive_C_mul_X_mul using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    coeff_nonneg := hc,
    factor_nonneg := hq_nonneg,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A113214`: `P_n = t P_{n-1} + t P_{n-2}`. -/
example {f g : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (X * f + (C (1 : ℝ) * X) * g))
    (hdeg_lo : f.natDegree ≤ (X * f + (C (1 : ℝ) * X) * g).natDegree)
    (hdeg_hi : (X * f + (C (1 : ℝ) * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (X * f + (C (1 : ℝ) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A113953`: `P_n = t P_{n-1} + 2t P_{n-2}`. -/
example {f g : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (X * f + (C (2 : ℝ) * X) * g))
    (hdeg_lo : f.natDegree ≤ (X * f + (C (2 : ℝ) * X) * g).natDegree)
    (hdeg_hi : (X * f + (C (2 : ℝ) * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (X * f + (C (2 : ℝ) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A106828`: `P_n = n P_{n-1} + n t P_{n-2}`.
The lag coefficient is discharged by the auto scalar side-goal path. -/
example {f g : ℝ[X]} {n : Nat}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (C (n : ℝ) * f + (C (n : ℝ) * X) * g))
    (hdeg_lo : f.natDegree ≤ (C (n : ℝ) * f + (C (n : ℝ) * X) * g).natDegree)
    (hdeg_hi :
      (C (n : ℝ) * f + (C (n : ℝ) * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (C (n : ℝ) * f + (C (n : ℝ) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A154233`: active positive polynomial coefficient
`n^2+n-1` in the positive `t` lag. -/
example {f g : ℝ[X]} {n : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hn : 1 ≤ n)
    (hF_pos :
      HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + (C (n ^ 2 + n - 1) * X) * g))
    (hdeg_lo :
      f.natDegree ≤ ((1 + X : ℝ[X]) * f + (C (n ^ 2 + n - 1) * X) * g).natDegree)
    (hdeg_hi :
      ((1 + X : ℝ[X]) * f + (C (n ^ 2 + n - 1) * X) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + (C (n ^ 2 + n - 1) * X) * g) := by
  have hc : 0 ≤ n ^ 2 + n - 1 := by nlinarith [sq_nonneg n]
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno


end Tactic
end RealRooted
