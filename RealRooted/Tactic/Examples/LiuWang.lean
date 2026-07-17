import RealRooted.Tactic.Finish
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.RootBounds

/-!
# `rr_liu_wang` examples

Abstract smoke tests for the generalized Liu-Wang dispatcher tactics.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c := by
  rr_lw_coeff_nonneg

example {n : Nat} : 0 ≤ (n : ℝ) + 1 := by
  rr_lw_coeff_nonneg

example {n : Nat} (hn : 1 ≤ n) : 0 ≤ (n : ℝ) - 1 := by
  rr_lw_coeff_nonneg

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

example {f g a : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_rr : f ≠ 0 ∧ f.Splits)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X) * g) := by
  have hb_nonpos : ∀ r, f.IsRoot r → (C c * X : ℝ[X]).eval r ≤ 0 := by
    rr_sign_at_roots using hf_rr, hf_nonneg
  rr_liu_wang_two using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_nonpos := hb_nonpos

example {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c) * q ^ 2) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c) * q ^ 2) * g).natDegree)
    (hdeg_hi : (a * f + (-(C c) * q ^ 2) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c) * q ^ 2) * g) := by
  have hb_nonpos : ∀ r, f.IsRoot r → (-(C c) * q ^ 2 : ℝ[X]).eval r ≤ 0 := by
    intro r _hr
    rr_sign
  rr_liu_wang_two using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_nonpos := hb_nonpos

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
  have hc : 0 ≤ n ^ 2 + n - 1 := by
    nlinarith [sq_nonneg n]
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Full sequence-level `A154233`-style induction skeleton.

The coefficient is indexed as `(n+1)^2+(n+1)-1`, so every recurrence step is
inside the active range.  A sequence-specific file would prove the base case,
recurrence identity, coefficient nonnegativity, degree increments, and
no-common-root certificate from the concrete row definition. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) - 1) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_one_add_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same full sequence certificate also closes real-rootedness of every
row. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) - 1) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_current_one_add_X_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint: the same auto real-rootedness shell closes row
nonvanishing goals. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) - 1) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_lw_current_one_add_X_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Strict Family E1 unit-lag shell: `P_{n+2}=A_n P_{n+1}+tP_n`.

The plateau-safe version is handled by the Wagner-X shell; this wrapper covers
the same displayed lag when the concrete sequence has strict degree growth. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_X_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the strict positive unit-`X` lag shell. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint: the unit-`X` real-rootedness tactic also closes row
splitting goals. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_positive_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G6 affine half-line lag: `P_{n+2}=A_nP_{n+1}+(c_nt-a_n)P_n`.

The sign side-goal follows from nonnegative row coefficients, which put the
current roots on the half-line `(-∞, 0]`, together with `c_n,a_n >= 0`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_X_sub_C_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    scalar_nonneg := hc,
    constant_nonneg := ha,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same affine half-line lag shell. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_sub_C_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    scalar_nonneg := hc,
    constant_nonneg := ha,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The affine half-line lag also has an auto side-goal path for routine
nonnegative scalar parameters. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X - C (1 : ℝ)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the auto affine half-line lag shell. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X - C (1 : ℝ)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G7 shifted-root positive affine lag:
`P_{n+2}=A_nP_{n+1}+c_n(a_n+t)P_n`.

The side condition is the root-location certificate `r <= -a_n` for the
current row, which is what the shifted-variable argument supplies. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_affine_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient side-goal for active positive-affine lags such as
`(n+1)(1+t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (C (1 : ℝ) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_affine_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit positive-affine lag `a_n+t`, covering the direct `1+t` and `2+t`
shifted-Fibonacci records after the root bound is supplied. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_add_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The shifted certificate version removes the explicit root-location
hypothesis from the positive-affine lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_affine_lag_sequence_shift_nonneg using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same shifted certificate path with automatic scalar nonnegativity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (1 : ℝ))))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (C (1 : ℝ) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit positive-affine lag `a_n+t` with shifted nonnegative coefficients
supplying the root bound automatically. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg using
    base := hbase,
    pos_lc := hpos,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G7 inner-window lag:
`P_{n+2}=A_nP_{n+1}+c_n t(1+t)P_n`.

The current-row upper root bound `r <= 0` is derived from nonnegative
coefficients, while the sequence-specific proof supplies the lower bound
`-1 <= r`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the scalar inner-window lag, with automatic
coefficient nonnegativity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same inner-window route accepts the factored cubic lag
`c_n t(1-t)(1+t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
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
  prec_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

/-- Expanded cubic lag `c_n(t-t^3)` uses the same `[-1,0]` window. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
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
  isRealRooted_of_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
    hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

/-- Narrower Family G7 interval lag:
`P_{n+2}=A_nP_{n+1}+c_n(1+t)(1+2t)P_n`.

This shape needs both root-window certificates `-1 <= r` and `r <= -1/2`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same interval lag, with automatic
coefficient nonnegativity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (C ((n : ℝ) + 1) * (1 + X) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto using
    base := hbase,
    pos_lc := hpos,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Inner-window negative affine lag:
`P_{n+2}=A_nP_{n+1}-c_n(a_n+b_n t)P_n`, with `0 <= b_n <= a_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    slope_nonneg := hb,
    slope_le_const := hba,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The common `-c_n(1+t)` lag has a shorter wrapper and an automatic
coefficient side-goal. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar-denominator raw recurrence whose normalized lag is `-(1+t)`.

This is the denominator bookkeeping needed for `A124848`/`A347056`-style
records after the active-range coefficient equation is supplied. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun _ => (1 : ℝ),
    root_lower := hroot_lower,
    den_nonzero := by rr_scalar_active_den_all,
    coeff_eq := by rr_scalar_coeff_all,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The tighter affine lag `-c_n(1+2t)` only needs roots in `[-1/2,0]`;
the upper half is still derived from nonnegative coefficients. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower_half := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The expanded inner-window lag `c_n(t^2-1)` covers recurrences with
`(-1+t^2)P_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Generic sequence-level nonpositive-lag shell.

This is the full induction form behind the Family G wrappers: the
sequence-specific file supplies the root-side sign certificate for the lag
coefficient. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_nonpos_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    lag_nonpos := hB,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The generic nonpositive-lag shell also gives real-rootedness of all rows. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag_nonpos := hB,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family E2-style global lag: `P_{n+2}=A_n P_{n+1}-t^2P_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G global lag: negative-definite monic quadratic. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ)),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scaled negative-definite quadratic lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_global_nonpos_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun n =>
      -(C ((n : ℝ) + 1)) * (X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ)),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like sequence shell: negative constant lag with automatic
nonnegativity of `c_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like sequence shell with an explicit coefficient certificate. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like negative-constant shell, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like negative-constant shell, automatic real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` negative-constant lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (-((n : ℝ) + 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_C_neg_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` lag with an explicit coefficient certificate. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_C_neg_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` lag with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (-((n : ℝ) + 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_C_neg_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G sequence shell: Narayana/Jacobi-style negative-square lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 - X : ℝ[X]) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G sequence shell: shifted-square lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ (n : ℝ) + 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (X - C α) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G negative-square lag, automatic real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (X - C (2 : ℝ)) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G shifted-square lag with unit scalar coefficient. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((X - C α : ℝ[X]) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_unit using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit shifted-square lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((X - C α : ℝ[X]) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted_unit using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A181738`-style sequence shell: negative-definite monic quadratic lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_monic_quadratic_sequence using
    base := hbase,
    pos_lc := hpos,
    discriminant := (fun _ => by norm_num),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same negative-definite quadratic sequence shell closes all rows. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_monic_quadratic_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    discriminant := (fun _ => by norm_num),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same negative-definite quadratic shell with automatic discriminant
discharge. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_monic_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic discriminant discharge, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_monic_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A001607`-style sequence shell: non-monic negative-definite quadratic
lag `-(2t^2-t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same non-monic negative quadratic shell. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A010892`-style sequence shell: repeated lag `-(t^2+t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (1 : ℝ) * X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A049347`-style sequence shell: repeated lag `-(t^2-t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (1 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A078020`-style sequence shell: repeated lag `-(2t^2+t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Active-leading-coefficient smoke test for repeated
`-(k t^2+t+1)` families. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1) * X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized raw quadratic smoke test.

The raw recurrence has a left factor `n+1` and raw lag coefficients
`(n+1) * (-(2t^2-t+1))`; after scalar cancellation the usual non-monic
quadratic discriminant certificate applies. -/
example {P : Nat → ℝ[X]} {Araw : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        Araw n * P (n + 1) +
          (-(C (2 * ((n : ℝ) + 1)) * X ^ 2 +
            C (-((n : ℝ) + 1)) * X + C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    den_nonzero := by rr_scalar_active_den_all,
    leading_coeff_eq := by rr_scalar_coeff_all,
    linear_coeff_eq := by rr_scalar_coeff_all,
    constant_coeff_eq := by rr_scalar_coeff_all,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- OEIS-style active-range check: after the active index threshold, a fitted
coefficient `c_n - 2` gives the nonnegative positive-`t` lag. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hactive : (2 : ℝ) ≤ c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g))
    (hdeg_lo :
      f.natDegree ≤ ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g).natDegree)
    (hdeg_hi :
      ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Active-range same-degree branch: a negative constant lag gives a plateau
step when the degree certificate says no new degree appears. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hactive : (2 : ℝ) < c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + C (2 - c) * g))
    (hdeg : (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree))
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + C (2 - c) * g) := by
  have hb_neg : ∀ r, f.IsRoot r → (C (2 - c) : ℝ[X]).eval r < 0 := by
    intro r _hr
    simpa using sub_neg.mpr hactive
  rr_liu_wang_two_strict_same using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

/-- Active-range successor-degree branch: the same sign certificate dispatches
to the degree-increase Liu--Wang wrapper when the degree certificate says so. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hactive : (2 : ℝ) < c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + C (2 - c) * g))
    (hdeg :
      (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree + 1))
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + C (2 - c) * g) := by
  have hb_neg : ∀ r, f.IsRoot r → (C (2 - c) : ℝ[X]).eval r < 0 := by
    intro r _hr
    simpa using sub_neg.mpr hactive
  rr_liu_wang_two_strict_succ using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

/-- The same active-range plateau/successor choice can be kept as a single
degree branch until the tactic dispatches to the matching Liu--Wang theorem. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hactive : (2 : ℝ) < c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + C (2 - c) * g))
    (hdegree :
      (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree) ∨
        (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree + 1))
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + C (2 - c) * g) := by
  have hb_neg : ∀ r, f.IsRoot r → (C (2 - c) : ℝ[X]).eval r < 0 := by
    intro r _hr
    simpa using sub_neg.mpr hactive
  rr_liu_wang_two_strict_branch using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_branch := hdegree,
    no_common_roots := hno,
    head_neg := hb_neg

/-- Plateau sequence skeleton combining the branch induction shell with the
strict Liu--Wang same/successor degree dispatcher.

The remaining sequence-specific input is `hinter`: for a concrete plateau
family, this is where one proves that the previous `Prec` certificate gives
the interlacer needed by the strict Liu--Wang step. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hinter : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Interlaces (P n) (P (n + 1)))
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)
    (hb_neg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r < 0) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let hsame : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)) := by
    intro n hdeg hprev
    have htarget_pos :
        HasPosLeadingCoeff (A n * P (n + 1) + B n * P n) := by
      simpa [← hrec n] using hpos (n + 2)
    have hbranch :
        (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree ∨
          (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree + 1 := by
      left
      simpa [← hrec n] using hdeg
    have hstep :
        Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) := by
      rr_liu_wang_two_strict_branch using
        interlacer := hinter n hprev,
        interlacer_pos_lc := hpos n,
        target_pos_lc := htarget_pos,
        degree_branch := hbranch,
        no_common_roots := hno n,
        head_neg := hb_neg n
    simpa [← hrec n] using hstep
  let hsucc : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)) := by
    intro n hdeg hprev
    have htarget_pos :
        HasPosLeadingCoeff (A n * P (n + 1) + B n * P n) := by
      simpa [← hrec n] using hpos (n + 2)
    have hbranch :
        (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree ∨
          (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree + 1 := by
      right
      simpa [← hrec n] using hdeg
    have hstep :
        Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) := by
      rr_liu_wang_two_strict_branch using
        interlacer := hinter n hprev,
        interlacer_pos_lc := hpos n,
        target_pos_lc := htarget_pos,
        degree_branch := hbranch,
        no_common_roots := hno n,
        head_neg := hb_neg n
    simpa [← hrec n] using hstep
  rr_prec_sequence_branches using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

/-- OEIS shapes `A154227`/`A154228`/`A249248`, using nonnegative coefficients
to infer the half-line root certificate for a positive `t` lag. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ ((1 + X : ℝ[X]) * f + (C c * X) * g).natDegree)
    (hdeg_hi : ((1 + X : ℝ[X]) * f + (C c * X) * g).natDegree ≤
      f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + (C c * X) * g) := by
  rr_lw_positive_t_nonneg_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Favard-like negative constant lag, available as a direct Liu--Wang
sign-test path when the adjacent interlacing invariant is already known. -/
example {f g : ℝ[X]} {α c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + (-(C c)) * g))
    (hdeg_lo : f.natDegree ≤ ((X - C α) * f + (-(C c)) * g).natDegree)
    (hdeg_hi : ((X - C α) * f + (-(C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + (-(C c)) * g) := by
  rr_lw_negative_const using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Favard-like negative constant lag with automatic constant nonnegativity. -/
example {f g : ℝ[X]} {α : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + (-(C (1 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤ ((X - C α) * f + (-(C (1 : ℝ))) * g).natDegree)
    (hdeg_hi :
      ((X - C α) * f + (-(C (1 : ℝ))) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + (-(C (1 : ℝ))) * g) := by
  rr_lw_negative_const_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Normalized negative constant lag with automatic constant nonnegativity. -/
example {f g : ℝ[X]} {α : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + C (-1 : ℝ) * g))
    (hdeg_lo : f.natDegree ≤ ((X - C α) * f + C (-1 : ℝ) * g).natDegree)
    (hdeg_hi : ((X - C α) * f + C (-1 : ℝ) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + C (-1 : ℝ) * g) := by
  rr_lw_negative_const_C_neg_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Family G quadratic lag: `B(t) = -c(t-α)^2`, a globally nonpositive lag. -/
example {f g a : ℝ[X]} {α c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c) * (X - C α) ^ 2) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c) * (X - C α) ^ 2) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C c) * (X - C α) ^ 2) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c) * (X - C α) ^ 2) * g) := by
  rr_lw_negative_square using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Family G unit negative-square lag with automatic coefficient
nonnegativity. -/
example {f g a : ℝ[X]} {α : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g) := by
  rr_lw_negative_square_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A181738`: a negative-definite monic quadratic lag can be
certified directly by the discriminant inequality, without exposing a square. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g) := by
  rr_lw_negative_monic_quadratic_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step non-monic negative quadratic lag, with explicit scalar
certificates. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g) := by
  rr_lw_negative_quadratic using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    leading_nonneg := by norm_num,
    constant_nonneg := by norm_num,
    discriminant := by norm_num,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step non-monic negative quadratic lag, with automatic scalar
certificates. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g) := by
  rr_lw_negative_quadratic_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step Family E3 product lag: `t Q(t)` reduces to a focused
`Q(r) >= 0` certificate at current-row roots. -/
example {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * q) * g) := by
  rr_lw_positive_X_mul using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step scalar product lag, deriving the half-line root bound from
nonnegative coefficients and closing the scalar side goal automatically. -/
example {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C (2 : ℝ) * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C (2 : ℝ) * X * q) * g).natDegree)
    (hdeg_hi :
      (a * f + (C (2 : ℝ) * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C (2 : ℝ) * X * q) * g) := by
  rr_lw_positive_C_mul_X_mul_nonneg_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Family E3 product-lag sequence shell: once the concrete recurrence supplies
`Q_n(r) >= 0` at current-row roots, the tactic handles the `t Q_n(t)` sign
test and the Liu--Wang induction. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_X_mul_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The product-lag sequence tactic accepts the natural associated form
`X * (Q_n * P_n)` by associativity, avoiding local rewrite blocks. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * (Q n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_X_mul_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same `t Q_n(t)` sequence shell closes real-rootedness of every row. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_X_mul_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the `t Q_n(t)` shell; this also checks the
associativity fallback branch. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_positive_X_mul_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The explicit scalar product-lag real-rootedness endpoint also accepts
`c_n X (Q_n P_n)` by associativity.  Use the explicit coefficient certificate
for this parenthesized scalar form. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (c n) * (X * (Q n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_C_mul_X_mul_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar product-lag sequence shell with automatic nonnegativity of the
scalar coefficient. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_C_mul_X_mul_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The automatic scalar product-lag shell also accepts the associated form
`c_n X (Q_n P_n)` when `positivity` can prove `0 <= c_n`. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + C ((n : ℝ) + 1) * (X * (Q n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_C_mul_X_mul_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same associated scalar product-lag form. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + C ((n : ℝ) + 1) * (X * (Q n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- A window-certified product lag: if current-row roots lie in `[-1, 0]`,
then `Q(t)=1+t` is nonnegative at those roots and the scalar product-lag
tactic applies. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * (1 + X : ℝ[X])) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r →
      0 ≤ ((1 + X : ℝ[X]).eval r) := by
    intro n r hr
    have hlo : -1 ≤ r := hroot_lower n r hr
    have hnonneg : 0 ≤ 1 + r := by linarith
    simpa [add_comm] using hnonneg
  rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family E strict-degree `t R_n(t)` spelling.  This is the named surface for
the largest clean three-term Liu--Wang bucket. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_tR_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same `t R_n(t)` Family E shell. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the named `t R_n(t)` router, using the associated
recurrence shape produced by some promoted product-lag rows. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * (R n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar active-coefficient form `c_n t R_n(t)` with the coefficient
nonnegativity closed by the active-index helper. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_c_tR_lag_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for active-coefficient `c_n t R_n(t)` recurrences. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_c_tR_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the active-coefficient `c_n t R_n(t)` router,
again in the associated product-lag form. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + C ((n : ℝ) + 1) * (X * (R n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_c_tR_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

end Tactic
end RealRooted
