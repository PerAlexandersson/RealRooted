import RealRooted.Tactic.Examples.LiuWang.Step
import RealRooted.Tactic.Examples.LiuWang.CurrentFactors
import RealRooted.Tactic.Examples.LiuWang.StrictPositiveLag
import RealRooted.Tactic.Examples.LiuWang.AffineHalfLine
import RealRooted.Tactic.Examples.LiuWang.PositiveAffine
import RealRooted.Tactic.Examples.LiuWang.InnerWindow
import RealRooted.Tactic.Examples.LiuWang.Interval
import RealRooted.Tactic.Examples.LiuWang.NegativeInnerWindow
import RealRooted.Tactic.Examples.LiuWang.StrictProducts
import RealRooted.Tactic.Examples.LiuWang.GenericNonpositive
import RealRooted.Tactic.Examples.LiuWang.NonpositiveGlobal
import RealRooted.Tactic.Examples.LiuWang.QuadraticSequences
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
  rr_lw_negative_monic_quadratic using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    discriminant := rr_lw_coeff_nonneg_term,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A181738`: automatic discriminant discharge for a monic
quadratic lag. -/
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
    leading_nonneg := rr_lw_coeff_nonneg_term,
    constant_nonneg := rr_lw_coeff_nonneg_term,
    discriminant := rr_lw_coeff_nonneg_term,
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

/-- One-step product lag with the root half-line supplied by nonnegative
coefficients. -/
example {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * q) * g) := by
  rr_lw_positive_X_mul_nonneg using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step scalar product lag with explicit scalar nonnegativity. -/
example {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X * q) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X * q) * g) := by
  rr_lw_positive_C_mul_X_mul_nonneg using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    coeff_nonneg := hc,
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

/-- The explicit scalar product-lag sequence endpoint uses a supplied
coefficient certificate. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_C_mul_X_mul_sequence using
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
    rr_eval_simp_arith
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

/-- Explicit active-coefficient `c_n t R_n(t)` shell with a supplied
coefficient certificate. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_c_tR_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the explicit `c_n t R_n(t)` alias. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (c n) * (X * (R n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_c_tR_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
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

section InferredSequenceCertificates

variable {P A B R Q : Nat → ℝ[X]}
variable (hbase : Prec (P 0) (P 1))
variable (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
variable (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
variable (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)

variable (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
variable (hrecB : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)

/-- A supplied recurrence fixes both hidden coefficient families before lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_nonpos_lag_sequence using recurrence := hrecB

/-- The inferred nonpositive-lag shell returns its full real-rooted endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports the splitting projection. -/
example : ∀ n : Nat, (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports the nonzero projection. -/
example : ∀ n : Nat, P n ≠ 0 := by rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

variable (_hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
variable (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
variable (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
variable (hrecR : ∀ n : Nat,
  P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
variable (hraw : ∀ n : Nat,
  P (n + 2) = A n * P (n + 1) + X * (R n * P n))

/-- The tR recurrence selects its factor family ahead of the decoy before lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by rr_lw_tR_lag_sequence using recurrence := hrecR

/-- The inferred tR shell returns its full real-rooted endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using recurrence := hrecR

/-- The inferred tR shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_lw_tR_lag_sequence_realrooted using recurrence := hrecR

/-- An ascribed normalizer fixes the hidden factor family before its tactic runs. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_tR_lag_sequence using recurrence :=
    (show ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * R n) * P n from
      fun n => by simpa only [mul_assoc] using hraw n)

end InferredSequenceCertificates

end Tactic
end RealRooted
