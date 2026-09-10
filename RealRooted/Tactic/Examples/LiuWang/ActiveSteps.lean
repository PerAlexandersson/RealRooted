import RealRooted.Tactic.LiuWang.Step

/-!
# Liu--Wang active-step regression examples

Active-range, plateau-branch, direct-step, Favard, and normalization smoke tests
for the generalized Liu--Wang dispatcher.
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


end Tactic
end RealRooted
