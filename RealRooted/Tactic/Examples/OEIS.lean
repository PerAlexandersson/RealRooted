import RealRooted.Tactic.OEIS

/-!
# OEIS router examples

Smoke tests for OEIS-facing certificate routers.  These examples keep the
router honest: it only dispatches to existing tactic backends after the caller
names a concrete certificate branch.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by rr_oeis_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_oeis_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_oeis_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_oeis_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_oeis_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_oeis_coeff_all_term

/-- Root-bound row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, ∀ r, (P n).IsRoot r → r ≤ 0 := by
  rr_root_nonpos_sequence using
    realrooted := hrr,
    nonneg := hpnn

/-- Sign-at-roots row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, ∀ r, (P n).IsRoot r →
      (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_sequence using
    realrooted := hrr,
    nonneg := hpnn

/-- Affine-derivative row-family `Prec` exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat, Prec
      (C (c n) * P n + (1 - X) * (P n).derivative)
      (P n) := by
  rr_prec_affine_derivative_nonneg_sequence using
    splits := hsplits,
    degree_ge_one := hdeg,
    nonneg := hnn,
    scalar_gt_degree := hc

/-- Affine-derivative row-family real-rootedness exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat,
      C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 ∧
        (C (c n) * P n + (1 - X) * (P n).derivative).Splits := by
  rr_prec_affine_derivative_nonneg_sequence_realrooted using
    splits := hsplits,
    degree_ge_one := hdeg,
    nonneg := hnn,
    scalar_gt_degree := hc

/-- Affine-derivative row-family coefficient side goal exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).coeff (P n).natDegree =
        (c n - (P n).natDegree) * (P n).leadingCoeff := by
  rr_affine_deriv_coeff_sequence using degree_ge_one := hdeg

/-- Affine-derivative row-family degree side goal exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).natDegree =
        (P n).natDegree := by
  rr_affine_deriv_natDegree_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

/-- Affine-derivative row-family leading coefficient side goal via the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).leadingCoeff =
        (c n - (P n).natDegree) * (P n).leadingCoeff := by
  rr_affine_deriv_leadingCoeff_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

/-- Affine-derivative row-family nonzero side goal exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat, C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 := by
  rr_affine_deriv_ne_zero_sequence using
    nonzero := hne,
    degree_ge_one := hdeg,
    scalar_ne_degree := hc

/-- Favard row-family `Prec` exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

/-- Favard unit-lag Chebyshev row-family route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hstep : ∀ n : Nat, P (n + 2) = X * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Favard row-sign unit-lag route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat, P (n + 2) = -X * P (n + 1) - P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_const_row_sign_unit using
    alpha := 0,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Favard denominator-normalized affine row-family route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        C (1 - ((n : ℝ) + 3)) *
          (((C (((4 * (n.succ : ℝ) + 2) / ((n.succ : ℝ) + 1))) * X -
                C (0 : ℝ)) *
              P (n + 1) -
            C ((4 * (n.succ : ℝ)) / ((n.succ : ℝ) + 1)) * P n))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun _ => (0 : ℝ),
    beta := fun m => (4 * (m : ℝ)) / ((m : ℝ) + 1),
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

/-- Favard raw scalar-denominator route exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X - C (-1 : ℝ))
    (hraw : ∀ n : Nat,
      C (1 - ((n : ℝ) + 3)) * P (n + 2) =
        (C (6 - 4 * ((n : ℝ) + 3)) * X +
            C (3 - 2 * ((n : ℝ) + 3))) * P (n + 1) +
          C (-2 + ((n : ℝ) + 3)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun m => (4 * (m : ℝ) + 2) / ((m : ℝ) + 1),
    alpha := fun m => -((2 * (m : ℝ) + 1) / ((m : ℝ) + 1)),
    beta := fun m => (m : ℝ) / ((m : ℝ) + 1),
    raw_slope := fun n => 6 - 4 * ((n : ℝ) + 3),
    raw_const := fun n => 3 - 2 * ((n : ℝ) + 3),
    raw_lag := fun n => -2 + ((n : ℝ) + 3),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun n => 1 - ((n : ℝ) + 3),
    raw_recurrence := hraw

/-- Scalar-left `Prec` row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, Prec (C (a n) * F n) (G n) := by
  rr_prec_C_mul_left_sequence using
    prec := hFG,
    scalar_ne := ha

/-- Scalar-both `Prec` row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hFG : ∀ n : Nat, Prec (F n) (G n)) :
    ∀ n : Nat, Prec (C ((n : ℝ) + 1) * F n) (C ((n : ℝ) + 2) * G n) := by
  rr_prec_C_mul_both_sequence using
    prec := hFG

/-- Multiplication by `X` row-family real-rootedness exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, X * P n ≠ 0 ∧ (X * P n).Splits := by
  rr_X_mul_realrooted_sequence using
    realrooted := hP

/-- Coefficient-shape row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasLogConcaveCoeffs (P n) := by
  rr_coeff_shape using
    nonneg := hPnn,
    realrooted := hPrr

/-- Single-row coefficient-shape exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    HasUnimodalCoeffs (P n) := by
  rr_coeff_shape

/-- `fPolynomial` row-family real-rootedness transport exposed through the OEIS facade. -/
example {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hp : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, fPolynomial (d n) (P n) ≠ 0 ∧
      (fPolynomial (d n) (P n)).Splits := by
  rr_fPolynomial_sequence_realrooted using
    degree := hpdeg,
    realrooted := hp,
    nonneg := hpnn

/-- `fPolynomial` row-family `Prec` transport exposed through the OEIS facade. -/
example {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ n : Nat, (U n).natDegree ≤ d n)
    (hvd : ∀ n : Nat, (V n).natDegree ≤ d n)
    (hu_nonneg : ∀ n : Nat, HasNonnegCoeffs (U n))
    (hv_nonneg : ∀ n : Nat, HasNonnegCoeffs (V n))
    (hprec : ∀ n : Nat, Prec (U n) (V n)) :
    ∀ n : Nat, Prec (fPolynomial (d n) (U n)) (fPolynomial (d n) (V n)) := by
  rr_fPolynomial_sequence_prec using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg,
    prec := hprec

/-- Gamma-transform row-family real-rootedness exposed through the OEIS facade. -/
example {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hne : ∀ n : Nat, Γ n ≠ 0)
    (hsplits : ∀ n : Nat, (Γ n).Splits)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (Γ n)) :
    ∀ n : Nat, gammaTransform (d n) (Γ n) ≠ 0 ∧
      (gammaTransform (d n) (Γ n)).Splits := by
  rr_gamma_transform_sequence_realrooted_nonneg using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_nonneg := hnn

/-- Gamma row-family bridge exposed through the OEIS facade. -/
example {d : Nat → Nat} {P Γ : Nat → ℝ[X]}
    (hγdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hsym : ∀ n : Nat, IdTransform (d n) (P n) = P n)
    (hexp : ∀ n : Nat, IsGammaExpansion (d n) (P n) (Γ n)) :
    ∀ n : Nat,
      (((Γ n ≠ 0 ∧ (Γ n).Splits) ∧ HasRootsNonpos (Γ n)) ↔
        ((P n ≠ 0 ∧ (P n).Splits) ∧ HasRootsNonpos (P n))) := by
  rr_gamma_sequence_realrooted_iff using
    gamma_degree := hγdeg,
    polynomial_degree := hpdeg,
    symmetric := hsym,
    expansion := hexp

/-- Veronese-section row-family PF exit exposed through the OEIS facade. -/
example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      IsPolyaFreqSeq (veroneseSectionPolynomial (r n) (k n) (P n)).coeff := by
  rr_veronese_section_sequence_pf_coeff using
    pf_coeff := hpf,
    r_pos := hr,
    k_lt_r := hk

/-- Veronese pair-section row-family `Prec` exit exposed through the OEIS facade. -/
example {r i j : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hij : ∀ n : Nat, i n < j n)
    (hj : ∀ n : Nat, j n < 2 * r n) :
    ∀ n : Nat, Prec
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := by
  rr_veronese_pair_sequence_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    index_lt := hij,
    right_lt_bound := hj

/-- Compatibility derivative closure exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n)) :
    ∀ n : Nat, Compatible (F n).derivative (G n).derivative := by
  rr_compatible_sequence_derivative using compatible := h

/-- Compatibility-to-positive-combo bridge exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hf_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hg_pos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_compatible_sequence_to_pos_combo using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

/-- Common-interleaver list-family upgrade exposed through the OEIS facade. -/
example {FS : Nat → List ℝ[X]}
    (hrr : ∀ n : Nat, ∀ f ∈ FS n, f.Splits)
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hpair : ∀ n : Nat, PairwiseHasCommonInterleaver (FS n)) :
    ∀ n : Nat, HasCommonInterleaver (FS n) := by
  rr_common_interleaver_sequence_of_pairwise using
    member_splits := hrr,
    member_pos_lc := hpos,
    pairwise_common := hpair

/-- Common-interleaver list-family sum exit exposed through the OEIS facade. -/
example {FS : Nat → List ℝ[X]}
    (hcommon : ∀ n : Nat, HasCommonInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hne : ∀ n : Nat, FS n ≠ []) :
    ∀ n : Nat, (FS n).sum ≠ 0 ∧ (FS n).sum.Splits := by
  rr_common_interleaver_sum_sequence_realrooted using
    common_right := hcommon,
    member_pos_lc := hpos,
    nonempty := hne

/-- Direct Family I2 half-line branch, adjacent-`Prec` endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Direct Family I2 half-line branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Direct Family I2 half-line branch, Narayana-style zero-lag derivative
term. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {m : Nat}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (((n + 1 : Nat) : ℝ) + 2 * m + 2)⁻¹ *
              (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)) *
            (P (n + 1)).derivative +
          0 * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- `A358623`-style Wagner gap-lag branch, adjacent-`Prec` endpoint. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec,
    certificate := wagnerGap

/-- `A358623`-style Wagner gap-lag branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec,
    certificate := wagnerGap

/-- Denominator-normalized direct Family I2 branch. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Denominator-normalized direct Family I2 branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Denominator-normalized Wagner gap-lag branch. -/
example {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence_den using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec,
    certificate := wagnerGap

/-- Denominator-normalized Wagner gap-lag branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_den_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec,
    certificate := wagnerGap

/-- error: rr_i2_derivative_lag_sequence: jacobiOrHypergeom requires a classical coefficient-formula/root-location bridge -/
#guard_msgs in
example : True := by rr_i2_derivative_lag_sequence using certificate := jacobiOrHypergeom

/-- error: rr_i2_derivative_lag_sequence_realrooted: jacobiOrHypergeom requires a classical coefficient-formula/root-location bridge -/
#guard_msgs in
example : True := by rr_i2_derivative_lag_sequence_realrooted using certificate := jacobiOrHypergeom

/-- error: rr_i2_derivative_lag_sequence: transformNeeded requires an explicit transformed recurrence and root-window certificate -/
#guard_msgs in
example : True := by rr_i2_derivative_lag_sequence using certificate := transformNeeded

/-- error: rr_i2_derivative_lag_sequence_realrooted: transformNeeded requires an explicit transformed recurrence and root-window certificate -/
#guard_msgs in
example : True := by rr_i2_derivative_lag_sequence_realrooted using certificate := transformNeeded

/-- error: rr_i2_derivative_lag_sequence: vectorNeeded means the scalar derivative-lag wrapper is invalid; provide a vector/PF certificate -/
#guard_msgs in
example : True := by rr_i2_derivative_lag_sequence using certificate := vectorNeeded

/-- error: rr_i2_derivative_lag_sequence_realrooted: vectorNeeded means the scalar derivative-lag wrapper is invalid; provide a vector/PF certificate -/
#guard_msgs in
example : True := by rr_i2_derivative_lag_sequence_realrooted using certificate := vectorNeeded

/-- Family E positive `t`-lag router, exact-current `X` branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C ((n : ℝ) + 1) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentX

/-- Family E positive `t`-lag router, exact-current `X` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C (1 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentX

/-- Family E positive `t`-lag router, scalar-current `c_n X` branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C ((n : ℝ) + 2) * X) * P (n + 1) +
          (C ((n : ℝ) + 2) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentCX

/-- Family E positive `t`-lag router, scalar-current `c_n X` Prec endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C ((n : ℝ) + 2) * X) * P (n + 1) +
          (C ((n : ℝ) + 2) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentCX

/-- Family E positive `t`-lag router, current factor `1 + X` branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (n : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentOneAddX

/-- Family E positive `t`-lag router, current factor `1 + X` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C ((n : ℝ) + 4) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentOneAddX

/-- Family E positive `t`-lag router, `X * (1 - X)` lag branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xOneSubX

/-- Family E positive `t`-lag router, `X * (1 - X)` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xOneSubX

/-- Family E positive `t`-lag router, `X * (a_n - b_n * X)` lag branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xCSubCMulX

/-- Family E positive `t`-lag router, `X * (a_n - b_n * X)` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xCSubCMulX

/-- Family E positive `t`-lag router, `c_n * X * (a_n - b_n * X)` lag branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (C (1 : ℝ) * X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cMulXCSubCMulX

/-- Family E positive `t`-lag router, scaled affine-down lag real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (C (1 : ℝ) * X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cMulXCSubCMulX

/-- Family E plateau-safe positive `t`-lag router, Wagner-X branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    certificate := plateauX

/-- Family E plateau-safe positive `t`-lag router, Wagner-X Prec endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    certificate := plateauX

/-- Family E positive `t R_n(t)` lag router. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := tR

/-- Family E positive `c_n t R_n(t)` lag router with explicit coefficient. -/
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
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cTR

/-- Family E positive `c_n t R_n(t)` lag router with automatic coefficient. -/
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
    ∀ n : Nat, (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cTRAuto

/-- Product-exit router, identity branch. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := identity

/-- Product-exit router, root-zero branch with a projection endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := rootZero

/-- Product-exit router, automatic one-step branch for constant rows. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-exit router, automatic one-step branch for a zero-root factor. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-exit router, cutoff identity branch. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := identity

/-- Product-exit router, cutoff automatic zero-root branch. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_exit_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-exit router, period-two branch. -/
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    recurrence := hrec,
    certificate := periodTwo

/-- Product-exit router, period-two branch from a cutoff row. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N + 1 → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 2) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := periodTwo

/-- Product-factor recurrence router with a supplied factor certificate. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec,
    certificate := suppliedFactor

/-- Product-factor router with a supplied factor certificate from a cutoff row. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    recurrence := hrec,
    certificate := suppliedFactor

/-- Product-factor recurrence router, automatic affine-slope certificate. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := affineAuto

/-- Product-factor recurrence router, constant-first affine factor. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec,
    certificate := constFirstAffine

/-- Product-factor router, affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := affine

/-- Product-factor router, automatic affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := affineAuto

/-- Product-factor router, constant-first affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffine

/-- Product-factor router, automatic constant-first affine cutoff branch. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (t n) + C ((n : ℝ) + 1) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffineAuto

/-- Product-factor recurrence router, unit-linear factor. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := xAddC

/-- Product-factor router, unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := xAddC

/-- Product-factor router, constant-first unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = (C (t n) + X) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := cAddX

/-- Product-factor recurrence router, automatic unit-linear factor. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor router, automatic unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches positive affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches constant-first affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = P n * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor cutoff auto reaches constant-first affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (2 : ℝ) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor recurrence router, repeated root-zero factor. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := rootZeroPow

/-- Product-factor router, repeated root-zero factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := rootZeroPow

/-- Product-factor router, powered unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := xAddCPow

/-- Product-factor router, powered constant-first factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := cAddXPow

/-- Product-factor recurrence router, automatic repeated root-zero factor. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor router, automatic root-zero-power factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches powered positive affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor cutoff auto reaches constant-first powered affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (2 : ℝ) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches positive scalar factors. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor cutoff auto reaches positive scalar-power factors. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor recurrence router, automatic scalar certificate. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := scalarAuto

/-- Product-factor router, scalar factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * C (a n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    recurrence := hrec,
    certificate := scalar

/-- Product-factor router, automatic scalar factor from a cutoff row. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := scalarAuto

/-- Product-factor recurrence router, scalar-power factor. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (a n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    recurrence := hrec,
    certificate := scalarPow

/-- Product-factor router, scalar-power factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (a n) : ℝ[X]) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    recurrence := hrec,
    certificate := scalarPow

/-- Product-factor router, automatic scalar-power factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := scalarPowAuto

/-- Product-factor recurrence router, automatic powered affine factor. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := affinePowAuto

/-- Product-factor router, powered affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (s n) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := affinePow

/-- Product-factor router, automatic powered affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := affinePowAuto

/-- Product-factor recurrence router, constant-first powered affine factor. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec :
      ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec,
    certificate := constFirstAffinePow

/-- Product-factor router, constant-first powered affine cutoff branch. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffinePow

/-- Product-factor router, automatic constant-first powered affine cutoff. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n →
        P (n + 1) = (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffinePowAuto

/-- Product-formula router, finite product of linear factors. -/
example {P : Nat → ℝ[X]} {roots : Nat → Nat → ℝ}
    (hroot : ∀ n : Nat,
      P n = ∏ j ∈ Finset.range n, (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_formula_sequence using
    formula := hroot,
    certificate := finiteLinearProduct

/-- Product-formula router, scalar finite product of linear factors. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_formula_sequence using
    scalar_ne_zero := hc,
    root_grid := hroot,
    certificate := scalarFiniteLinearProduct

/-- J1 factorable-row router, scalar finite product of linear factors. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, (P n).Splits := by
  rr_j1_factorable_sequence_realrooted using
    scalar_ne_zero := hc,
    root_grid := hroot,
    certificate := finiteLinearProduct

/-- J1 gap-3 reciprocal router from a real-rooted model family. -/
example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, R n ≠ 0 ∧ (R n).Splits)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_j1_gap3_reciprocal_sequence_realrooted using
    model_realrooted := hmodel,
    degree := hdegree,
    reciprocal := hreciprocal,
    certificate := modelRealRooted

/-- J1 gap-3 reciprocal router from a PF-polynomial model family. -/
example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, IsPFPolynomial (R n))
    (hmodel_ne : ∀ n : Nat, R n ≠ 0)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_j1_gap3_reciprocal_sequence_realrooted using
    model_pf := hmodel,
    model_ne := hmodel_ne,
    degree := hdegree,
    reciprocal := hreciprocal,
    certificate := modelPF

/-- Linear-power interlacing exit exposed through the OEIS facade. -/
example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_interlaces_linear_pow using
    const := 2,
    slope := 3,
    slope_pos := rr_side_pos_term,
    index := n

/-- Linear-power nonnegative-coefficient exit exposed through the OEIS facade. -/
example (n : Nat) :
    HasNonnegCoeffs ((C (2 : ℝ) + C 3 * X) ^ n) := by
  rr_hasNonnegCoeffs_linear_pow using
    a_nonneg := rr_side_nonneg_term,
    b_nonneg := rr_side_nonneg_term,
    index := n

/-- Operator-preserver row-family exit exposed through the OEIS facade. -/
example {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {F G : Nat → ℝ[X]}
    (hT : PreservesRealRootedOrZero T)
    (hfg : ∀ n : Nat, Prec (F n) (G n)) :
    ∀ n : Nat, Prec0 (T (F n)) (T (G n)) ∨ Prec0 (T (G n)) (T (F n)) := by
  rr_operator_prec0_sequence_up_to_order using
    preserves := hT,
    prec := hfg

/-- All-combinations derivative row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]}
    (hall : ∀ n : Nat, AllComboRealRooted (F n) (G n)) :
    ∀ n : Nat, AllComboRealRooted (F n).derivative (G n).derivative := by
  rr_all_combo_sequence_derivative using all_combo := hall

/-- Derivative proper-position row-family exit exposed through the OEIS
facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree) :
    ∀ n : Nat, Prec (P n).derivative (P n) := by
  rr_derivative_sequence_prec using
    splits := hP,
    degree_two := hdeg

/-- Derivative nonnegative-coefficient row-family exit exposed through the
OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n).derivative := by
  rr_nonneg_coeffs_sequence_derivative using nonneg_coeffs := hP

/-- Magnitude-dominated row-family interlacing exit exposed through the OEIS
facade. -/
example {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hG1F : ∀ n : Nat, Interlaces (G1 n) (F n))
    (hG1_pos : ∀ n : Nat, HasPosLeadingCoeff (G1 n))
    (hF_pos : ∀ n : Nat,
      HasPosLeadingCoeff (A n * F n + B1 n * G1 n + B2 n * G2 n))
    (hdeg_lo : ∀ n : Nat,
      (F n).natDegree ≤ (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree)
    (hdeg_hi : ∀ n : Nat,
      (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree ≤
        (F n).natDegree + 1)
    (hcert : ∀ n : Nat, ∀ r, (F n).IsRoot r →
      (B1 n).eval r * ((G1 n).eval r) ^ 2 +
        (B2 n).eval r * ((G2 n).eval r * (G1 n).eval r) < 0) :
    ∀ n : Nat, Prec (F n) (A n * F n + B1 n * G1 n + B2 n * G2 n) := by
  rr_magnitude_dominated_sequence using
    interlaces := hG1F,
    interlacer_pos_lc := hG1_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    certificate := hcert

/-- All-combinations to positive-combinations row-family exit exposed through
the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hall : ∀ n : Nat, AllComboRealRooted (F n) (G n))
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hdeg : ∀ n : Nat, (F n).natDegree = (G n).natDegree) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_all_combo_sequence_to_pos_combo_sameDegree using
    all_combo := hall,
    left_pos_lc := hF,
    right_pos_lc := hG,
    degree_eq := hdeg

/-- Positive-combination row-family exit from proper position exposed through
the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, Prec (F n) (G n))
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_pos_combo_sequence_of_prec using
    prec := hfg,
    left_pos_lc := hF,
    right_pos_lc := hG

/-- Positive-combination sum real-rooted row-family exit exposed through the
OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n)) :
    ∀ n : Nat, F n + G n ≠ 0 ∧ (F n + G n).Splits := by
  rr_pos_combo_sequence_add_realrooted using pos_combo := hfg

/-- Weighted Wagner-sum row-family common-left exit exposed through the OEIS
facade. -/
example {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ n : Nat, WeightedCompatibleLeft (H n) (L n)) :
    ∀ n : Nat, Prec (H n) (weightedSum (L n)) := by
  rr_weighted_sum_sequence_left_prec using compatible := hl

/-- Unweighted Wagner-sum row-family common-right exit exposed through the OEIS
facade. -/
example {L : Nat → List ℝ[X]} {H : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, ∀ p ∈ L n, Prec p (H n))
    (hpos : ∀ n : Nat, ∀ p ∈ L n, HasPosLeadingCoeff p)
    (hne : ∀ n : Nat, L n ≠ []) :
    ∀ n : Nat, Prec (L n).sum (H n) := by
  rr_sum_sequence_right_prec using
    all_prec := hprec,
    terms_pos_lc := hpos,
    nonempty := hne

/-- Staircase-sum row-family real-rootedness exit exposed through the OEIS
facade. -/
example {L : Nat → List ℝ[X]} {M : Nat → Nat}
    (hL : ∀ n : Nat, IsInterlacingSeqNonneg (L n))
    (hM : ∀ n : Nat, M n < (L n).length) :
    ∀ n : Nat, staircaseSum (L n) (M n) ≠ 0 ∧
      (staircaseSum (L n) (M n)).Splits := by
  rr_staircaseSum_sequence_realrooted using
    interlacing_nonneg := hL,
    index_lt := hM

/-- Root-count degree side-goal row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]} {μ : Nat → ℝ}
    (hμ : ∀ n : Nat, μ n ≠ 0)
    (hdeg : ∀ n : Nat, (F n).natDegree < (G n).natDegree) :
    ∀ n : Nat, (F n + C (μ n) * G n).natDegree = (G n).natDegree := by
  rr_natDegree_add_C_mul_lt_sequence using
    parameter_ne_zero := hμ,
    degree_lt := hdeg

/-- Root-count same-sign nonroot row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]} {β x : Nat → ℝ}
    (hβ0 : ∀ n : Nat, 0 ≤ β n)
    (hβ1 : ∀ n : Nat, β n ≤ 1)
    (hprod : ∀ n : Nat, 0 < (F n).eval (x n) * (G n).eval (x n)) :
    ∀ n : Nat, ¬ (C (1 - β n) * F n + C (β n) * G n).IsRoot (x n) := by
  rr_closedSegment_not_isRoot_same_sign_sequence using
    parameter_nonneg := hβ0,
    parameter_le_one := hβ1,
    eval_product_pos := hprod

/-- Root-count comparison row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0)
    (hG : ∀ n : Nat, G n ≠ 0)
    (hbound : ∀ n : Nat, ∀ x : ℝ, (F n).eval x ≠ 0 → (G n).eval x ≠ 0 →
      (((F n).roots.filter (x < ·)).card : ℤ) -
          ((G n).roots.filter (x < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x < ·)).card : ℤ) -
          ((F n).roots.filter (x < ·)).card ≤ 1) :
    ∀ n : Nat, ∀ x : ℝ,
      (((F n).roots.filter (x < ·)).card : ℤ) -
          ((G n).roots.filter (x < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x < ·)).card : ℤ) -
          ((F n).roots.filter (x < ·)).card ≤ 1 := by
  rr_rootCountAbove_diff_le_one_nonRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

/-- Interval root-count row-family transport exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ n : Nat, a n ≤ b n)
    (hno : ∀ n : Nat, ∀ x, a n < x → x ≤ b n → ¬ (P n).IsRoot x) :
    ∀ n : Nat,
      ((P n).roots.filter (· ≤ a n)).card =
          ((P n).roots.filter (· ≤ b n)).card ∧
        ((P n).roots.filter (a n < ·)).card =
          ((P n).roots.filter (b n < ·)).card ∧
          ((P n).roots.filter (fun x => a n < x ∧ x ≤ b n)).card = 0 := by
  rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    no_roots := hno

/-- Interval root-count comparison transfer exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ n : Nat, a n ≤ b n)
    (hF : ∀ n : Nat, ∀ x, a n < x → x ≤ b n → ¬ (F n).IsRoot x)
    (hG : ∀ n : Nat, ∀ x, a n < x → x ≤ b n → ¬ (G n).IsRoot x)
    (hle : ∀ n : Nat,
      (((F n).roots.filter (· ≤ a n)).card : ℤ) -
          ((G n).roots.filter (· ≤ a n)).card ≤ 1 ∧
        (((G n).roots.filter (· ≤ a n)).card : ℤ) -
          ((F n).roots.filter (· ≤ a n)).card ≤ 1)
    (hgt : ∀ n : Nat,
      (((F n).roots.filter (a n < ·)).card : ℤ) -
          ((G n).roots.filter (a n < ·)).card ≤ 1 ∧
        (((G n).roots.filter (a n < ·)).card : ℤ) -
          ((F n).roots.filter (a n < ·)).card ≤ 1) :
    ∀ n : Nat,
      ((((F n).roots.filter (· ≤ b n)).card : ℤ) -
          ((G n).roots.filter (· ≤ b n)).card ≤ 1 ∧
        (((G n).roots.filter (· ≤ b n)).card : ℤ) -
          ((F n).roots.filter (· ≤ b n)).card ≤ 1) ∧
        ((((F n).roots.filter (b n < ·)).card : ℤ) -
            ((G n).roots.filter (b n < ·)).card ≤ 1 ∧
          (((G n).roots.filter (b n < ·)).card : ℤ) -
            ((F n).roots.filter (b n < ·)).card ≤ 1) := by
  rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    lower_source_bound := hle,
    upper_source_bound := hgt

/-- Succ-degree endpoint root-count row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG_pos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hFG : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hsucc : ∀ n : Nat, (G n).natDegree = (F n).natDegree + 1) :
    ∀ n : Nat, F n ≠ 0 ∧ (F n).roots.card = (F n).natDegree := by
  rr_left_ne_zero_card_roots_succDegree_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    succ_degree := hsucc

/-- Same-degree root-count row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG_pos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hFG : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hdeg : ∀ n : Nat, (G n).natDegree = (F n).natDegree)
    (hxG : ∀ n : Nat, ¬ (G n).IsRoot (x n))
    (hno : ∀ n : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F n + C μ * G n).IsRoot (x n)) :
    ∀ n : Nat,
      (((F n).roots.filter (x n < ·)).card : ℤ) -
          ((G n).roots.filter (x n < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x n < ·)).card : ℤ) -
          ((F n).roots.filter (x n < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_rightFamily_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    right_not_root := hxG,
    no_right_family_roots := hno

/-- Low-degree same-degree root-count certificate exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG_pos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hFnn : ∀ n : Nat, HasNonnegCoeffs (F n))
    (hGnn : ∀ n : Nat, HasNonnegCoeffs (G n))
    (hFG : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hdeg : ∀ n : Nat, (G n).natDegree = (F n).natDegree)
    (hno : ∀ n : Nat, ∀ r, (F n).IsRoot r → ¬ (G n).IsRoot r)
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ 2) :
    ∀ n : Nat,
      (((F n).roots.filter (x n < ·)).card : ℤ) -
          ((G n).roots.filter (x n < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x n < ·)).card : ℤ) -
          ((F n).roots.filter (x n < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

/-- Euler-operator PF row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, IsPFPolynomial (thetaPlusOne (P n)) := by
  rr_thetaPlusOne_sequence_pf using pf := hP

/-- Iterated Euler-operator proper-position row-family exit exposed through
the OEIS facade. -/
example {l : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n))
    (hPQ : ∀ n : Nat, Prec0 (P n) (Q n)) :
    ∀ n : Nat,
      Prec0 (iterateThetaPlusOne (l n) (P n)) (iterateThetaPlusOne (l n) (Q n)) := by
  rr_iterateThetaPlusOne_sequence_prec0 using
    index := l,
    left_pf := hP,
    right_pf := hQ,
    prec0 := hPQ

/-- Derivative-shift row-family real-rootedness exit exposed through the OEIS
facade. -/
example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ n : Nat, 0 < eps n)
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat, (TDeriv (eps n) (P n)).Splits := by
  rr_TDeriv_sequence_splits using
    eps_pos := heps,
    splits := hP

/-- Iterated derivative-shift row-family proper-position exit exposed through
the OEIS facade. -/
example {eps : Nat → ℝ} {K : Nat → Nat} {P : Nat → ℝ[X]}
    (heps : ∀ n : Nat, 0 < eps n)
    (hP0 : ∀ n : Nat, P n ≠ 0)
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat,
      Prec (iterateTDeriv (eps n) (K n) (P n))
        (iterateTDeriv (eps n) (K n + 1) (P n)) := by
  rr_iterateTDeriv_sequence_prec_succ using
    eps_pos := heps,
    nonzero := hP0,
    splits := hP,
    index := K

/-- Wagner common-left addition row-family exit exposed through the OEIS
facade. -/
example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n)) :
    ∀ n : Nat, Prec (H n) (F n + G n) := by
  rr_wagner_common_left_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    common_interlaces_left := hHF,
    common_interlaces_right := hHG

/-- PF-polynomial product row-family exit exposed through the OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n)) :
    ∀ n : Nat, IsPFPolynomial (P n * Q n) := by
  rr_pf_sequence_mul using
    left_pf := hP,
    right_pf := hQ

/-- PF-polynomial real-rootedness row-family exit exposed through the OEIS
facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_pf_sequence_zero_or_splits using pf := hP

/-- Hadamard PF exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  rr_hadamard_pf using
    left_pf := hp,
    right_pf := hq

/-- Hadamard nonnegative real-rootedness exit exposed through the OEIS
facade. -/
example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0 := by
  rr_hadamard_nonneg_realrooted using
    left_nonneg := hpnn,
    right_nonneg := hqnn,
    left_realrooted := hp,
    right_realrooted := hq

/-- Hadamard nonnegative-coefficient exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  rr_hadamard_nonneg_coeffs using
    left_nonneg := hpnn,
    right_nonneg := hqnn

/-- Hadamard PF row-family exit exposed through the OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n)) :
    ∀ n : Nat, IsPFPolynomial (hadamardProduct (P n) (Q n)) := by
  rr_hadamard_sequence_pf using
    left_pf := hP,
    right_pf := hQ

/-- Hadamard nonnegative real-rootedness row-family exit exposed through the
OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQnn : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hQ : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits) :
    ∀ n : Nat,
      (hadamardProduct (P n) (Q n) = 0 ∨
          (hadamardProduct (P n) (Q n)).Splits) ∧
        HasNonnegCoeffs (hadamardProduct (P n) (Q n)) ∧
        ∀ r ∈ (hadamardProduct (P n) (Q n)).roots, r ≤ 0 := by
  rr_hadamard_sequence_nonneg_realrooted using
    left_nonneg := hPnn,
    right_nonneg := hQnn,
    left_realrooted := hP,
    right_realrooted := hQ

/-- Hadamard nonnegative-coefficient row-family exit exposed through the OEIS
facade. -/
example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQnn : ∀ n : Nat, HasNonnegCoeffs (Q n)) :
    ∀ n : Nat, HasNonnegCoeffs (hadamardProduct (P n) (Q n)) := by
  rr_hadamard_sequence_nonneg_coeffs using
    left_nonneg := hPnn,
    right_nonneg := hQnn

/-- Hadamard proper-position row-family exit exposed through the OEIS facade. -/
example {F G P Q : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasNonnegCoeffs (F n))
    (hG : ∀ n : Nat, HasNonnegCoeffs (G n))
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (hPQ : ∀ n : Nat, Prec (P n) (Q n)) :
    ∀ n : Nat,
      Prec0 (hadamardProduct (F n) (P n)) (hadamardProduct (G n) (Q n)) := by
  rr_hadamard_sequence_prec0 using
    first_left_nonneg := hF,
    first_right_nonneg := hG,
    second_left_nonneg := hP,
    second_right_nonneg := hQ,
    first_prec := hFG,
    second_prec := hPQ

/-- Schur--Szego row-family exit exposed through the OEIS facade. -/
example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ n : Nat, IsPFPolynomial (F n))
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hPdeg : ∀ n : Nat, (P n).natDegree ≤ N n)
    (hPsplits : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat,
      schurSzegoComp (N n) (F n) (P n) = 0 ∨
        (schurSzegoComp (N n) (F n) (P n)).Splits := by
  rr_schur_szego_sequence using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits

/-- Schur--Szego row-family nonzero endpoint exposed through the OEIS facade. -/
example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ n : Nat, IsPFPolynomial (F n))
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hPdeg : ∀ n : Nat, (P n).natDegree ≤ N n)
    (hPsplits : ∀ n : Nat, (P n).Splits)
    (hout : ∀ n : Nat, schurSzegoComp (N n) (F n) (P n) ≠ 0) :
    ∀ n : Nat, (schurSzegoComp (N n) (F n) (P n)).Splits := by
  rr_schur_szego_sequence_splits using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits,
    nonzero := hout

/-- Schur--Szego low-degree PF-factor exit exposed through the OEIS facade. -/
example {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_two using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

/-- Schur--Szego cubic numerator route exposed through the OEIS facade. -/
example {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum,
    nonzero := hout

/-- Jensen nonnegative-coefficient row-family exit exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k) :
    ∀ n : Nat, HasNonnegCoeffs (jensenPolynomial (N n) (Gamma n)) := by
  rr_jensen_sequence_nonneg using
    level := N,
    sequence_nonneg := hGamma

/-- Jensen PF row-family exit from finite multipliers exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k)
    (hmult : ∀ n : Nat, IsFiniteMultiplierSequence (N n) (Gamma n)) :
    ∀ n : Nat, IsPFPolynomial (jensenPolynomial (N n) (Gamma n)) := by
  rr_jensen_sequence_pf_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

/-- Finite PF-multiplier row-family conversion exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k)
    (hmult : ∀ n : Nat, IsFiniteMultiplierSequence (N n) (Gamma n)) :
    ∀ n : Nat, IsFinitePFMultiplierSequence (N n) (Gamma n) := by
  rr_finite_pf_multiplier_sequence_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

/-- Hermite--Biehler statement exit exposed through the OEIS facade. -/
example :
    hermiteBiehlerForwardPosStatement := by
  rr_hermite_biehler_forward_pos_statement

/-- Hermite--Biehler odd/even Hurwitz row-family exit exposed through the OEIS
facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat, IsHurwitzStable (oddEvenPolynomial (P n) (Q n)) := by
  rr_hermite_biehler_odd_even_hurwitz_stable_sequence using
    odd_nonneg := hP,
    even_nonneg := hQ,
    stable := hstable

/-- Hermite--Poulain row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits) :
    ∀ n : Nat,
      RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          = 0 ∨
        (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator
          (F n) (G n)).Splits := by
  rr_hermite_poulain_sequence using
    operator := hF,
    input := hG

/-- Kurtz coefficient-criterion exit exposed through the OEIS facade. -/
example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

/-- Kurtz row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Challenges.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

/-- Narayana polynomial exit exposed through the OEIS facade. -/
example {m n : ℕ} :
    (narayanaPolynomial m n).Splits := by
  rr_narayana_polynomial_splits using
    parameter := m,
    degree := n

/-- Narayana row-family exit exposed through the OEIS facade. -/
example {m d : Nat → ℕ} :
    ∀ n : Nat, (narayanaPolynomial (m n) (d n)).Splits := by
  rr_narayana_polynomial_sequence_splits using
    parameter := m,
    degree := d

/-- Second-derivative shell exposed through the OEIS facade. -/
example {P U V : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha_ne : ∀ n : Nat, a n ≠ 0)
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative))
    (hV_nonpos : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_plus_derivative_sequence using
    outer := a,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_nonzero := ha_ne,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    coeff_nonpos := hV_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

/-- Product-parity router, automatic scalar step with supplied factor. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenFactorAuto

/-- Product-parity router, supplied factor with cutoff. -/
example {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    factor_realrooted := hfactor,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenFactor

/-- Product-parity router, automatic scalar supplied factor with cutoff. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenFactorAuto

/-- Product-parity router, automatic scalar then unit-linear step. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hlinear : ∀ n : Nat,
      P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenXAddCAuto

/-- Product-parity router, constant-first unit-linear step. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenCAddX

/-- Product-parity router, unit-linear step with cutoff. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenXAddC

/-- Product-parity router, automatic scalar constant-first unit-linear cutoff. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = P (2 * n) * C (2 * (n : ℝ) + 1))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenCAddXAuto

/-- Product-parity router, automatic scalar then root-zero powers. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenRootZeroPowAuto

/-- Product-parity router, powered unit-linear step. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = (X + C (b n)) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenXAddCPow

/-- Product-parity router, automatic scalar then powered constant-first step. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenCAddXPowAuto

/-- Product-parity router, root-zero powers with cutoff. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = X ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenRootZeroPow

/-- Product-parity router, powered unit-linear step with cutoff. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenXAddCPowAuto

/-- Product-parity router, powered constant-first step with cutoff. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (C (b n) + X) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenCAddXPow

/-- Product-parity lift router, odd rows are scalar multiples of `X` times
the even quotient. -/
example {P Q : Nat → ℝ[X]} {a : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (heven : ∀ n : Nat, P (2 * n) = Q n)
    (hodd : ∀ n : Nat, P (2 * n + 1) = C (a n) * X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_lift_sequence using
    even_realrooted := hquot,
    scalar_ne := ha,
    even_factorization := heven,
    odd_factorization := hodd,
    certificate := scalarXOdd

/-- Endpoint-pair router, sum-then-`X` branch. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, Prec (A n) (B n) := by
  rr_endpoint_pair_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop,
    certificate := sumThenX

/-- Endpoint-pair router, real-rootedness endpoint for the reversed branch. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  rr_endpoint_pair_sequence_realrooted using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    certificate := xThenSum

/-- Endpoint-pair lift router, sum-then-`X` branch. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1)))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_endpoint_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop,
    even_factorization := hrowA,
    odd_factorization := hrowB,
    certificate := sumThenX

/-- Endpoint-pair lift router, reversed branch. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mB n) * B n) :
    ∀ n : Nat, (P n).Splits := by
  rr_endpoint_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    even_factorization := hrowA,
    odd_factorization := hrowB,
    certificate := xThenSum

/-- Endpoint-pair lift router, reversed branch with swapped row quotient. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowB : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mB n) * B n)
    (hrowA : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mA n) * A n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_endpoint_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    even_factorization := hrowB,
    odd_factorization := hrowA,
    certificate := xThenSumSwapped

/-- Product-lift router with a supplied factor certificate. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    factorization := hrow,
    certificate := suppliedFactor

/-- Product-lift router with supplied factor and cutoff. -/
example {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    cutoff := N,
    factorization := hrow,
    certificate := suppliedFactor

/-- Product-lift router, repeated root-zero factor. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := rootZeroPow

/-- Product-lift router, root-zero factor with cutoff. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := rootZero

/-- Product-lift router, root-zero powers with cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := rootZeroPow

/-- Product-lift router, row-wise unit linear factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := xAddC

/-- Product-lift router, row-wise unit linear factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := xAddC

/-- Product-lift router, row-wise unit linear power. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := rowXAddCPow

/-- Product-lift router, automatic scalar certificate. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := scalarAuto

/-- Product-lift router, automatic affine-slope certificate. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := affineAuto

/-- Product-lift router, constant-first unit linear factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := cAddX

/-- Product-lift router, constant-first unit linear factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := cAddX

/-- Product-lift router, fixed unit-linear power. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (1 : ℝ)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := fixedXAddCPow

/-- Product-lift router, row-wise constant-first unit-linear power. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := cAddXPow

/-- Product-lift router, scalar-power factor. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    scalar_ne := hc,
    factorization := hrow,
    certificate := scalarPow

/-- Product-lift router, automatic scalar-power factor. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := scalarPowAuto

/-- Product-lift router, scalar factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = C (c n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    scalar_ne := hc,
    cutoff := N,
    factorization := hrow,
    certificate := scalar

/-- Product-lift router, automatic scalar factor with cutoff. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * C ((n : ℝ) + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := scalarAuto

/-- Product-lift router, scalar-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    scalar_ne := hc,
    cutoff := N,
    factorization := hrow,
    certificate := scalarPow

/-- Product-lift router, automatic scalar-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := scalarPowAuto

/-- Product-lift router, affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := affine

/-- Product-lift router, automatic affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := affineAuto

/-- Product-lift router, constant-first affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffine

/-- Product-lift router, automatic constant-first affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffineAuto

/-- Product-lift router, constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow,
    certificate := constFirstAffine

/-- Product-lift router, automatic constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := constFirstAffineAuto

/-- Product-lift router, powered affine factor. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow,
    certificate := affinePow

/-- Product-lift router, automatic powered affine factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := affinePowAuto

/-- Product-lift router, powered constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow,
    certificate := constFirstAffinePow

/-- Product-lift router, automatic powered constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := constFirstAffinePowAuto

/-- Product-lift router, fixed unit-linear power with cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (1 : ℝ)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := fixedXAddCPow

/-- Product-lift router, row-wise unit-linear power with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := rowXAddCPow

/-- Product-lift router, constant-first unit-linear power with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := cAddXPow

/-- Product-lift router, affine-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := affinePow

/-- Product-lift router, automatic affine-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := affinePowAuto

/-- Product-lift router, powered constant-first affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffinePow

/-- Product-lift router, automatic powered constant-first affine cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffinePowAuto

/-- Product-lift router, automatic certificate selection. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := auto

/-- Product-lift auto router reaches constant-first affine factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := auto

/-- Product-lift auto router reaches powered positive affine factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := auto

/-- Product-lift auto router reaches positive scalar-power factors. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := auto

/-- Product-lift router, automatic certificate selection after a cutoff. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := auto

/-- Product-lift cutoff auto reaches constant-first powered affine factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C (2 : ℝ) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := auto

/-- Product-lift cutoff auto reaches positive scalar-power factors. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := auto

/-- Family G negative-lag router, shifted-square branch. -/
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
  rr_g_negative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeSquare

/-- Family G denominator-normalized negative-square branch. -/
example {P : Nat → ℝ[X]} {A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) * (A n * P (n + 1)) +
          C ((n : ℝ) + 1) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_g_negative_lag_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeSquare

/-- Family G denominator-normalized negative-square real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) * (A n * P (n + 1)) +
          C ((n : ℝ) + 1) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeSquare

/-- Family G negative-lag router, monic quadratic real-rooted endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeMonicQuadratic

/-- Family G negative-lag router, non-monic quadratic branch. -/
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
  rr_g_negative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeQuadratic

/-- Family G denominator-normalized non-monic quadratic branch. -/
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_g_negative_lag_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeQuadratic

/-- Family G denominator-normalized non-monic quadratic real-rooted endpoint. -/
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
  rr_g_negative_lag_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeQuadratic

/-- Family G negative-lag router, global nonpositive branch. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := globalNonpos

/-- Family G denominator-normalized global nonpositive branch. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) *
          (A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_g_negative_lag_sequence_den_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := globalNonpos

end Tactic
end RealRooted
