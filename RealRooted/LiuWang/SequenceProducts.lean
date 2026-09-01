import RealRooted.LiuWang.SequenceIntervals

/-!
# Product-lag Liu--Wang sequence theorems

Sequence criteria for factored lags and fixed current-row coefficients.
-/

open Polynomial

namespace RealRooted

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => X * Q n) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr)
        (hQ_nonneg n r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_positive_X_mul_lag_sequence
      hbase hpos hnonneg hQ_nonneg hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => C (c n) * X * Q n) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        (hc n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr)
        (hQ_nonneg n r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_positive_C_mul_X_mul_lag_sequence
      hbase hpos hnonneg hc hQ_nonneg hrec hdeg_succ hno

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
  prec_lw_positive_X_mul_lag_sequence
    hbase hpos hnonneg hR_nonneg hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_tR_lag_sequence hbase hpos hnonneg hR_nonneg hrec hdeg_succ hno

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
  prec_lw_positive_C_mul_X_mul_lag_sequence
    hbase hpos hnonneg hc hR_nonneg hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_c_tR_lag_sequence hbase hpos hnonneg hc hR_nonneg hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun _ => X * (1 - X)) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_one_sub_X_nonpos_of_nonpos
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_X_mul_one_sub_X_lag_sequence hbase hpos hnonneg hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => X * (C (a n) - C (b n) * X)) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_C_sub_C_mul_X_nonpos_of_nonneg_of_nonneg_of_nonpos
        (ha n) (hb n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_X_mul_C_sub_C_mul_X_lag_sequence
      hbase hpos hnonneg ha hb hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => C (c n) * X * (C (a n) - C (b n) * X)) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_mul_C_sub_C_mul_X_nonpos
        (hc n) (ha n) (hb n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_X_mul_C_sub_C_mul_X_lag_sequence
      hbase hpos hnonneg hc ha hb hrec hdeg_succ hno

/-- Sequence-level positive `t`-lag induction when the current-row coefficient
is also a scalar multiple of `X`.  This packages the OEIS shapes
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
  prec_lw_positive_t_lag_sequence
    (A := fun n => C (a n) * X) hbase hpos hnonneg hc hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_current_CX_positive_t_lag_sequence
      hbase hpos hnonneg hc hrec hdeg_succ hno

/-- Sequence-level positive `t`-lag induction for the exact current factor
`X`.  This avoids normalizing unit-current OEIS recurrences to
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
  prec_lw_positive_t_lag_sequence
    (A := fun _ => X) hbase hpos hnonneg hc hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_current_X_positive_t_lag_sequence hbase hpos hnonneg hc hrec hdeg_succ hno

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
  prec_lw_positive_t_lag_sequence
    (A := fun _ => (1 + X : ℝ[X])) hbase hpos hnonneg hc hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_current_one_add_X_positive_t_lag_sequence
      hbase hpos hnonneg hc hrec hdeg_succ hno


end RealRooted
