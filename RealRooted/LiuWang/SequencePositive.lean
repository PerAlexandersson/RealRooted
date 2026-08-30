import RealRooted.LiuWang.SequenceCore

/-!
# Positive-lag Liu--Wang sequence theorems

Sequence criteria for positive linear and affine lag coefficients.
-/

open Polynomial

namespace RealRooted

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => C (c n) * X) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_positive_t_lag_sequence
      hbase hpos hnonneg hc hrec hdeg_succ hno

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
  prec_lw_positive_t_lag_sequence
    (A := A) (c := fun _ => 1) hbase hpos hnonneg (fun _ => by norm_num)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_positive_X_lag_sequence hbase hpos hnonneg hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => C (c n) * X - C (a n)) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_sub_C_nonpos_of_nonneg_of_nonneg_of_nonpos
        (hc n) (ha n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_X_sub_C_lag_sequence
      hbase hpos hnonneg hc ha hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence
    (B := fun n => C (c n) * (C (a n) + X)) hbase hpos
    (fun n r hr =>
      eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg (hc n)
        (hroot_upper n r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_positive_affine_lag_sequence
      hbase hpos hc hroot_upper hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => C (c n) * (C (a n) + X)) hbase hpos
    (fun n hsource _r hr =>
      eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg (hc n)
        (root_le_neg_of_realrooted_of_shift_nonneg_coeffs
          hsource (hshift_nonneg n) hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
      hbase hpos hc hshift_nonneg hrec hdeg_succ hno

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
  prec_lw_positive_affine_lag_sequence
    (c := fun _ => 1) hbase hpos (fun _ => by norm_num) hroot_upper
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_add_X_lag_sequence hbase hpos hroot_upper hrec hdeg_succ hno

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
  prec_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
    (c := fun _ => 1) hbase hpos (fun _ => by norm_num) hshift_nonneg
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_add_X_lag_sequence_of_shift_nonneg_coeffs
      hbase hpos hshift_nonneg hrec hdeg_succ hno

end RealRooted
