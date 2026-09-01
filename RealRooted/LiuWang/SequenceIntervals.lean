import RealRooted.LiuWang.SequencePositive

/-!
# Interval-controlled Liu--Wang sequence theorems

Sequence criteria whose lag sign is certified on a root interval.
-/

open Polynomial

namespace RealRooted

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
  prec_lw_nonpos_lag_sequence_of_inductive_nonpos hbase hpos
    (fun n hsource r hr =>
      hB_nonpos n r hr (hroot_lower n r hr)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hroot_lower hB_nonpos hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun _ => X * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi => eval_X_mul_one_add_X_nonpos_of_mem_Icc hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => C (c n) * X * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc (hc n) hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun _ => X * (1 - X) * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi =>
      eval_X_mul_one_sub_X_mul_one_add_X_nonpos_of_mem_Icc hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => C (c n) * X * (1 - X) * (1 + X)) hbase hpos hnonneg
    hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_mul_one_sub_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
        (hc n) hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun _ => X - X ^ 3) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi => eval_X_sub_X_pow_three_nonpos_of_mem_Icc hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => C (c n) * (X - X ^ 3)) hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_sub_X_pow_three_nonpos_of_nonneg_of_mem_Icc (hc n) hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence hbase hpos
    (fun n r hr => hB_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_interval_lag_sequence
      hbase hpos hroot_lower hroot_upper hB_nonpos hrec hdeg_succ hno

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
  prec_lw_interval_lag_sequence
    (B := fun _ => (1 + X) * (1 + C (2 : ℝ) * X)) hbase hpos
    hroot_lower hroot_upper
    (fun _ _ _ hlo hhi =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_one_add_X_mul_one_add_two_mul_X_lag_sequence
      hbase hpos hroot_lower hroot_upper hrec hdeg_succ hno

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
  prec_lw_interval_lag_sequence
    (B := fun n => C (c n) * (1 + X) * (1 + C (2 : ℝ) * X)) hbase hpos
    hroot_lower hroot_upper
    (fun n _ _ hlo hhi =>
      eval_C_mul_one_add_X_mul_one_add_two_mul_X_nonpos_of_nonneg_of_mem_interval
        (hc n) hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
      hbase hpos hc hroot_lower hroot_upper hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => -(C (c n)) * (C (a n) + C (b n) * X))
    hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo _ =>
      eval_neg_C_mul_C_add_C_mul_X_nonpos_of_nonneg_of_nonneg_of_le_of_ge_neg_one
        (hc n) (hb n) (hba n) hlo)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_neg_C_mul_affine_inner_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hb hba hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => -(C (c n)) * (1 + X)) hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo _ => eval_neg_C_mul_one_add_X_nonpos_of_nonneg_of_ge_neg_one
      (hc n) hlo)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_lw_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
      (A := A) hbase hpos hnonneg hc hroot_lower ?_ hdeg_succ hno
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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
      (A := A) hbase hpos hnonneg hc hroot_lower hden hcoeff hraw hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => -(C (c n)) * (1 + C (2 : ℝ) * X))
    hbase hpos hnonneg
    (fun n r hr => by
      have hhalf := hroot_lower n r hr
      linarith)
    (fun n r hr _ _ =>
      eval_neg_C_mul_one_add_two_mul_X_nonpos_of_nonneg_of_ge_neg_half
        (hc n) (hroot_lower n r hr))
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun _ => X ^ 2 - 1) hbase hpos hnonneg hroot_lower
    (fun _ _ _ hlo hhi => eval_X_sq_sub_one_nonpos_of_mem_Icc hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hroot_lower hrec hdeg_succ hno

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
  prec_lw_inner_window_lag_sequence_of_nonneg_coeffs
    (B := fun n => C (c n) * (X ^ 2 - 1)) hbase hpos hnonneg hroot_lower
    (fun n _ _ hlo hhi =>
      eval_C_mul_X_sq_sub_one_nonpos_of_nonneg_of_mem_Icc (hc n) hlo hhi)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hc hroot_lower hrec hdeg_succ hno

end RealRooted
