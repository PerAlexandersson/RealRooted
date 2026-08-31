import RealRooted.LiuWangRecursion
import RealRooted.MaWang.DerivativeStep
import RealRooted.RootBounds
import RealRooted.SequenceClosure

/-!
# Ma--Wang derivative sequences

Sequence closure for weak derivative steps and derivative-plus-lag recurrences.
-/

open Polynomial

namespace RealRooted

/-- Sequence-level weak Ma--Wang induction for derivative recurrences whose
derivative coefficient is nonpositive at every old root. -/
theorem prec_mw_derivative_nonpos_sequence {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := hprev.2.1
  have hstep :
      Prec (P (n + 1))
        (U n * P (n + 1) + V n * (P (n + 1)).derivative) :=
    prec_mw_derivative_of_nonpos_of_recurrence hsource.2 (hdeg_two n)
      (hrec n) (hpos (n + 2)) (hdeg_lo n) (hdeg_hi n)
      (hpos (n + 1)) (hV_nonpos n)
  simpa [← hrec n] using hstep

/-- Real-rootedness corollary for sequence-level weak Ma--Wang induction. -/
theorem isRealRooted_of_mw_derivative_nonpos_sequence {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_mw_derivative_nonpos_sequence
      hbase hpos hdeg_two hV_nonpos hrec hdeg_lo hdeg_hi
  exact isRealRooted_of_prec_chain hbase hprec

/-- Sequence-level Ma--Wang induction for the `A194649` window factor
`(1+X)(1+2X)`.  The sequence proof supplies the root window `[-1,-1/2]`;
the tactic dispatches the sign certificate and induction shell. -/
theorem prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
        (hroot_lower n r hr) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness endpoint for the sequence-level `(1+X)(1+2X)P'`
Ma--Wang window shell. -/
theorem isRealRooted_of_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
        (hroot_lower n r hr) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_neg_const_sequence {P : Nat → ℝ[X]}
    {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + C (-(c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => eval_C_neg_nonpos_of_nonneg (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level negative-constant
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_neg_const_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + C (-(c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => eval_C_neg_nonpos_of_nonneg (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_neg_C_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (-(C (c n))) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => eval_neg_C_nonpos_of_nonneg (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `-(C c_n)P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_neg_C_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (-(C (c n))) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => eval_neg_C_nonpos_of_nonneg (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_neg_C_mul_X_sq_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => eval_neg_C_mul_X_sq_nonpos_of_nonneg (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `-c_n X^2 P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => eval_neg_C_mul_X_sq_nonpos_of_nonneg (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_C_neg_mul_X_sq_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (-(c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => by
      simpa [mul_assoc] using
        eval_neg_C_mul_X_sq_nonpos_of_nonneg (c := c n) (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the `C(-c_n)X^2P'` sequence wrapper. -/
theorem isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (-(c n)) * X ^ 2) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => by
      simpa [mul_assoc] using
        eval_neg_C_mul_X_sq_nonpos_of_nonneg (c := c n) (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_neg_C_mul_X_sq_product_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n) * X ^ 2)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => by
      simpa [neg_mul, mul_assoc] using
        eval_neg_C_mul_X_sq_nonpos_of_nonneg (c := c n) (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the `-(C c_n * X^2)P'` sequence wrapper. -/
theorem isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n) * X ^ 2)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r _ => by
      simpa [neg_mul, mul_assoc] using
        eval_neg_C_mul_X_sq_nonpos_of_nonneg (c := c n) (r := r) (hc n))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (1 + X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => eval_one_add_X_nonpos_of_le_neg_one (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `(1+X)P'`
Ma--Wang wrapper on roots at most `-1`. -/
theorem isRealRooted_of_mw_derivative_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (1 + X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => eval_one_add_X_nonpos_of_le_neg_one (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_C_mul_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n(1+X)P'`
Ma--Wang wrapper on roots at most `-1`. -/
theorem isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_one_add_X_mul_C_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + ((1 + X) * C (c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
          (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for scalar-on-right `(1+X)C(c_n)P'`. -/
theorem isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + ((1 + X) * C (c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
          (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_X_sub_one_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X - 1) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => eval_X_sub_one_nonpos_of_le_one (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `(X-1)P'`
Ma--Wang wrapper on roots at most `1`. -/
theorem isRealRooted_of_mw_derivative_X_sub_one_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X - 1) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => eval_X_sub_one_nonpos_of_le_one (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_C_mul_X_sub_one_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n(X-1)P'`
Ma--Wang wrapper on roots at most `1`. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * (X - 1)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

theorem prec_mw_derivative_X_sub_one_mul_C_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + ((X - 1) * C (c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one
          (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for scalar-on-right `(X-1)C(c_n)P'`. -/
theorem isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + ((X - 1) * C (c n)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr => by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one
          (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Sequence-level weak Ma--Wang induction for the common
`c_n X(1-X) P'_{n+1}` derivative coefficient on roots contained in
`(-∞,0]`. -/
theorem prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence {P : Nat → ℝ[X]}
    {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hdeg_two
    (fun n r hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos
        (hc n) (hroots_nonpos n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X(1-X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hdeg_two
    (fun n r hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos
        (hc n) (hroots_nonpos n r hr))
    hrec hdeg_lo hdeg_hi

/-- Sequence-level weak Ma--Wang induction where the derivative coefficient is
nonpositive on the current roots, after using nonnegative coefficients to
derive the current-row root bound `r <= 0`. -/
theorem prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := hprev.2.1
  have hV_at_roots :
      ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0 := by
    intro r hr
    have hr_nonpos : r ≤ 0 :=
      roots_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) r hr
    exact hV_nonpos n r hr hr_nonpos
  have hstep :
      Prec (P (n + 1))
        (U n * P (n + 1) + V n * (P (n + 1)).derivative) :=
    prec_mw_derivative_of_nonpos_of_recurrence hsource.2 (hdeg_two n)
      (hrec n) (hpos (n + 2)) (hdeg_lo n) (hdeg_hi n)
      (hpos (n + 1)) hV_at_roots
  simpa [← hrec n] using hstep

/-- Sequence-level weak Ma--Wang induction where the derivative coefficient is
nonpositive on the nonpositive half-line, and the current-row root bound is
derived internally from real-rootedness plus nonnegative coefficients. -/
theorem prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    hbase hpos hnonneg hdeg_two
    (fun n r _ hr_nonpos => hV_nonpos n r hr_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the nonnegative-coefficient sequence-level
weak Ma--Wang induction with a root-aware derivative coefficient sign. -/
theorem isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
      hbase hpos hnonneg hdeg_two hV_nonpos hrec hdeg_lo hdeg_hi
  exact isRealRooted_of_prec_chain hbase hprec

/-- Real-rootedness corollary for the nonnegative-coefficient sequence-level
weak Ma--Wang induction. -/
theorem isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    hbase hpos hnonneg hdeg_two
    (fun n r _ hr_nonpos => hV_nonpos n r hr_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Combined Ma--Wang/Liu--Wang sequence induction for recurrences
`P_{n+2} = U_n P_{n+1} + V_n P'_{n+1} + W_n P_n`.

The derivative term is handled as an additional generalized Liu--Wang
interlacer of the current row, while the lag term `P_n` is the distinguished
interlacer that supplies the no-common-roots hypothesis.  The sign side
conditions may use the already-established current-row real-rootedness data. -/
theorem prec_mw_lw_derivative_lag_sequence_of_root_signs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec hV_nonpos hW_nonpos hdeg_succ hno

/-- Combined Ma--Wang/Liu--Wang sequence induction with direct root-sign
side conditions. -/
theorem prec_mw_lw_derivative_lag_sequence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec
    (fun n _ r hr => hV_nonpos n r hr)
    (fun n _ r hr => hW_nonpos n r hr)
    hdeg_succ hno

/-- Combined Ma--Wang/Liu--Wang sequence induction where the derivative and
lag sign checks are certified on an explicit root window. -/
theorem prec_mw_lw_derivative_lag_sequence_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_lw_derivative_lag_sequence
    hbase hpos hdeg_two hrec
    (fun n r hr => hV_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    (fun n r hr => hW_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hdeg_succ hno

/-- Combined Ma--Wang/Liu--Wang sequence induction where nonnegative
coefficients of the current row provide the half-line root bound `r <= 0`. -/
theorem prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec
    (fun n hsource r hr => by
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) r hr
      exact hV_nonpos n r hr hr_nonpos)
    (fun n hsource r hr => by
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) r hr
      exact hW_nonpos n r hr hr_nonpos)
    hdeg_succ hno

/-- Combined Ma--Wang/Liu--Wang sequence induction with half-line sign
side conditions independent of the current-root proof. -/
theorem prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
    hbase hpos hnonneg hdeg_two hrec
    (fun n r _ hr_nonpos => hV_nonpos n r hr_nonpos)
    (fun n r _ hr_nonpos => hW_nonpos n r hr_nonpos)
    hdeg_succ hno

/-- Real-rootedness corollary for the combined Ma--Wang/Liu--Wang
derivative-plus-lag sequence induction. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_signs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec hV_nonpos hW_nonpos hdeg_succ hno

/-- Real-rootedness corollary for the combined Ma--Wang/Liu--Wang
derivative-plus-lag sequence induction with direct root-sign side conditions. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec
    (fun n _ r hr => hV_nonpos n r hr)
    (fun n _ r hr => hW_nonpos n r hr)
    hdeg_succ hno

/-- Real-rootedness corollary for the combined Ma--Wang/Liu--Wang
derivative-plus-lag sequence induction on an explicit root window. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence
    hbase hpos hdeg_two hrec
    (fun n r hr => hV_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    (fun n r hr => hW_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hdeg_succ hno

/-- Real-rootedness corollary for the combined Ma--Wang/Liu--Wang
derivative-plus-lag sequence induction. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec
    (fun n hsource r hr => by
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) r hr
      exact hV_nonpos n r hr hr_nonpos)
    (fun n hsource r hr => by
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) r hr
      exact hW_nonpos n r hr hr_nonpos)
    hdeg_succ hno

/-- Real-rootedness corollary for the combined Ma--Wang/Liu--Wang
derivative-plus-lag sequence induction with half-line sign side conditions. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
    hbase hpos hnonneg hdeg_two hrec
    (fun n r _ hr_nonpos => hV_nonpos n r hr_nonpos)
    (fun n r _ hr_nonpos => hW_nonpos n r hr_nonpos)
    hdeg_succ hno

end RealRooted
