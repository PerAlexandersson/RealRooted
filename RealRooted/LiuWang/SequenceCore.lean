import RealRooted.LiuWang.Step
import RealRooted.ScalarNormalization
import RealRooted.SequenceClosure

/-!
# Liu--Wang sequence core

Sequence induction for globally nonpositive, square, and quadratic lag coefficients.
-/

open Polynomial

namespace RealRooted

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
  have hInter : Interlaces (P n) (P (n + 1)) :=
    hprev.toInterlaces (hdeg_succ n)
  have hstep : Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) :=
    prec_lw_two_of_nonpos_of_recurrence hInter (hpos n) (hrec n)
      (hpos (n + 2)) (hdeg_succ (n + 1)) (hno n) (hB_nonpos n)
  simpa [← hrec n] using hstep

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
  have hInter : Interlaces (P n) (P (n + 1)) :=
    hprev.toInterlaces (hdeg_succ n)
  have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := hprev.2.1
  have hstep : Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) :=
    prec_lw_two_of_nonpos_of_recurrence hInter (hpos n) (hrec n)
      (hpos (n + 2)) (hdeg_succ (n + 1)) (hno n) (hB_nonpos n hsource)
  simpa [← hrec n] using hstep

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_nonpos_lag_sequence hbase hpos hB_nonpos hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_nonpos_lag_sequence_of_inductive_nonpos
      hbase hpos hB_nonpos hrec hdeg_succ hno

/-- Denominator-fused Liu--Wang induction for a scalar left factor.

This wrapper consumes the raw OEIS-style recurrence
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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_nonpos_lag_sequence_den hbase hpos hB_nonpos hden hraw hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence
    (B := fun n => -(C (c n))) hbase hpos
    (fun n _ _ => eval_neg_C_nonpos_of_nonneg (hc n))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_const_lag_sequence hbase hpos hc hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence
    (B := fun n => C (-(c n))) hbase hpos
    (fun n _ _ => eval_C_neg_nonpos_of_nonneg (hc n))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_const_C_neg_lag_sequence hbase hpos hc hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence
    (B := fun n => -(C (c n)) * (q n) ^ 2) hbase hpos
    (fun n _ _ => eval_neg_C_mul_sq_nonpos_of_nonneg (hc n))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_square_lag_sequence hbase hpos hc hrec hdeg_succ hno

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
  prec_lw_negative_square_lag_sequence
    (A := A) (q := q) (c := fun _ => 1) hbase hpos (fun _ => by norm_num)
    (fun n => by simpa using hrec n) hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_square_lag_sequence_unit hbase hpos hrec hdeg_succ hno

/-- Denominator-fused negative-square Liu--Wang induction for split raw
coefficients.

This matches Narayana-style OEIS recurrences where the raw recurrence has
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_lw_negative_square_lag_sequence
      (A := A) (q := q) (c := c) hbase hpos hc ?_ hdeg_succ hno
  intro n
  have hnorm :
      P (n + 2) =
        A n * P (n + 1) + C (c n) * (-(q n) ^ 2 * P n) :=
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
  calc
    P (n + 2) = A n * P (n + 1) + C (c n) * (-(q n) ^ 2 * P n) := hnorm
    _ = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n := by ring

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_square_lag_sequence_den_coeff
      hbase hpos hc hden hcoeff hraw hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence
    (B := fun n => -(X ^ 2 + C (b n) * X + C (c n))) hbase hpos
    (fun n _ _ => eval_neg_monic_quadratic_nonpos_of_discrim_nonpos (hdisc n))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_monic_quadratic_lag_sequence hbase hpos hdisc hrec hdeg_succ hno

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
  prec_lw_nonpos_lag_sequence
    (B := fun n => -(C (a n) * X ^ 2 + C (b n) * X + C (c n))) hbase hpos
    (fun n _ _ => eval_neg_quadratic_nonpos_of_discrim_nonpos
      (ha n) (hc n) (hdisc n))
    hrec hdeg_succ hno

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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_quadratic_lag_sequence
      hbase hpos ha hc hdisc hrec hdeg_succ hno

/-- Denominator-fused Liu--Wang induction for a raw split non-monic
quadratic lag.

This matches OEIS-style recurrences where a scalar factor `d_n` multiplies
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_lw_negative_quadratic_lag_sequence
      (A := fun n => C ((d n)⁻¹) * Araw n)
      (a := a) (b := b) (c := c)
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
  isRealRooted_of_prec_chain_from_step <|
    prec_lw_negative_quadratic_lag_sequence_den_coeff
      hbase hpos ha hc hdisc hden ha_coeff hb_coeff hc_coeff hraw hdeg_succ hno

end RealRooted
