module

import RealRooted.LiuWang.General
import RealRooted.ScalarNormalization
import RealRooted.SequenceClosure
import RealRooted.SignEvaluation
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Liu--Wang sequence core

Sequence induction for globally nonpositive, square, and quadratic lag coefficients.

The general form is `strictInterl_succ_of_recurrence_of_eval_nonpos`: it allows each step to
keep or raise the degree by one, and it allows consecutive rows to share roots.  The older
`*_lag_sequence` theorems require an exact degree increase and no common roots.
-/

public section

open Polynomial

namespace RealRooted.LiuWang

/-- **Liu--Wang sequence criterion**, with the lag condition read off the induction state.
Let `P (n + 2) = A n * P (n + 1) + B n * P n`, where every `P n` has positive leading
coefficient and each step keeps or raises the degree by one.  If `P 0 ≪ P 1` and `B n` is
nonpositive at the roots of `P (n + 1)` whenever `P (n + 1)` is real-rooted, then
`P n ≪ P (n + 1)` for all `n`.  Consecutive rows may share roots. -/
theorem strictInterl_succ_of_recurrence_of_eval_nonpos_of_splits {P A B : ℕ → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hrec : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_lo : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1)
    (hB : ∀ n, (P (n + 1)).Splits → ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0) :
    ∀ n, StrictInterl (P n) (P (n + 1)) := by
  refine strictInterl_sequence_of_base_and_step hbase fun n hprev ↦ ?_
  have hstep := strictInterl_mul_add_mul_of_eval_nonpos hprev (hpos n)
    (hrec n ▸ hpos (n + 2)) (hrec n ▸ hdeg_lo n) (hrec n ▸ hdeg_hi n) (hB n hprev.2.1.2)
  rwa [← hrec n] at hstep

/-- **Liu--Wang sequence criterion.**  Let `P (n + 2) = A n * P (n + 1) + B n * P n`, where
every `P n` has positive leading coefficient and each step keeps or raises the degree by one.
If `P 0 ≪ P 1` and `B n` is nonpositive at the roots of `P (n + 1)`, then `P n ≪ P (n + 1)`
for all `n`.  Consecutive rows may share roots. -/
theorem strictInterl_succ_of_recurrence_of_eval_nonpos {P A B : ℕ → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hrec : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_lo : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1)
    (hB : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0) :
    ∀ n, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_succ_of_recurrence_of_eval_nonpos_of_splits hbase hpos hrec hdeg_lo hdeg_hi
    fun n _ ↦ hB n

/-- Sequence-level Liu--Wang induction for a lag coefficient that is
nonpositive at all roots of the current row. -/
theorem strictInterl_nonpos_lag_sequence {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  exact (fun _ : (∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) ↦
    strictInterl_succ_of_recurrence_of_eval_nonpos
      hbase hpos hrec
      (fun n ↦ by rw [← hdeg_succ (n + 1)]; lia)
      (fun n ↦ by rw [← hdeg_succ (n + 1)]) hB_nonpos) hno

/-- Sequence-level Liu--Wang induction where lag nonpositivity may use the
current row's real-rootedness certificate from the induction state. -/
theorem strictInterl_nonpos_lag_sequence_of_inductive_nonpos {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
      ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  exact (fun _ : (∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) ↦
    strictInterl_succ_of_recurrence_of_eval_nonpos_of_splits
      hbase hpos hrec
      (fun n ↦ by rw [← hdeg_succ (n + 1)]; lia)
      (fun n ↦ by rw [← hdeg_succ (n + 1)])
      (fun n hs ↦ hB_nonpos n ⟨(hpos (n + 1)).ne_zero, hs⟩)) hno

/-- Denominator-fused Liu--Wang induction for a scalar left factor.

This wrapper consumes the raw OEIS-style recurrence
`C d_n * P_{n+2} = C d_n * (A_n P_{n+1} + B_n P_n)` and cancels the
nonzero scalar denominator internally before applying the usual nonpositive-lag
sequence theorem. -/
theorem strictInterl_nonpos_lag_sequence_den {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_nonpos_lag_sequence (A := A) hbase hpos hB_nonpos
    (fun n => eq_of_C_mul_eq_C_mul (hden n) (hraw n)) hdeg_succ hno

/-- Real-rootedness corollary for denominator-fused nonpositive-lag
Liu--Wang induction. -/
theorem isRealRooted_of_nonpos_lag_sequence_den {P : Nat → ℝ[X]}
    {A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_strictInterl_chain_from_step <|
    strictInterl_nonpos_lag_sequence_den hbase hpos hB_nonpos hden hraw hdeg_succ hno

/-- Sequence-level Liu--Wang induction for globally nonpositive negative
constant lag. -/
theorem strictInterl_negative_const_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_nonpos_lag_sequence
    (B := fun n => -(C (c n))) hbase hpos
    (fun n _ _ => eval_neg_C_nonpos_of_nonneg (hc n))
    hrec hdeg_succ hno

/-- Sequence-level Liu--Wang induction for globally nonpositive negative-square
lag. -/
theorem strictInterl_negative_square_lag_sequence {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_nonpos_lag_sequence
    (B := fun n => -(C (c n)) * (q n) ^ 2) hbase hpos
    (fun n _ _ => eval_neg_C_mul_sq_nonpos_of_nonneg (hc n))
    hrec hdeg_succ hno

/-- Real-rootedness corollary for the negative-square sequence wrapper. -/
theorem isRealRooted_of_negative_square_lag_sequence {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_strictInterl_chain_from_step <|
    strictInterl_negative_square_lag_sequence hbase hpos hc hrec hdeg_succ hno

/-- Sequence-level negative-square lag with unit scalar coefficient.

This accepts the natural recurrence spelling `-q_n^2 P_n` without requiring a
visible `-(C 1) * q_n^2` coefficient. -/
theorem strictInterl_negative_square_lag_sequence_unit {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((q n) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_negative_square_lag_sequence
    (A := A) (q := q) (c := fun _ => 1) hbase hpos (fun _ => by norm_num)
    (fun n => by simpa using hrec n) hdeg_succ hno

/-- Denominator-fused negative-square Liu--Wang induction for split raw
coefficients.

This matches Narayana-style OEIS recurrences where the raw recurrence has
`C d_n * P_{n+2}` on the left, the current-row summand already multiplied by
`C d_n`, and the lag summand written as
`C b_n * (-(q_n)^2 * P_n)`.  The side condition
`d_n⁻¹ * b_n = c_n` gives the normalized negative-square coefficient. -/
theorem strictInterl_negative_square_lag_sequence_den_coeff {P : Nat → ℝ[X]}
    {A q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  refine
    strictInterl_negative_square_lag_sequence
      (A := A) (q := q) (c := c) hbase hpos hc ?_ hdeg_succ hno
  intro n
  have hnorm :
      P (n + 2) =
        A n * P (n + 1) + C (c n) * (-(q n) ^ 2 * P n) :=
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
  calc
    P (n + 2) = A n * P (n + 1) + C (c n) * (-(q n) ^ 2 * P n) := hnorm
    _ = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n := by ring

end RealRooted.LiuWang

namespace RealRooted

end RealRooted
