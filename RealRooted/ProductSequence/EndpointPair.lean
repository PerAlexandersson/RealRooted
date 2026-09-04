import RealRooted.PosCombo
import RealRooted.ProductSequence.Lifts

/-!
# Endpoint-pair product sequences

Interlacing recurrences for paired endpoint quotients and the corresponding
parity and endpoint-power lifts.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequenceInternal

/-- Parity lift for product-form rows whose odd rows are a nonzero scalar
times `X` times the corresponding even quotient row.

This is the final bookkeeping step for product exits such as A137477 after the
even quotient sequence has been proved real-rooted by a product-factor shell. -/
theorem isRealRooted_of_even_product_odd_X_scalar_sequence
    {P Q : Nat → ℝ[X]} {a : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (heven : ∀ n : Nat, P (2 * n) = Q n)
    (hodd : ∀ n : Nat, P (2 * n + 1) = C (a n) * X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have heven_realrooted : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    simpa [heven n] using hquot n
  have hodd_realrooted :
      ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_product_lift_sequence hquot
      (isRealRooted_C_mul_X_sequence ha) (fun n => by simpa [mul_assoc] using hodd n)
  exact isRealRooted_of_even_odd_sequence heven_realrooted hodd_realrooted

/-- One endpoint-quotient transition: first form `a+b`, then the next row is
`b+X(a+b)`. -/
theorem prec_endpoint_sum_then_X_step {a b : ℝ[X]}
    (hab : Prec a b)
    (ha_nonneg : HasNonnegCoeffs a) (hb_nonneg : HasNonnegCoeffs b)
    (hcop : IsCoprime b (X * (a + b))) :
    Prec (a + b) (b + X * (a + b)) := by
  have ha_pos : HasPosLeadingCoeff a :=
    ha_nonneg.pos_leadingCoeff (left_ne_zero_of_prec hab)
  have hb_pos : HasPosLeadingCoeff b :=
    hb_nonneg.pos_leadingCoeff (right_ne_zero_of_prec hab)
  have hsum_prec_raw : Prec (C (1 : ℝ) * a + C (1 : ℝ) * b) b :=
    prec_nonneg_combo_right hab ha_pos hb_pos zero_le_one zero_le_one (Or.inl zero_lt_one)
  have hsum_prec : Prec (a + b) b := by simpa using hsum_prec_raw
  have hsum_nonneg : HasNonnegCoeffs (a + b) := ha_nonneg.add hb_nonneg
  have hsum_pos : HasPosLeadingCoeff (a + b) :=
    hsum_nonneg.pos_leadingCoeff (left_ne_zero_of_prec hsum_prec)
  have hXsum_prec : Prec (a + b) (X * (a + b)) :=
    prec_mul_X_of_prec_of_nonneg
      (prec_refl (left_ne_zero_of_prec hsum_prec) (left_splits_of_prec hsum_prec))
      hsum_nonneg hsum_nonneg
  have hXsum_pos : HasPosLeadingCoeff (X * (a + b)) := hsum_pos.X_mul
  have hcombo : PosComboRealRooted b (X * (a + b)) :=
    PosComboRealRooted.of_commonLeftInterleaver
      hsum_prec hXsum_prec hb_pos hXsum_pos
  have hrr : b + X * (a + b) ≠ 0 ∧ (b + X * (a + b)).Splits :=
    PosComboRealRooted.isRealRooted_add hcombo
  exact
    prec_add_of_prec_left
      hsum_prec hXsum_prec hb_pos hXsum_pos hrr.1 hrr.2 hcop

/-- One endpoint-quotient transition with the parity reversed: first form
`b+Xa`, then the next row is `a+(b+Xa)`. -/
theorem prec_endpoint_X_then_sum_step {a b : ℝ[X]}
    (hab : Prec a b)
    (ha_nonneg : HasNonnegCoeffs a) (hb_nonneg : HasNonnegCoeffs b)
    (hcop : IsCoprime b (X * a)) :
    Prec (a + (b + X * a)) (b + X * a) := by
  have ha_pos : HasPosLeadingCoeff a :=
    ha_nonneg.pos_leadingCoeff (left_ne_zero_of_prec hab)
  have hb_pos : HasPosLeadingCoeff b :=
    hb_nonneg.pos_leadingCoeff (right_ne_zero_of_prec hab)
  have hXa_prec : Prec a (X * a) :=
    prec_mul_X_of_prec_of_nonneg
      (prec_refl (left_ne_zero_of_prec hab) (left_splits_of_prec hab))
      ha_nonneg ha_nonneg
  have hXa_pos : HasPosLeadingCoeff (X * a) := ha_pos.X_mul
  have hcombo : PosComboRealRooted b (X * a) :=
    PosComboRealRooted.of_commonLeftInterleaver hab hXa_prec hb_pos hXa_pos
  have hrr : b + X * a ≠ 0 ∧ (b + X * a).Splits :=
    PosComboRealRooted.isRealRooted_add hcombo
  have ha_sum_prec : Prec a (b + X * a) :=
    prec_add_of_prec_left hab hXa_prec hb_pos hXa_pos hrr.1 hrr.2 hcop
  have hsum_nonneg : HasNonnegCoeffs (b + X * a) :=
    hb_nonneg.add (hasNonnegCoeffs_X.mul ha_nonneg)
  have hsum_pos : HasPosLeadingCoeff (b + X * a) :=
    hsum_nonneg.pos_leadingCoeff (right_ne_zero_of_prec ha_sum_prec)
  have hnext_raw :
      Prec (C (1 : ℝ) * a + C (1 : ℝ) * (b + X * a)) (b + X * a) :=
    prec_nonneg_combo_right ha_sum_prec ha_pos hsum_pos
      zero_le_one zero_le_one (Or.inl zero_lt_one)
  simpa [add_assoc] using hnext_raw

private def endpointPairPackage (A B : Nat → ℝ[X]) (n : Nat) : Prop :=
  Prec (A n) (B n) ∧ HasNonnegCoeffs (A n) ∧ HasNonnegCoeffs (B n)

private theorem prec_sequence_of_endpointPairPackage {A B : Nat → ℝ[X]}
    (hpack : ∀ n : Nat, endpointPairPackage A B n) :
    ∀ n : Nat, Prec (A n) (B n) :=
  fun n => (hpack n).1

/-- Pair-sequence endpoint quotient shell.

This is the quotient recurrence after removing endpoint powers when the
transition first forms `A_{n+1}=A_n+B_n` and then
`B_{n+1}=B_n+X A_{n+1}`. -/
theorem prec_endpoint_sum_then_X_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, Prec (A n) (B n) := by
  have hpack : ∀ n : Nat, endpointPairPackage A B n :=
    sequence_of_base_and_step ⟨hbase, hA0_nonneg, hB0_nonneg⟩ fun n hP => by
      rcases hP with ⟨hprec, hA_nonneg, hB_nonneg⟩
      have hcop' : IsCoprime (B n) (X * (A n + B n)) := by simpa [hstepA n] using hcop n
      have hprec_next :
          Prec (A (n + 1)) (B (n + 1)) := by
        simpa [hstepA n, hstepB n] using
          prec_endpoint_sum_then_X_step hprec hA_nonneg hB_nonneg hcop'
      have hA_nonneg_next : HasNonnegCoeffs (A (n + 1)) := by
        rw [hstepA n]
        exact hA_nonneg.add hB_nonneg
      have hB_nonneg_next : HasNonnegCoeffs (B (n + 1)) := by
        rw [hstepB n]
        exact hB_nonneg.add (hasNonnegCoeffs_X.mul hA_nonneg_next)
      exact ⟨hprec_next, hA_nonneg_next, hB_nonneg_next⟩
  exact prec_sequence_of_endpointPairPackage hpack

/-- Real-rootedness corollary for
`prec_endpoint_sum_then_X_pair_sequence`. -/
theorem isRealRooted_of_endpoint_sum_then_X_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
  isRealRooted_pair_sequence_of_prec_sequence <|
    prec_endpoint_sum_then_X_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepA hstepB hcop

/-- Pair-sequence endpoint quotient shell with the parity reversed.

Here the transition first forms `B_{n+1}=B_n+X A_n` and then
`A_{n+1}=A_n+B_{n+1}`. -/
theorem prec_endpoint_X_then_sum_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, Prec (A n) (B n) := by
  have hpack : ∀ n : Nat, endpointPairPackage A B n :=
    sequence_of_base_and_step ⟨hbase, hA0_nonneg, hB0_nonneg⟩ fun n hP => by
      rcases hP with ⟨hprec, hA_nonneg, hB_nonneg⟩
      have hprec_next :
          Prec (A (n + 1)) (B (n + 1)) := by
        simpa [hstepB n, hstepA n] using
          prec_endpoint_X_then_sum_step hprec hA_nonneg hB_nonneg (hcop n)
      have hB_nonneg_next : HasNonnegCoeffs (B (n + 1)) := by
        rw [hstepB n]
        exact hB_nonneg.add (hasNonnegCoeffs_X.mul hA_nonneg)
      have hA_nonneg_next : HasNonnegCoeffs (A (n + 1)) := by
        rw [hstepA n]
        exact hA_nonneg.add hB_nonneg_next
      exact ⟨hprec_next, hA_nonneg_next, hB_nonneg_next⟩
  exact prec_sequence_of_endpointPairPackage hpack

/-- Real-rootedness corollary for
`prec_endpoint_X_then_sum_pair_sequence`. -/
theorem isRealRooted_of_endpoint_X_then_sum_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
  isRealRooted_pair_sequence_of_prec_sequence <|
    prec_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop

/-- Endpoint quotient plus endpoint-power lift for a single row sequence.

The even rows are endpoint powers times `A_n`, while the odd rows are endpoint
powers times `B_n`.  The quotient pair uses the sum-then-`X` parity. -/
theorem isRealRooted_of_endpoint_sum_then_X_pair_lift_sequence
    {P A B : Nat → ℝ[X]} {t : ℝ} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1)))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C t) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C t) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot :
      ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
    isRealRooted_of_endpoint_sum_then_X_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepA hstepB hcop
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n)) (Q := A) (t := t) (m := mA)
      (left_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowA
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n + 1)) (Q := B) (t := t) (m := mB)
      (right_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowB
  exact isRealRooted_of_even_odd_sequence heven hodd

/-- Endpoint quotient plus endpoint-power lift for the reversed quotient
parity. -/
theorem isRealRooted_of_endpoint_X_then_sum_pair_lift_sequence
    {P A B : Nat → ℝ[X]} {t : ℝ} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C t) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C t) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot :
      ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
    isRealRooted_of_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n)) (Q := A) (t := t) (m := mA)
      (left_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowA
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n + 1)) (Q := B) (t := t) (m := mB)
      (right_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowB
  exact isRealRooted_of_even_odd_sequence heven hodd

/-- Endpoint quotient plus endpoint-power lift for the reversed quotient
parity, with the single row sequence using the opposite even/odd assignment.

This is the shape for endpoint recurrences where the quotient pair satisfies
`B_{n+1}=B_n+X A_n`, `A_{n+1}=A_n+B_{n+1}`, but the original even rows are
endpoint powers times `B_n` and the original odd rows are endpoint powers
times `A_n`. -/
theorem isRealRooted_of_endpoint_X_then_sum_pair_lift_swapped_sequence
    {P A B : Nat → ℝ[X]} {t : ℝ} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowB : ∀ n : Nat, P (2 * n) = (X + C t) ^ (mB n) * B n)
    (hrowA : ∀ n : Nat, P (2 * n + 1) = (X + C t) ^ (mA n) * A n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot :
      ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
    isRealRooted_of_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n)) (Q := B) (t := t) (m := mB)
      (right_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowB
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n + 1)) (Q := A) (t := t) (m := mA)
      (left_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowA
  exact isRealRooted_of_even_odd_sequence heven hodd


end RealRooted

