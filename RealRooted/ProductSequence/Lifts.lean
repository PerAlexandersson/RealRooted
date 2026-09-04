import RealRooted.ProductSequence.Core

/-!
# Row-wise product lifts

Real-rootedness transport from quotient or model sequences through scalar,
monomial, affine, and powered affine row factors.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequenceInternal

/-- Lift real-rootedness from a quotient sequence through row-wise real-rooted
left factors. -/
theorem isRealRooted_of_product_lift_sequence
    {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  have hnext : F n * Q n ≠ 0 ∧ (F n * Q n).Splits :=
    isRealRooted_mul_of_isRealRooted (hfactor n) (hquot n)
  simpa [hrow n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_lift_sequence`. -/
theorem isRealRooted_of_product_lift_right_sequence
    {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot hfactor
    (fun n => by rw [hrow n, mul_comm])

/-- A real-rooted base row followed by an independently factorized real-rooted tail. -/
theorem isRealRooted_of_product_tail_sequence
    {P Q F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P (n + 1) = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  cases n with
  | zero => exact hbase
  | succ n =>
      have hnext : F n * Q n ≠ 0 ∧ (F n * Q n).Splits :=
        isRealRooted_mul_of_isRealRooted (hfactor n) (hquot n)
      simpa [hrow n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_tail_sequence`. -/
theorem isRealRooted_of_product_tail_right_sequence
    {P Q F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P (n + 1) = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_tail_sequence hbase hquot hfactor
    (fun n => by rw [hrow n, mul_comm])

/-- Transfer real-rootedness from a rowwise equal model sequence. -/
theorem isRealRooted_of_model_sequence
    {P Q : Nat → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hidentify : ∀ n : Nat, P n = Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  rw [hidentify n]
  exact hmodel n

/-- Lift a real-rooted model sequence through rowwise nonzero scalars and
monomial factors. -/
theorem isRealRooted_of_scalar_monomial_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * (X ^ (m n) * Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  have hproduct : X ^ (m n) * Q n ≠ 0 ∧ (X ^ (m n) * Q n).Splits :=
    isRealRooted_mul_of_isRealRooted
      (isRealRooted_pow_of_isRealRooted isRealRooted_X (m n)) (hmodel n)
  simpa [hrow n] using isRealRooted_C_mul_of_isRealRooted hproduct (hc n)

/-- A real-rooted base row followed by scalar-monomial lifts of a model
sequence. -/
theorem isRealRooted_of_scalar_monomial_tail_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P (n + 1) = C (c n) * (X ^ (m n) * Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  cases n with
  | zero =>
      exact hbase
  | succ n =>
      have hproduct : X ^ (m n) * Q n ≠ 0 ∧ (X ^ (m n) * Q n).Splits :=
        isRealRooted_mul_of_isRealRooted
          (isRealRooted_pow_of_isRealRooted isRealRooted_X (m n)) (hmodel n)
      simpa [Nat.succ_eq_add_one, hrow n] using
        isRealRooted_C_mul_of_isRealRooted hproduct (hc n)

/-- Lift separate even and odd real-rooted model sequences through rowwise
nonzero scalars and monomial factors. -/
theorem isRealRooted_of_even_odd_scalar_monomial_lift_sequence
    {P Qeven Qodd : Nat → ℝ[X]}
    {ceven codd : Nat → ℝ} {meven modd : Nat → Nat}
    (heven_model : ∀ n : Nat, Qeven n ≠ 0 ∧ (Qeven n).Splits)
    (hodd_model : ∀ n : Nat, Qodd n ≠ 0 ∧ (Qodd n).Splits)
    (hceven : ∀ n : Nat, ceven n ≠ 0)
    (hcodd : ∀ n : Nat, codd n ≠ 0)
    (heven : ∀ n : Nat,
      P (2 * n) = C (ceven n) * (X ^ (meven n) * Qeven n))
    (hodd : ∀ n : Nat,
      P (2 * n + 1) = C (codd n) * (X ^ (modd n) * Qodd n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have heven_realrooted :
      ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_scalar_monomial_lift_sequence heven_model hceven heven
  have hodd_realrooted :
      ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_scalar_monomial_lift_sequence hodd_model hcodd hodd
  exact isRealRooted_of_even_odd_sequence heven_realrooted hodd_realrooted

/-- Tail-start lift from a quotient sequence through row-wise real-rooted
left factors. -/
theorem isRealRooted_of_product_lift_sequence_from
    {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  by_cases hn : n ≤ N
  · exact hbase n hn
  · have hNn : N ≤ n := by lia
    have hnext : F n * Q n ≠ 0 ∧ (F n * Q n).Splits :=
      isRealRooted_mul_of_isRealRooted (hfactor n hNn) (hquot n hNn)
    simpa [hrow n hNn] using hnext

/-- Right-factor variant of `isRealRooted_of_product_lift_sequence_from`. -/
theorem isRealRooted_of_product_lift_right_sequence_from
    {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot hfactor
    (fun n hn => by rw [hrow n hn, mul_comm])

/-- Lift through a row-wise factor `X`, used for product reductions with a
persistent root at the origin. -/
theorem isRealRooted_of_X_lift_sequence
    {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot isRealRooted_X_sequence hrow

/-- Right-factor variant of `isRealRooted_of_X_lift_sequence`. -/
theorem isRealRooted_of_X_lift_right_sequence
    {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot isRealRooted_X_sequence hrow

/-- Tail-start variant of `isRealRooted_of_X_lift_sequence`. -/
theorem isRealRooted_of_X_lift_sequence_from
    {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_sequence n) hrow

/-- Right-factor variant of `isRealRooted_of_X_lift_sequence_from`. -/
theorem isRealRooted_of_X_lift_right_sequence_from
    {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_sequence n) hrow

/-- Lift through row-wise unit-slope real linear factors. -/
theorem isRealRooted_of_X_add_C_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_X_add_C_one_sequence t) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_X_add_C_one_sequence t) hrow

/-- Tail-start variant of `isRealRooted_of_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_one_sequence t n) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_lift_sequence_from`. -/
theorem isRealRooted_of_X_add_C_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_one_sequence t n) hrow

/-- Constant-first spelling of `isRealRooted_of_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_X_one_sequence t) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_X_one_sequence t) hrow

/-- Tail-start variant of `isRealRooted_of_C_add_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_one_sequence t n) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_X_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_one_sequence t n) hrow

/-- Lift through row-wise nonzero scalar constants. -/
theorem isRealRooted_of_C_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot (isRealRooted_C_sequence hc) hrow

/-- Right-factor variant of `isRealRooted_of_C_lift_sequence`. -/
theorem isRealRooted_of_C_lift_right_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * C (c n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_sequence hc) hrow

/-- Tail-start variant of `isRealRooted_of_C_lift_sequence`. -/
theorem isRealRooted_of_C_lift_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = C (c n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C (hc n hn)) hrow

/-- Right-factor variant of `isRealRooted_of_C_lift_sequence_from`. -/
theorem isRealRooted_of_C_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * C (c n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C (hc n hn)) hrow

/-- Lift through row-wise nonzero-slope real linear factors. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_mul_X_add_C_sequence hs) hrow

/-- Right-factor variant of `isRealRooted_of_C_mul_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_mul_X_add_C_sequence hs) hrow

/-- Tail-start variant of
`isRealRooted_of_C_mul_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C (hs n hn)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_mul_X_add_C_lift_sequence_from`. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C (hs n hn)) hrow

/-- Constant-first spelling of `isRealRooted_of_C_mul_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_C_mul_X_one_sequence hs) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_C_mul_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_C_mul_X_one_sequence hs) hrow

/-- Tail-start variant of
`isRealRooted_of_C_add_C_mul_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + C (s n) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X (hs n hn)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_add_C_mul_X_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X (hs n hn)) hrow

/-- Lift through row-wise powers of nonzero scalar constants. -/
theorem isRealRooted_of_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (c n) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_pow_sequence hc m) hrow

/-- Right-factor variant of `isRealRooted_of_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_pow_sequence hc m) hrow

/-- Tail-start variant of `isRealRooted_of_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (c n) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_pow (hc n hn) (m n)) hrow

/-- Right-factor variant of `isRealRooted_of_C_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_pow (hc n hn) (m n)) hrow

/-- Lift through row-wise powers of `X`. -/
theorem isRealRooted_of_X_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_X_pow_sequence m) hrow

/-- Right-factor variant of `isRealRooted_of_X_pow_lift_sequence`. -/
theorem isRealRooted_of_X_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_X_pow_sequence m) hrow

/-- Tail-start variant of `isRealRooted_of_X_pow_lift_sequence`. -/
theorem isRealRooted_of_X_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_pow_sequence m n) hrow

/-- Right-factor variant of `isRealRooted_of_X_pow_lift_sequence_from`. -/
theorem isRealRooted_of_X_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_pow_sequence m n) hrow

/-- Lift through row-wise powers of a fixed unit-slope real linear factor. -/
theorem isRealRooted_of_X_add_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C t) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_fixed_X_add_C_pow_sequence t m) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C t) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_fixed_X_add_C_pow_sequence t m) hrow

/-- Tail-start variant of `isRealRooted_of_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C t) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_fixed_X_add_C_pow_sequence t m n) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_pow_lift_sequence_from`. -/
theorem isRealRooted_of_X_add_C_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C t) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_fixed_X_add_C_pow_sequence t m n) hrow

/-- Lift through row-wise powers of unit-slope real linear factors. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_X_add_C_pow_sequence t m) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_row_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_X_add_C_pow_sequence t m) hrow

/-- Tail-start variant of
`isRealRooted_of_X_add_C_row_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_pow_sequence t m n) hrow

/-- Right-factor variant of
`isRealRooted_of_X_add_C_row_pow_lift_sequence_from`. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_pow_sequence t m n) hrow

/-- Constant-first spelling of
`isRealRooted_of_X_add_C_row_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_X_pow_sequence t m) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_X_pow_sequence t m) hrow

/-- Tail-start variant of `isRealRooted_of_C_add_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_pow_sequence t m n) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_X_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_pow_sequence t m n) hrow

/-- Lift through row-wise powers of a nonzero-slope real linear factor. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (s n) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_mul_X_add_C_pow_sequence hs m) hrow

/-- Right-factor variant of `isRealRooted_of_C_mul_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_mul_X_add_C_pow_sequence hs m) hrow

/-- Tail-start variant of
`isRealRooted_of_C_mul_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (s n) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C_pow (hs n hn) (m n)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C_pow (hs n hn) (m n)) hrow

/-- Constant-first spelling of
`isRealRooted_of_C_mul_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_C_mul_X_pow_sequence hs m) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_C_mul_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_C_mul_X_pow_sequence hs m) hrow

/-- Tail-start variant of
`isRealRooted_of_C_add_C_mul_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X_pow (hs n hn) (m n)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X_pow (hs n hn) (m n)) hrow


end RealRooted

