import RealRooted.LiuWangRecursion
import RealRooted.MaWang
import RealRooted.Tactic.Finish
import RealRooted.Tactic.RootBounds
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.Sign
import RealRooted.Tactic.SideGoals

open Polynomial

/-!
# Ma-Wang tactic

Dispatcher tactics:

```lean
rr_ma_wang
rr_finish_sequence
```

Primary target:
one-step derivative recurrences of the form

```text
P (n + 1) = u n * P n + v n * (P n).derivative.
```

The tactic should apply existing theorems such as `prec_ma_wang` and
`prec_of_interlaces_evalCoeff_nonpos`, then discharge certificate side goals.

First intended regression examples:

- `touchard`;
- `coloredSetPartitions`;
- `stirlingPermutations`;
- `typeBEulerian`;
- `simsun`.
-/

namespace RealRooted

/-- Weak Ma--Wang derivative step using the Liu--Wang sign criterion.  This is
useful when the derivative coefficient can vanish at endpoint roots, so the
strict Ma--Wang sign condition is too strong. -/
theorem prec_mw_derivative_of_nonpos {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f := derivative_interlaces hf hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  exact
    prec_of_interlaces_evalCoeff_nonpos
      (f := f) (g := f.derivative) (a := u) (b := v)
      hder hf'_pos hF_pos hdeg_lo hdeg_hi hv_nonpos

theorem prec_mw_derivative_X_mul_of_nonneg_on_roots {f u q : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * q) * f.derivative).natDegree)
    (hdeg_hi : (u * f + (X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    Prec f (u * f + (X * q) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact eval_X_mul_nonpos_of_nonpos_of_nonneg (hf_roots r hr) (hq_nonneg r hr)

theorem prec_mw_derivative_C_mul_X_mul_of_nonneg_on_roots {f u q : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * X * q) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * X * q) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * X * q) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hq_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r) :
    Prec f (u * f + (C c * X * q) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact
    eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
      hc (hf_roots r hr) (hq_nonneg r hr)

theorem prec_mw_derivative_X_mul_one_add_X_of_roots_in_Icc {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + (X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (X * (1 + X)) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ 0) :
    Prec f (u * f + (X * (1 + X)) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact eval_X_mul_one_add_X_nonpos_of_mem_Icc (hroot_lo r hr) (hroot_hi r hr)

theorem prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
    {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X * (1 + X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X * (1 + X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff (u * f + (-(C c) * X * (1 + X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ -1) :
    Prec f (u * f + (-(C c) * X * (1 + X)) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact
    eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
      hc (hroot_hi r hr)

theorem prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval
    {f u : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤
        (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos :
      HasPosLeadingCoeff
        (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_lo : ∀ r, f.IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ r, f.IsRoot r → r ≤ -(1 / 2 : ℝ)) :
    Prec f (u * f + ((1 + X) * (1 + C (2 : ℝ) * X)) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact
    eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
      (hroot_lo r hr) (hroot_hi r hr)

theorem prec_mw_derivative_neg_const {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + C (-c) * f.derivative).natDegree)
    (hdeg_hi : (u * f + C (-c) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + C (-c) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    Prec f (u * f + C (-c) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact eval_C_neg_nonpos_of_nonneg hc

theorem prec_mw_derivative_neg_C_mul_X_sq {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo :
      f.natDegree ≤ (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (-(C c) * X ^ 2) * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (-(C c) * X ^ 2) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hc : 0 ≤ c) :
    Prec f (u * f + (-(C c) * X ^ 2) * f.derivative) := by
  refine
    prec_mw_derivative_of_nonpos
      hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos ?_
  intro r hr
  exact eval_neg_C_mul_X_sq_nonpos_of_nonneg hc

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
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := ih.2.1
      have hF_pos :
          HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative) := by
        simpa [← hrec n] using hpos (n + 2)
      have hstep :
          Prec (P (n + 1))
            (U n * P (n + 1) + V n * (P (n + 1)).derivative) :=
        prec_mw_derivative_of_nonpos
          hsource.2 (hdeg_two n)
          (by simpa [← hrec n] using hdeg_lo n)
          (by simpa [← hrec n] using hdeg_hi n)
          hF_pos (hpos (n + 1)) (hV_nonpos n)
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
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

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
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := ih.2.1
      have hF_pos :
          HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative) := by
        simpa [← hrec n] using hpos (n + 2)
      have hV_at_roots :
          ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0 := by
        intro r hr
        have hr_nonpos : r ≤ 0 :=
          root_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) hr
        exact hV_nonpos n r hr hr_nonpos
      have hstep :
          Prec (P (n + 1))
            (U n * P (n + 1) + V n * (P (n + 1)).derivative) :=
        prec_mw_derivative_of_nonpos
          hsource.2 (hdeg_two n)
          (by simpa [← hrec n] using hdeg_lo n)
          (by simpa [← hrec n] using hdeg_hi n)
          hF_pos (hpos (n + 1)) hV_at_roots
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
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact
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
        root_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) hr
      exact hV_nonpos n r hr hr_nonpos)
    (fun n hsource r hr => by
      have hr_nonpos : r ≤ 0 :=
        root_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) hr
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
        root_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) hr
      exact hV_nonpos n r hr hr_nonpos)
    (fun n hsource r hr => by
      have hr_nonpos : r ≤ 0 :=
        root_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) hr
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

/-- Denominator-fused combined Ma--Wang/Liu--Wang induction.

This consumes the split raw recurrence
`C d_n P_{n+2} = C d_n U_n P_{n+1} + C b_n V_n P'_{n+1} +
C e_n W_n P_n` and internally normalizes the two scalar coefficients to
`c_n` and `a_n`, using `d_n⁻¹ * b_n = c_n` and `d_n⁻¹ * e_n = a_n`. -/
theorem prec_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs
      (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
      hbase hpos hnonneg hdeg_two ?_ ?_ ?_ hdeg_succ hno
  · intro n
    have hnorm :
        P (n + 2) =
          U n * P (n + 1) +
            C (c n) * (V n * (P (n + 1)).derivative) +
            C (a n) * (W n * P n) :=
      eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
        (hden n) (hcoeffV n) (hcoeffW n) (hraw n)
    calc
      P (n + 2) =
          U n * P (n + 1) +
            C (c n) * (V n * (P (n + 1)).derivative) +
            C (a n) * (W n * P n) := hnorm
      _ =
          U n * P (n + 1) +
            (C (c n) * V n) * (P (n + 1)).derivative +
            (C (a n) * W n) * P n := by ring
  · intro n r hr
    simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos (hc n) (hV_nonpos n r hr)
  · intro n r hr
    simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos (ha n) (hW_nonpos n r hr)

/-- Denominator-fused combined Ma--Wang/Liu--Wang induction with explicit
root-window sign certificates. -/
theorem prec_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_mw_lw_derivative_lag_sequence_of_root_window
      (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
      hbase hpos hdeg_two ?_ hroot_lower hroot_upper ?_ ?_ hdeg_succ hno
  · intro n
    have hnorm :
        P (n + 2) =
          U n * P (n + 1) +
            C (c n) * (V n * (P (n + 1)).derivative) +
            C (a n) * (W n * P n) :=
      eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
        (hden n) (hcoeffV n) (hcoeffW n) (hraw n)
    calc
      P (n + 2) =
          U n * P (n + 1) +
            C (c n) * (V n * (P (n + 1)).derivative) +
            C (a n) * (W n * P n) := hnorm
      _ =
          U n * P (n + 1) +
            (C (c n) * V n) * (P (n + 1)).derivative +
            (C (a n) * W n) * P n := by ring
  · intro n r hr hlo hhi
    simpa [Polynomial.eval_mul] using
      mul_nonpos_of_nonneg_of_nonpos (hc n) (hV_nonpos n r hr hlo hhi)
  · intro n r hr hlo hhi
    simpa [Polynomial.eval_mul] using
      mul_nonpos_of_nonneg_of_nonpos (ha n) (hW_nonpos n r hr hlo hhi)

/-- Real-rootedness corollary for denominator-fused combined Ma--Wang/Liu--Wang
induction. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs
    (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
    hbase hpos hnonneg hdeg_two
    (fun n => by
      have hnorm :
          P (n + 2) =
            U n * P (n + 1) +
              C (c n) * (V n * (P (n + 1)).derivative) +
              C (a n) * (W n * P n) :=
        eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
          (hden n) (hcoeffV n) (hcoeffW n) (hraw n)
      calc
        P (n + 2) =
            U n * P (n + 1) +
              C (c n) * (V n * (P (n + 1)).derivative) +
              C (a n) * (W n * P n) := hnorm
        _ =
            U n * P (n + 1) +
              (C (c n) * V n) * (P (n + 1)).derivative +
              (C (a n) * W n) * P n := by ring)
    (fun n r hr => by
      simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos (hc n) (hV_nonpos n r hr))
    (fun n r hr => by
      simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos (ha n) (hW_nonpos n r hr))
    hdeg_succ hno

/-- Real-rootedness corollary for denominator-fused combined Ma--Wang/Liu--Wang
induction with explicit root-window sign certificates. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_window
    (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
    hbase hpos hdeg_two
    (fun n => by
      have hnorm :
          P (n + 2) =
            U n * P (n + 1) +
              C (c n) * (V n * (P (n + 1)).derivative) +
              C (a n) * (W n * P n) :=
        eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
          (hden n) (hcoeffV n) (hcoeffW n) (hraw n)
      calc
        P (n + 2) =
            U n * P (n + 1) +
              C (c n) * (V n * (P (n + 1)).derivative) +
              C (a n) * (W n * P n) := hnorm
        _ =
            U n * P (n + 1) +
              (C (c n) * V n) * (P (n + 1)).derivative +
              (C (a n) * W n) * P n := by ring)
    hroot_lower hroot_upper
    (fun n r hr hlo hhi => by
      simpa [Polynomial.eval_mul] using
        mul_nonpos_of_nonneg_of_nonpos (hc n) (hV_nonpos n r hr hlo hhi))
    (fun n r hr hlo hhi => by
      simpa [Polynomial.eval_mul] using
        mul_nonpos_of_nonneg_of_nonpos (ha n) (hW_nonpos n r hr hlo hhi))
    hdeg_succ hno

/-- Denominator-fused nonpositive-factor Ma--Wang induction with
nonnegative coefficients.

This consumes the split raw recurrence
`C d_n P_{n+2} = C d_n U_n P_{n+1} + C b_n (V_n P'_{n+1})` and internally
normalizes the scalar derivative coefficient to `c_n`, using
`d_n⁻¹ * b_n = c_n`. -/
theorem prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
      (U := U) (V := fun n => C (c n) * V n) hbase hpos hnonneg hdeg_two ?_ ?_
      hdeg_lo hdeg_hi
  · intro n r hr
    simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos (hc n) (hV_nonpos n r hr)
  · intro n
    have hnorm :
        P (n + 2) =
          U n * P (n + 1) +
            C (c n) * (V n * (P (n + 1)).derivative) :=
      eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
    calc
      P (n + 2) =
          U n * P (n + 1) +
            C (c n) * (V n * (P (n + 1)).derivative) := hnorm
      _ =
          U n * P (n + 1) +
            (C (c n) * V n) * (P (n + 1)).derivative := by ring

/-- Real-rootedness corollary for denominator-fused nonpositive-factor
Ma--Wang induction with nonnegative coefficients. -/
theorem isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (U := U) (V := fun n => C (c n) * V n) hbase hpos hnonneg hdeg_two
    (fun n r hr => by
      simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos (hc n) (hV_nonpos n r hr))
    (fun n => by
      have hnorm :
          P (n + 2) =
            U n * P (n + 1) +
              C (c n) * (V n * (P (n + 1)).derivative) :=
        eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
      calc
        P (n + 2) =
            U n * P (n + 1) +
              C (c n) * (V n * (P (n + 1)).derivative) := hnorm
        _ =
            U n * P (n + 1) +
              (C (c n) * V n) * (P (n + 1)).derivative := by ring)
    hdeg_lo hdeg_hi

/-- Sequence-level `X Q_n P'` Ma--Wang wrapper.  The current-row root bound is
derived internally from nonnegative coefficients; the remaining input is the
nonnegativity of `Q_n` at current-row roots. -/
theorem prec_mw_derivative_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X Q_n P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X Q_n P'` Ma--Wang wrapper. -/
theorem prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        (hc n) hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X Q_n P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        (hc n) hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Denominator-fused `c_n X Q_n P'` Ma--Wang induction with nonnegative
coefficients.

This consumes the split raw recurrence
`C d_n P_{n+2} = C d_n U_n P_{n+1} + C b_n (X Q_n P'_{n+1})` and internally
normalizes the scalar derivative coefficient to `c_n`, using
`d_n⁻¹ * b_n = c_n`. -/
theorem prec_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine
    prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
      (U := U) (Q := Q) (c := c) hbase hpos hnonneg hdeg_two hc hQ_nonneg ?_
      hdeg_lo hdeg_hi
  intro n
  have hnorm :
      P (n + 2) =
        U n * P (n + 1) +
          C (c n) * ((X * Q n) * (P (n + 1)).derivative) :=
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
  calc
    P (n + 2) =
        U n * P (n + 1) +
          C (c n) * ((X * Q n) * (P (n + 1)).derivative) := hnorm
    _ =
        U n * P (n + 1) +
          (C (c n) * X * Q n) * (P (n + 1)).derivative := by ring

/-- Real-rootedness corollary for denominator-fused `c_n X Q_n P'`
Ma--Wang induction with nonnegative coefficients. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    (U := U) (Q := Q) (c := c) hbase hpos hnonneg hdeg_two hc hQ_nonneg
    (fun n => by
      have hnorm :
          P (n + 2) =
            U n * P (n + 1) +
              C (c n) * ((X * Q n) * (P (n + 1)).derivative) :=
        eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
      calc
        P (n + 2) =
            U n * P (n + 1) +
              C (c n) * ((X * Q n) * (P (n + 1)).derivative) := hnorm
        _ =
            U n * P (n + 1) +
              (C (c n) * X * Q n) * (P (n + 1)).derivative := by ring)
    hdeg_lo hdeg_hi

/-- Sequence-level `X P'` Ma--Wang wrapper.  The current-row root bound is
derived internally from nonnegative coefficients. -/
theorem prec_mw_derivative_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun _ => X) hbase hpos hnonneg hdeg_two
    (fun _ _ hroot_nonpos => eval_X_nonpos_of_nonpos hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X P'` Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun _ => X) hbase hpos hnonneg hdeg_two
    (fun _ _ hroot_nonpos => eval_X_nonpos_of_nonpos hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X P'` Ma--Wang wrapper for positive-constant MW2
derivative coefficients. -/
theorem prec_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (C (c n) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X) hbase hpos hnonneg hdeg_two
    (fun n _ hroot_nonpos =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (C (c n) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X) hbase hpos hnonneg hdeg_two
    (fun n _ hroot_nonpos =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `X(1+X) P'` Ma--Wang wrapper for inner-window roots.
The upper bound `r <= 0` is derived from nonnegative coefficients, while the
lower bound `-1 <= r` is a sequence-specific certificate. -/
theorem prec_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun _ => X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_one_add_X_nonpos_of_mem_Icc (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X(1+X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun _ => X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_one_add_X_nonpos_of_mem_Icc (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X(1+X) P'` Ma--Wang wrapper for inner-window roots. -/
theorem prec_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
        (hc n) (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X(1+X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
        (hc n) (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `-c_n X(1+X) P'` Ma--Wang wrapper for outer-window roots. -/
theorem prec_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `-c_n X(1+X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X(1-X) P'` Ma--Wang wrapper where nonpositive roots of
the current row are derived internally from nonnegative coefficients. -/
theorem prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hnonneg hdeg_two
    (fun n _ hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos (hc n) hr)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the nonnegative-coefficient
`c_n X(1-X) P'` sequence-level Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hnonneg hdeg_two
    (fun n _ hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos (hc n) hr)
    hrec hdeg_lo hdeg_hi

namespace Tactic

macro "rr_mw_active_nonneg_at " n:term : tactic =>
  `(tactic| rr_scalar_active_nonneg_at $n)

macro "rr_mw_degree_from " hdeg:term : tactic =>
  `(tactic|
    solve
      | have hdeg' := $hdeg
        lia)

syntax (name := rr_ma_wang)
  "rr_ma_wang" " using " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_named)
  "rr_ma_wang" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_same)
  "rr_ma_wang_same" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_same_named)
  "rr_ma_wang_same" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_succ)
  "rr_ma_wang_succ" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_succ_named)
  "rr_ma_wang_succ" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos)
  "rr_mw_derivative_nonpos" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term :
  tactic

syntax (name := rr_mw_derivative_nonpos_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_degree_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_roots_nonpos_named)
  "rr_mw_derivative_sign_roots_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_nonneg_coeffs_named)
  "rr_mw_derivative_sign_nonneg_coeffs" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_nonneg_factor_named)
  "rr_mw_derivative_sign_nonneg_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_root_upper_named)
  "rr_mw_derivative_sign_root_upper" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_window_named)
  "rr_mw_derivative_sign_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_named)
  "rr_mw_derivative_X_mul" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_named)
  "rr_mw_derivative_C_mul_X_mul" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_window_named)
  "rr_mw_derivative_X_one_add_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_named)
  "rr_mw_derivative_neg_X_one_add_outer" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_named)
  "rr_mw_derivative_one_add_two_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_named)
  "rr_mw_derivative_neg_const" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_auto_named)
  "rr_mw_derivative_neg_const_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_named)
  "rr_mw_derivative_neg_X_sq" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_auto_named)
  "rr_mw_derivative_neg_X_sq_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_named)
  "rr_mw_derivative_nonpos_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_named)
  "rr_mw_derivative_neg_const_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_auto_named)
  "rr_mw_derivative_neg_const_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_named)
  "rr_mw_derivative_neg_const_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_const_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_named)
  "rr_mw_derivative_neg_X_sq_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_X_sequence_named)
  "rr_mw_derivative_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sub_one_sequence_named)
  "rr_mw_derivative_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_named)
  "rr_mw_derivative_nonpos_nonneg_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "den_nonzero" ":=" term ","
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "den_nonzero" ":=" term ","
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_on_roots_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_on_roots" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_on_roots" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_on_roots" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_sequence_nonneg_named)
  "rr_mw_derivative_X_mul_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_mul_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_nonneg_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_root_window_linear_facts) "rr_mw_root_window_linear_facts" : tactic

macro_rules
  | `(tactic| rr_mw_root_window_linear_facts) =>
      `(tactic|
        all_goals
          try
            have hroot_window_one_add_mul_nonneg : 0 ≤ 1 + r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_two_mul_nonneg : 0 ≤ 1 + 2 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_three_mul_nonneg : 0 ≤ 1 + 3 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_four_mul_nonneg : 0 ≤ 1 + 4 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_two_add_three_mul_nonneg : 0 ≤ 2 + 3 * r := by
              linarith only [hroot_window_lower])
  | `(tactic|
      rr_ma_wang using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_same
          $hf $hdegf $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_same using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_succ
          $hf $hdegf $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_succ using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_mw_derivative_nonpos using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hv_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_of_nonpos
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := $hf,
          degree_two := $hdegf,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          target_pos_lc := $hF_pos,
          source_pos_lc := $hf_pos,
          coeff_nonpos := $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_sign_roots_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hroot_nonpos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_nonpos : r ≤ 0 := $hroot_nonpos r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_nonneg_coeffs using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            ($hrr).2 $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by rr_sign_at_roots using $hrr, $hnn))
  | `(tactic|
      rr_mw_derivative_sign_nonneg_factor using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        factor_nonneg := $hfactor:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            ($hrr).2 $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by rr_sign_at_roots_with_factor using $hrr, $hnn, $hfactor))
  | `(tactic|
      rr_mw_derivative_sign_root_upper using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_lower := $hroot_lower r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_X_mul using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hq_nonneg:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_of_nonneg_on_roots
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hf_roots $hq_nonneg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hq_nonneg:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_of_nonneg_on_roots
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc $hf_roots $hq_nonneg)
  | `(tactic|
      rr_mw_derivative_X_one_add_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_one_add_X_of_roots_in_Icc
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_lo $hroot_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc $hroot_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        refine
          RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_ $hroot_hi
        <;> rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_one_add_two_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_lo $hroot_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hdeg_two $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hdeg_two $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_neg_const using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_const
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc)
  | `(tactic|
      rr_mw_derivative_neg_const_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        refine RealRooted.prec_mw_derivative_neg_const
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_
        <;> rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_neg_X_sq using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_C_mul_X_sq
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        refine RealRooted.prec_mw_derivative_neg_C_mul_X_sq
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_
        <;> rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence
          $hbase $hpos $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            $hbase $hpos $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | exact RealRooted.prec_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi
        | exact RealRooted.prec_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | refine RealRooted.prec_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n
        | refine RealRooted.prec_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_neg_const_sequence
              $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_neg_C_sequence
              $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_neg_const_sequence
                $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n)
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_neg_C_sequence
                $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | exact RealRooted.prec_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi
        | exact RealRooted.prec_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi
        | exact RealRooted.prec_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | refine RealRooted.prec_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n
        | refine RealRooted.prec_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n
        | refine RealRooted.prec_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_neg_X_sq_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
              $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
              $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
              $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
                $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n)
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
                $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n)
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine
                RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
                $hbase $hpos $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_one_add_X_sequence
          $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_sequence
            $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | exact RealRooted.prec_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi
        | exact RealRooted.prec_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | refine RealRooted.prec_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n
        | refine RealRooted.prec_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
              $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
              $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
                $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n)
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
                $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_X_sub_one_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_sub_one_sequence
          $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sub_one_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | exact RealRooted.prec_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi
        | exact RealRooted.prec_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | refine RealRooted.prec_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n
        | refine RealRooted.prec_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
              $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
        | rr_exact_realrooted_sequence_or_projection
            (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
              $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        first
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
                $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n)
        | rr_exact_realrooted_sequence_or_projection
            (by
              refine RealRooted.isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
                $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi <;>
              intro n <;>
              rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_of_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_of_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two
          (by intro n r hr; rr_sign) $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two
            (by intro n r hr; rr_sign) $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hrec
            (by intro n r hr hroot_nonpos; rr_sign)
            (by intro n r hr hroot_nonpos; rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hrec
            (by intro n r hr hroot_nonpos; rr_sign)
            (by intro n r hr hroot_nonpos; rr_sign)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_of_root_window
            $hbase $hpos $hdeg_two $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_window
            $hbase $hpos $hdeg_two $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n r hr; rr_sign)
            (by intro n r hr; rr_sign)
            $hden $hcoeffV $hcoeffW
            (by
              intro n
              simpa [add_comm, add_left_comm, add_assoc] using $hraw n)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n r hr; rr_sign)
            (by intro n r hr; rr_sign)
            $hden $hcoeffV $hcoeffW
            (by
              intro n
              simpa [add_comm, add_left_comm, add_assoc] using $hraw n)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n; rr_mw_active_nonneg_at n)
            $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hden $hcoeffV $hcoeffW
            (by
              intro n
              simpa [add_comm, add_left_comm, add_assoc] using $hraw n)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n; rr_mw_active_nonneg_at n)
            $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hden $hcoeffV $hcoeffW
            (by
              intro n
              simpa [add_comm, add_left_comm, add_assoc] using $hraw n)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two ?_ $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n r hr; rr_sign)
            $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n r hr; rr_sign)
            $hden $hcoeff
            (by
              intro n
              simpa [add_comm, add_left_comm, add_assoc] using $hraw n)
            $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine
              RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
                (c := $c) $hbase $hpos $hnonneg $hdeg_two ?_ $hV $hden $hcoeff
                $hraw $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n r hr; rr_sign)
            $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            (by intro n; rr_mw_active_nonneg_at n)
            (by intro n r hr; rr_sign)
            $hden $hcoeff
            (by
              intro n
              simpa [add_comm, add_left_comm, add_assoc] using $hraw n)
            $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_on_roots using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_on_roots := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_on_roots := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_mul_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_mul_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine RealRooted.prec_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
              $hbase $hpos $hnonneg $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two ?_ $hQ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine
              RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
                $hbase $hpos $hnonneg $hdeg_two ?_ $hQ $hrec $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine
          RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two ?_ $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine
              isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
                (c := $c) $hbase $hpos $hnonneg $hdeg_two ?_ $hQ $hden $hcoeff
                $hraw $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hroot_lower $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_one_add_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hroot_lower $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hroot_lower
            $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine
          RealRooted.prec_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two ?_ $hroot_lower
            $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine
              isRealRooted_of_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
                $hbase $hpos $hnonneg $hdeg_two ?_ $hroot_lower
                $hrec $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
          $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
          $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine
              RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
                $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence
          $hbase $hpos $hdeg_two $hc $hroots $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence
          $hbase $hpos $hdeg_two ?_ $hroots $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          roots_nonpos := $hroots,
          recurrence := $hrec,
          degree_lower := (by
            intro n
            rr_mw_degree_from (($hdeg) n)),
          degree_upper := (by
            intro n
            rr_mw_degree_from (($hdeg) n)))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        refine
          RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
          <;> intro n <;> rr_mw_active_nonneg_at n)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos $hdeg_two $hc $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence
              $hbase $hpos $hdeg_two ?_ $hroots $hrec $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            refine
              isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
                $hbase $hpos $hnonneg $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi
              <;> intro n <;> rr_mw_active_nonneg_at n))

end Tactic
end RealRooted
