module

import RealRooted.Derivative.Algebra
import RealRooted.Derivative.Interlacing
public import RealRooted.LiuWang.FiniteFamily

/-!
# Liu--Wang derivative-lag recursions

This file packages the common recurrence

```text
P_{n+2} = U_n P_{n+1} + V_n P'_{n+1} + W_n P_n
```

as a direct backend theorem.  The lag term `P_n` is the distinguished
Liu--Wang interlacer, while the derivative term is handled as an additional
interlacer of the current row.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.LiuWang

/-- One-step Liu--Wang recursion with an additional derivative term.

The lag polynomial `g` is the distinguished interlacer.  The derivative
`f.derivative` is only used as a tail interlacer, so this theorem does not need
`f` to be squarefree.  No degree hypothesis is needed: `Interlaces g f` forces
`f` to be nonconstant. -/
theorem strictInterl_derivative_lag_of_nonpos {f g u v w : ℝ[X]}
    (hf : f.Splits)
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative + w * g))
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative + w * g).natDegree)
    (hdeg_hi : (u * f + v * f.derivative + w * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0)
    (hw_nonpos : ∀ r, f.IsRoot r → w.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative + w * g) := by
  exact (fun _ : (∀ r, f.IsRoot r → ¬ g.IsRoot r) ↦
    strictInterl_derivative_lag_of_eval_nonpos
      hf_pos.ne_zero hf hf_pos hgf.toStrictInterl hg_pos
      hF_pos hdeg_lo hdeg_hi hv_nonpos hw_nonpos) hno

/-- General sequence criterion for derivative--lag recurrences.  The degree may
stay fixed or rise by one, and consecutive rows may share roots. -/
theorem strictInterl_derivative_lag_sequence_of_eval_nonpos_of_splits
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := ih.2.1
      have hstep := strictInterl_derivative_lag_of_eval_nonpos
        hsource.1 hsource.2 (hpos (n + 1)) ih (hpos n)
        (hrec n ▸ hpos (n + 2)) (hrec n ▸ hdeg_lo n) (hrec n ▸ hdeg_hi n)
        (hV_nonpos n hsource) (hW_nonpos n hsource)
      rwa [← hrec n] at hstep

/-- Sequence-level Liu--Wang induction for derivative-lag recurrences where
the sign checks may use the current row's already proved real-rootedness. -/
theorem strictInterl_derivative_lag_sequence_of_root_signs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  exact (fun _ : (∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) ↦
    strictInterl_derivative_lag_sequence_of_eval_nonpos_of_splits
      hbase hpos hrec hV_nonpos hW_nonpos
      (fun n ↦ by rw [← hdeg_succ (n + 1)]; lia)
      (fun n ↦ by rw [← hdeg_succ (n + 1)])) hno

/-- Sequence-level Liu--Wang induction with direct root-sign side conditions. -/
theorem strictInterl_derivative_lag_sequence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_derivative_lag_sequence_of_root_signs
    hbase hpos hrec
    (fun n _ r hr => hV_nonpos n r hr)
    (fun n _ r hr => hW_nonpos n r hr)
    hdeg_succ hno

/-- Sequence-level Liu--Wang induction where the two sign checks are certified
on an explicit root window. -/
theorem strictInterl_derivative_lag_sequence_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {lo hi : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
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
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_derivative_lag_sequence
    hbase hpos hrec
    (fun n r hr => hV_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    (fun n r hr => hW_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hdeg_succ hno

/-- Real-rootedness corollary for derivative-lag Liu--Wang induction where the
sign checks may use the current row's already proved real-rootedness. -/
theorem isRealRooted_of_derivative_lag_sequence_of_root_signs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hstrictInterl : ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
    strictInterl_derivative_lag_sequence_of_root_signs
      hbase hpos hrec hV_nonpos hW_nonpos hdeg_succ hno
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hstrictInterl n).2.1

/-- Real-rootedness corollary for derivative-lag Liu--Wang induction with
direct root-sign side conditions. -/
theorem isRealRooted_of_derivative_lag_sequence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
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
  isRealRooted_of_derivative_lag_sequence_of_root_signs
    hbase hpos hrec
    (fun n _ r hr => hV_nonpos n r hr)
    (fun n _ r hr => hW_nonpos n r hr)
    hdeg_succ hno

/-- Real-rootedness corollary for derivative-lag Liu--Wang induction on an
explicit root window. -/
theorem isRealRooted_of_derivative_lag_sequence_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {lo hi : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
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
  isRealRooted_of_derivative_lag_sequence
    hbase hpos hrec
    (fun n r hr => hV_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    (fun n r hr => hW_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hdeg_succ hno

end RealRooted.LiuWang

namespace RealRooted

end RealRooted
