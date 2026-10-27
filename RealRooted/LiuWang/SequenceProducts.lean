module

import RealRooted.LiuWang.SequencePositive
import RealRooted.LiuWang.SequenceCore
import RealRooted.RootBounds
import RealRooted.SignEvaluation
import RealRooted.SequenceClosure
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Product-lag Liu--Wang sequence theorems

Sequence criteria for factored lags and fixed current-row coefficients.
-/

public section

open Polynomial

namespace RealRooted.LiuWang

/-- Sequence-level `X Q_n` positive-lag Liu--Wang induction.

The current-row root bound `r <= 0` is derived internally from real-rootedness
and nonnegative coefficients.  The sequence-specific certificate is only the
remaining factor inequality `0 <= Q_n(r)` at roots of the current row. -/
theorem strictInterl_positive_X_mul_lag_sequence {P : Nat → ℝ[X]}
    {A Q : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => X * Q n) hbase hpos
    (fun n hsource r hr =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr)
        (hQ_nonneg n r hr))
    hrec hdeg_succ hno

/-- Real-rootedness corollary for sequence-level `X Q_n` positive-lag
Liu--Wang induction. -/
theorem isRealRooted_of_positive_X_mul_lag_sequence {P : Nat → ℝ[X]}
    {A Q : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_strictInterl_chain_from_step <|
    strictInterl_positive_X_mul_lag_sequence
      hbase hpos hnonneg hQ_nonneg hrec hdeg_succ hno

/-- Sequence-level positive `t`-lag induction for current factor `1+X`. -/
theorem strictInterl_current_one_add_X_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_positive_t_lag_sequence
    (A := fun _ => (1 + X : ℝ[X])) hbase hpos hnonneg hc hrec hdeg_succ hno

end RealRooted.LiuWang

namespace RealRooted

end RealRooted
