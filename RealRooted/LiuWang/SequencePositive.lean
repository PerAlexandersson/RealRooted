module

import RealRooted.LiuWang.SequenceCore
import RealRooted.RootBounds
import RealRooted.SignEvaluation
import RealRooted.SequenceClosure
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Positive-lag Liu--Wang sequence theorems

Sequence criteria for positive linear and affine lag coefficients.
-/

public section

open Polynomial

namespace RealRooted.LiuWang

/-- Sequence-level positive `t`-lag Liu--Wang induction.

This is the reusable full proof shell for strict degree-increasing recurrences
of the form
`P_{n+2} = A_n P_{n+1} + c_n X P_n`.
The sequence-specific file supplies the base interlacing, recurrence identity,
coefficient/degree certificates, and no-common-root hypothesis. -/
theorem strictInterl_positive_t_lag_sequence {P : Nat → ℝ[X]}
    {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_nonpos_lag_sequence_of_inductive_nonpos
    (B := fun n => C (c n) * X) hbase hpos
    (fun n hsource r hr =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n)
        (roots_nonpos_of_realrooted_of_nonneg_coeffs
          hsource (hnonneg (n + 1)) r hr))
    hrec hdeg_succ hno

end RealRooted.LiuWang
