import RealRooted.PosCombo
import RealRooted.AffineFamily
import RealRooted.Tactic.Finish
import RealRooted.Tactic.Lookup

/-!
# Wagner `X`-shift core

The basic Wagner bridge and derivative-gap recurrence backends.
-/

open Polynomial

namespace RealRooted

/-- Derivative-lag bridge for later mixed lag recurrences.

If `f` is real-rooted with nonnegative coefficients, then `X * f'` is in
proper position with `X * f`.  This packages derivative interlacing together
with the Wagner common-`X` multiplication bridge. -/
theorem prec_X_mul_derivative_X_mul_self_of_splits_nonneg {f : ℝ[X]}
    (hf : f.Splits)
    (hdeg : 2 ≤ f.natDegree)
    (hfnn : HasNonnegCoeffs f) :
    Prec (X * f.derivative) (X * f) :=
  prec_mul_X_both_of_prec_of_nonneg
    (derivative_interlaces hf hdeg).toPrec hfnn.derivative hfnn

/-- Wagner derivative-gap-lag step.

If `f ≪ g`, then the derivative of `g` also precedes `g`, and Wagner's
positive-cone theorem puts `c g' + a f` before `g`.  Multiplication by `X`
then gives the active-row step behind recurrences
`P_{n+2} = X * (c_n P'_{n+1} + a_n P_n)`. -/
theorem prec_wagner_derivative_gap_lag_step {f g : ℝ[X]} {a c : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c) :
    Prec g (X * (C c * g.derivative + C a * f)) := by
  have hg_pos : HasPosLeadingCoeff g := by rr_pos_lc using nonzero := right_ne_zero_of_prec h
  have hf_pos : HasPosLeadingCoeff f := by rr_pos_lc using nonzero := left_ne_zero_of_prec h
  have hg_der_pos : HasPosLeadingCoeff g.derivative := hg_pos.derivative (by lia)
  have hder : Prec g.derivative g := (derivative_interlaces (right_splits_of_prec h) hdeg).toPrec
  have hnonneg : ∀ ap ∈ [(c, g.derivative), (a, f)], 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hc.le
    rcases List.mem_cons.mp hap with rfl | hap
    · exact ha.le
    · cases hap
  have hprec : ∀ ap ∈ [(c, g.derivative), (a, f)], Prec ap.2 g := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hder
    rcases List.mem_cons.mp hap with rfl | hap
    · exact h
    · cases hap
  have hpoly_pos :
      ∀ ap ∈ [(c, g.derivative), (a, f)], HasPosLeadingCoeff ap.2 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hg_der_pos
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hf_pos
    · cases hap
  have hex : ∃ ap ∈ [(c, g.derivative), (a, f)], 0 < ap.1 :=
    ⟨(c, g.derivative), by simp, hc⟩
  have hsum_prec : Prec (weightedSum [(c, g.derivative), (a, f)]) g :=
    prec_weightedSum_right [(c, g.derivative), (a, f)] g
      hnonneg hprec hpoly_pos hex
  have hsum_nonneg : HasNonnegCoeffs (C c * g.derivative + C a * f) := by
    rr_nonneg_coeffs using hgnn.derivative, hfnn
  have hsum_nonneg_weighted :
      HasNonnegCoeffs (weightedSum [(c, g.derivative), (a, f)]) := by
    simpa [weightedSum, add_assoc] using hsum_nonneg
  simpa [weightedSum, add_assoc] using
    (prec_mul_X_of_prec_of_nonneg hsum_prec hsum_nonneg_weighted hgnn)

/-- Scalar-left Wagner derivative-gap-lag step.

This is the same bridge as `prec_wagner_derivative_gap_lag_step`, but the
recurrence may be supplied in the unnormalized form
`d * p = X * (c * g' + a * f)`. -/
theorem prec_wagner_derivative_gap_lag_step_den {f g p : ℝ[X]} {a c d : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c)
    (hd : 0 < d)
    (hrec : C d * p = X * (C c * g.derivative + C a * f)) :
    Prec g p := by
  have hstep : Prec g (X * (C c * g.derivative + C a * f)) :=
    prec_wagner_derivative_gap_lag_step h hfnn hgnn hdeg ha hc
  have hscaled : Prec g (C d * p) := by simpa [hrec] using hstep
  have hscaled' : Prec g (C d⁻¹ * (C d * p)) :=
    prec_C_mul_right hscaled (inv_ne_zero hd.ne')
  have hnormalize : C d⁻¹ * (C d * p) = p := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hd.ne']
    simp
  simpa [hnormalize] using hscaled'

/-- Sequence induction for active Wagner derivative-gap-lag recurrences.

Use this after any exceptional startup rows have been absorbed into the base
case, so that the derivative and lag coefficients are both positive on the
indexed range. -/
theorem prec_wagner_derivative_gap_lag_sequence {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  have hstep :
      Prec (P (n + 1))
        (X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :=
    prec_wagner_derivative_gap_lag_step
      hprev (hnonneg n) (hnonneg (n + 1)) (hdeg n) (ha n) (hc n)
  simpa [← hrec n] using hstep

/-- Real-rootedness corollary for active Wagner derivative-gap-lag recurrences. -/
theorem isRealRooted_of_prec_wagner_derivative_gap_lag_sequence
    {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    prec_wagner_derivative_gap_lag_sequence hbase hnonneg hdeg ha hc hrec

/-- Sequence induction for scalar-left active Wagner derivative-gap-lag recurrences. -/
theorem prec_wagner_derivative_gap_lag_sequence_den
    {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  exact
    prec_wagner_derivative_gap_lag_step_den
      hprev (hnonneg n) (hnonneg (n + 1)) (hdeg n) (ha n) (hc n) (hd n)
      (hrec n)

/-- Real-rootedness corollary for scalar-left active Wagner gap-lag recurrences. -/
theorem isRealRooted_of_prec_wagner_derivative_gap_lag_sequence_den
    {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    prec_wagner_derivative_gap_lag_sequence_den hbase hnonneg hdeg ha hc hd hrec



end RealRooted
