import RealRooted.Tactic.WagnerX

/-!
# Wagner `X`-shift tactic examples

Smoke tests for the same-degree plateau bridge used by positive `t`-lag
recurrences.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : 0 < c) : 0 < c := by
  rr_wagner_pos

example {n : Nat} : 0 < (n : ℝ) + 1 := by
  rr_wagner_pos

example {n : Nat} (hn : 0 < n) : 0 < (n : ℝ) := by
  rr_wagner_pos

example : 0 < (2 : ℝ) :=
  rr_wagner_pos_term

example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rr_prec_mul_X using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn

example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rr_prec_mul_X

/-- Narayana/singleton-free-set-partition style common `X` factor:
nonnegative coefficients discharge the root-nonpositive side conditions. -/
example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec (X * f) (X * g) := by
  rr_prec_mul_X_both using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn

example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec (X * f) (X * g) := by
  rr_prec_mul_X_both

example {f g : ℝ[X]} {c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hc : c ≠ 0) :
    Prec g ((C c * X) * f) := by
  rr_prec_C_mul_X using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    coeff_ne := hc

example {f g : ℝ[X]} {c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hc : c ≠ 0) :
    Prec g ((C c * X) * f) := by
  rr_prec_C_mul_X using coeff_ne := hc

example {f g : ℝ[X]} {c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hc : 0 < c) :
    Prec g ((C c * X) * f) := by
  rr_prec_C_mul_X using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    coeff_pos := hc

example {f g : ℝ[X]} {c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hc : 0 < c) :
    Prec g ((C c * X) * f) := by
  rr_prec_C_mul_X using coeff_pos := hc

/-- Derivative-lag bridge: a nonnegative real-rooted row gives
`X * P'_n ≪ X * P_n`. -/
example {f : ℝ[X]}
    (hf : f.Splits)
    (hdeg : 2 ≤ f.natDegree)
    (hfnn : HasNonnegCoeffs f) :
    Prec (X * f.derivative) (X * f) := by
  rr_prec_X_derivative_X_self using
    splits := hf,
    degree_two := hdeg,
    nonneg_coeffs := hfnn

example {f : ℝ[X]}
    (hf : f.Splits)
    (hdeg : 2 ≤ f.natDegree)
    (hfnn : HasNonnegCoeffs f) :
    Prec (X * f.derivative) (X * f) := by
  rr_prec_X_derivative_X_self

namespace WagnerXInferenceSmoke

@[rr_base_prec] theorem one_prec_one : Prec (1 : ℝ[X]) 1 :=
  prec_refl (by simp) (by simp)

@[rr_nonneg] theorem one_nonneg : HasNonnegCoeffs (1 : ℝ[X]) :=
  hasNonnegCoeffs_one

@[rr_nonneg] theorem zero_nonneg : HasNonnegCoeffs (0 : ℝ[X]) :=
  hasNonnegCoeffs_zero

example : Prec (1 : ℝ[X]) (X * 1) := by
  rr_prec_mul_X

end WagnerXInferenceSmoke

/-- Plateau sequence bridge: from the adjacent `Prec` invariant on
`P_n,P_{n+1}`, the Wagner `X`-shift gives the positive-lag target
`P_{n+1} ≪ X P_n` without requiring a differ-by-one `Interlaces` certificate. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hprev : Prec (P n) (P (n + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k)) :
    Prec (P (n + 1)) (X * P n) := by
  rr_prec_mul_X using
    proper := hprev,
    left_nonneg := hnonneg n,
    right_nonneg := hnonneg (n + 1)

example {P : Nat → ℝ[X]} {n : Nat}
    (hprev : Prec (P n) (P (n + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k)) :
    Prec (P (n + 1)) (X * P n) := by
  rr_prec_mul_X

/-- OEIS-style scalar positive-lag bridge for recurrences with
`c_n t P_{n-2}`. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {n : Nat}
    (hprev : Prec (P n) (P (n + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hc : 0 < c n) :
    Prec (P (n + 1)) ((C (c n) * X) * P n) := by
  rr_prec_C_mul_X using
    proper := hprev,
    left_nonneg := hnonneg n,
    right_nonneg := hnonneg (n + 1),
    coeff_pos := hc

/-- OEIS shapes `A052553`/`A061896`/`A169803`:
`P_n = P_{n-1} + t P_{n-2}`. -/
example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec g (g + X * f) := by
  rr_prec_pos_X_lag_combo using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    current_coeff_pos := (rr_wagner_pos_term : 0 < (1 : ℝ)),
    lag_coeff_pos := (rr_wagner_pos_term : 0 < (1 : ℝ))

/-- OEIS shape `A201701`: `P_n = 2 P_{n-1} + t P_{n-2}`. -/
example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec g (C (2 : ℝ) * g + X * f) := by
  rr_prec_pos_X_lag_combo using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    current_coeff_pos := (rr_wagner_pos_term : 0 < (2 : ℝ)),
    lag_coeff_pos := (rr_wagner_pos_term : 0 < (1 : ℝ))

/-- OEIS shape `A106828`: `P_n = n P_{n-1} + n t P_{n-2}` on the
active range `0 < n`. -/
example {f g : ℝ[X]} {n : Nat}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hn : 0 < n) :
    Prec g (C (n : ℝ) * g + (C (n : ℝ) * X) * f) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  rr_prec_pos_X_lag_combo using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    current_coeff_pos := hn_pos,
    lag_coeff_pos := hn_pos

/-- Active-range scalar lag: `P_n = P_{n-1} + (c-2)t P_{n-2}` for
`2 <= c`. -/
example {f g : ℝ[X]} {c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hc : (2 : ℝ) ≤ c) :
    Prec g (g + (C (c - 2) * X) * f) := by
  have hlag : 0 ≤ c - 2 := sub_nonneg.mpr hc
  rr_prec_pos_X_lag_combo using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    current_coeff_pos := (rr_wagner_pos_term : 0 < (1 : ℝ)),
    lag_coeff_nonneg := hlag

/-- Sequence-level scalar positive-lag step.  This is the compact proof shape
for plateau recurrences once the recurrence has been normalized to scalar
coefficients on `P_{n+1}` and `t P_n`. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ} {n : Nat}
    (hprev : Prec (P n) (P (n + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (ha : 0 < a n)
    (hc : 0 ≤ c n) :
    Prec (P (n + 1)) (C (a n) * P (n + 1) + (C (c n) * X) * P n) := by
  rr_prec_pos_X_lag_combo using
    proper := hprev,
    left_nonneg := hnonneg n,
    right_nonneg := hnonneg (n + 1),
    current_coeff_pos := ha,
    lag_coeff_nonneg := hc

/-- Full sequence shell for `A052553`/`A061896`/`A169803`:
`P_{n+2}=P_{n+1}+tP_n`. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_pos_X_lag_sequence_auto using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-- Explicit-coefficient form of the same positive-`X` lag shell. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat,
      P (n + 2) = C (1 : ℝ) * P (n + 1) + (C (1 : ℝ) * X) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_pos_X_lag_sequence using
    base := hbase,
    nonneg_coeffs := hnonneg,
    current_coeff_pos := rr_side_pos_seq_term,
    lag_coeff_nonneg := rr_side_nonneg_seq_term,
    recurrence := hrec

/-- Real-rootedness corollary for the same `P_{n+2}=P_{n+1}+tP_n` shell. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_pos_X_lag_sequence_realrooted_auto using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-- Explicit-coefficient real-rootedness endpoint for the positive-`X` shell. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat,
      P (n + 2) = C (1 : ℝ) * P (n + 1) + (C (1 : ℝ) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_pos_X_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    current_coeff_pos := rr_side_pos_seq_term,
    lag_coeff_nonneg := rr_side_nonneg_seq_term,
    recurrence := hrec

/-- Projection endpoint for the same positive-`X` lag shell. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_prec_pos_X_lag_sequence_realrooted_auto using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-- Full sequence shell for `A201701`: `P_{n+2}=2P_{n+1}+tP_n`. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat, P (n + 2) = C (2 : ℝ) * P (n + 1) + X * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_pos_X_unit_lag_sequence_auto using
    current_coeff := fun _ => (2 : ℝ),
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-- Real-rootedness endpoint for the same `A201701` unit-lag shell. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat, P (n + 2) = C (2 : ℝ) * P (n + 1) + X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_pos_X_unit_lag_sequence_realrooted_auto using
    current_coeff := fun _ => (2 : ℝ),
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-- Full sequence shell for active scalar families such as
`P_{n+2}=(n+1)P_{n+1}+(n+1)tP_n`. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat,
      P (n + 2) = C ((n : ℝ) + 1) * P (n + 1) +
        (C ((n : ℝ) + 1) * X) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_pos_X_same_coeff_sequence_auto using
    shared_coeff := fun n => (n : ℝ) + 1,
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-- Real-rootedness endpoint for the active same-coefficient shell. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hrec : ∀ n : Nat,
      P (n + 2) = C ((n : ℝ) + 1) * P (n + 1) +
        (C ((n : ℝ) + 1) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_pos_X_same_coeff_sequence_realrooted_auto using
    shared_coeff := fun n => (n : ℝ) + 1,
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec

/-!
### Wagner derivative-gap-lag step

These examples cover the active range of recurrences of the form
`P_{n+2} = X * (c_n P'_{n+1} + a_n P_n)`, together with the scalar-left
variant `d_n P_{n+2} = X * (c_n P'_{n+1} + a_n P_n)`.
-/

/-- Single active Wagner derivative-gap-lag step. -/
example {f g : ℝ[X]} {a c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c) :
    Prec g (X * (C c * g.derivative + C a * f)) := by
  rr_prec_wagner_derivative_gap_lag using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc

/-- The same step can infer all certificates once the displayed target fixes
the two polynomials and both scalar coefficients. -/
example {f g : ℝ[X]} {a c : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c) :
    Prec g (X * (C c * g.derivative + C a * f)) := by
  rr_prec_wagner_derivative_gap_lag

/-- Indexed local families supply the active step without pointwise aliases. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ} {n : Nat}
    (hprev : Prec (P n) (P (n + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ k : Nat, 2 ≤ (P (k + 1)).natDegree)
    (ha : ∀ k : Nat, 0 < a k)
    (hc : ∀ k : Nat, 0 < c k) :
    Prec (P (n + 1))
      (X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) := by
  rr_prec_wagner_derivative_gap_lag

/-- Shifted families may instantiate offset certificate families and mix
indexed with arithmetic scalar bounds. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {n : Nat}
    (hchain : ∀ k : Nat, Prec (P k) (P (k + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ k : Nat, 2 ≤ (P (k + 1)).natDegree)
    (ha : ∀ k : Nat, 0 < a k) :
    Prec (P (n + 4))
      (X * (C ((n : ℝ) + 4) * (P (n + 4)).derivative +
        C (a (n + 3)) * P (n + 3))) := by
  rr_prec_wagner_derivative_gap_lag

/-- A recurrence rewrite exposes the rigid target consumed by the bare step. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hprev : Prec (P n) (P (n + 1)))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ k : Nat, 2 ≤ (P (k + 1)).natDegree)
    (hrec : ∀ k : Nat,
      P (k + 2) = X * (C (1 : ℝ) * (P (k + 1)).derivative +
        C ((k : ℝ) + 1) * P k)) :
    Prec (P (n + 1)) (P (n + 2)) := by
  rw [hrec n]
  rr_prec_wagner_derivative_gap_lag

/-- Scalar-left single-step wrapper for unnormalized recurrence certificates. -/
example {f g p : ℝ[X]} {a c d : ℝ}
    (hfg : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c)
    (hd : 0 < d)
    (hrec : C d * p = X * (C c * g.derivative + C a * f)) :
    Prec g p := by
  rr_prec_wagner_derivative_gap_lag_den using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec

/-- Active-range sequence shell for normalized Wagner derivative-gap-lag rows. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_wagner_derivative_gap_lag_sequence using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec

/-- Real-rootedness endpoint for the normalized active-range shell. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec

/-- Projection endpoint for the normalized derivative-gap shell. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec

/-- Active-offset `A358623`/`A124324` shape:
`P_{n+2}=t(P'_{n+1}+(n+1)P_n)`. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        X * (C (1 : ℝ) * (P (n + 1)).derivative + C ((n : ℝ) + 1) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := rr_wagner_pos_seq,
    derivative_coeff_pos := rr_wagner_pos_seq,
    recurrence := hrec

/-- `A358623`, active offset: the recurrence
`P_{n+5}=t(P'_{n+4}+(n+4)P_{n+3})` preserves the shifted adjacent
`Prec` invariant from the base pair `P_3 ≪ P_4`. -/
theorem a358623_activeOffset_prec {P : Nat → ℝ[X]}
    (hbase : Prec (P 3) (P 4))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 4)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 5) =
        X * (C (1 : ℝ) * (P (n + 4)).derivative + C ((n : ℝ) + 4) * P (n + 3))) :
    ∀ n : Nat, Prec (P (n + 3)) (P (n + 4)) := by
  let Q : Nat → ℝ[X] := fun n => P (n + 3)
  have hQbase : Prec (Q 0) (Q 1) := by
    simpa [Q] using hbase
  have hQnonneg : ∀ n : Nat, HasNonnegCoeffs (Q n) := by
    intro n
    simpa [Q] using hnonneg (n + 3)
  have hQdeg : ∀ n : Nat, 2 ≤ (Q (n + 1)).natDegree := by
    intro n
    simpa [Q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdeg n
  have hQrec : ∀ n : Nat,
      Q (n + 2) =
        X * (C (1 : ℝ) * (Q (n + 1)).derivative + C ((n : ℝ) + 4) * Q n) := by
    intro n
    simpa [Q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec n
  have hQprec : ∀ n : Nat, Prec (Q n) (Q (n + 1)) := by
    rr_prec_wagner_derivative_gap_lag_sequence using
      base := hQbase,
      nonneg_coeffs := hQnonneg,
      degree_two := hQdeg,
      lag_coeff_pos := rr_wagner_pos_seq,
      derivative_coeff_pos := rr_wagner_pos_seq,
      recurrence := hQrec
  intro n
  simpa [Q] using hQprec n

/-- `A358623`, active offset: real-rootedness of all shifted active rows
`P_{n+3}` from the same base and recurrence certificates. -/
theorem a358623_activeOffset_realRooted {P : Nat → ℝ[X]}
    (hbase : Prec (P 3) (P 4))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 4)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 5) =
        X * (C (1 : ℝ) * (P (n + 4)).derivative + C ((n : ℝ) + 4) * P (n + 3))) :
    ∀ n : Nat, P (n + 3) ≠ 0 ∧ (P (n + 3)).Splits := by
  let Q : Nat → ℝ[X] := fun n => P (n + 3)
  have hQbase : Prec (Q 0) (Q 1) := by
    simpa [Q] using hbase
  have hQnonneg : ∀ n : Nat, HasNonnegCoeffs (Q n) := by
    intro n
    simpa [Q] using hnonneg (n + 3)
  have hQdeg : ∀ n : Nat, 2 ≤ (Q (n + 1)).natDegree := by
    intro n
    simpa [Q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdeg n
  have hQrec : ∀ n : Nat,
      Q (n + 2) =
        X * (C (1 : ℝ) * (Q (n + 1)).derivative + C ((n : ℝ) + 4) * Q n) := by
    intro n
    simpa [Q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec n
  have hQrr : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits := by
    rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
      base := hQbase,
      nonneg_coeffs := hQnonneg,
      degree_two := hQdeg,
      lag_coeff_pos := rr_wagner_pos_seq,
      derivative_coeff_pos := rr_wagner_pos_seq,
      recurrence := hQrec
  intro n
  simpa [Q] using hQrr n

/-- Shifted recurrence-defined active family for `A358623`.

This models the rows `P_{n+3}` after the zero row and first degree-one step
have been absorbed into the base case. -/
def a358623Shifted : Nat → ℝ[X]
  | 0 => X
  | 1 => X * (1 + C (3 : ℝ) * X)
  | n + 2 =>
      X * (C (1 : ℝ) * (a358623Shifted (n + 1)).derivative +
        C ((n : ℝ) + 4) * a358623Shifted n)

@[simp] lemma a358623Shifted_zero : a358623Shifted 0 = X := rfl

@[simp] lemma a358623Shifted_one :
    a358623Shifted 1 = X * (1 + C (3 : ℝ) * X) := rfl

lemma a358623Shifted_succ_succ (n : Nat) :
    a358623Shifted (n + 2) =
      X * (C (1 : ℝ) * (a358623Shifted (n + 1)).derivative +
        C ((n : ℝ) + 4) * a358623Shifted n) := by
  rfl

/-- Concrete base certificate for the shifted `A358623` active family. -/
lemma a358623Shifted_base : Prec (a358623Shifted 0) (a358623Shifted 1) := by
  have hlin : Interlaces (1 : ℝ[X]) (1 + C (3 : ℝ) * X) :=
    interlaces_one_linear (by
      simpa [add_comm] using
        (Polynomial.natDegree_linear (a := (3 : ℝ)) (b := (1 : ℝ)) (by simp)))
  have hprec : Prec (1 : ℝ[X]) (1 + C (3 : ℝ) * X) := hlin.toPrec
  have hlin_nonneg : HasNonnegCoeffs (1 + C (3 : ℝ) * X) := by
    rr_nonneg_coeffs
  have hmul : Prec (X * (1 : ℝ[X])) (X * (1 + C (3 : ℝ) * X)) := by
    rr_prec_mul_X_both using
      proper := hprec,
      left_nonneg := hasNonnegCoeffs_one,
      right_nonneg := hlin_nonneg
  simpa using hmul

/-- Nonnegative coefficients for every shifted `A358623` active row. -/
theorem a358623Shifted_nonneg : ∀ n : Nat, HasNonnegCoeffs (a358623Shifted n)
  | 0 => by simpa using hasNonnegCoeffs_X
  | 1 => by
      rw [a358623Shifted_one]
      rr_nonneg_coeffs
  | n + 2 => by
      rw [a358623Shifted_succ_succ]
      rr_nonneg_coeffs using
        a358623Shifted_nonneg (n + 1),
        a358623Shifted_nonneg n

lemma a358623Shifted_coeff_zero :
    ∀ n : Nat, (a358623Shifted n).coeff 0 = 0
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [a358623Shifted_succ_succ]

lemma a358623Shifted_coeff_one : ∀ n : Nat, (a358623Shifted n).coeff 1 = 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      simp [a358623Shifted_succ_succ, coeff_derivative,
        a358623Shifted_coeff_zero n, a358623Shifted_coeff_one (n + 1)]

lemma a358623Shifted_coeff_two_pos_succ :
    ∀ n : Nat, 0 < (a358623Shifted (n + 1)).coeff 2
  | 0 => by simp [a358623Shifted_one, coeff_one]
  | n + 1 => by
      have hprev : 0 < (a358623Shifted (n + 1)).coeff 2 :=
        a358623Shifted_coeff_two_pos_succ n
      have hone : (a358623Shifted n).coeff 1 = 1 :=
        a358623Shifted_coeff_one n
      rw [a358623Shifted_succ_succ, coeff_X_mul, coeff_add, coeff_C_mul,
        coeff_C_mul, coeff_derivative, hone]
      norm_num
      nlinarith [hprev, show (0 : ℝ) < (n : ℝ) + 4 by positivity]

/-- Active shifted rows have degree at least two, as required by Rolle. -/
lemma a358623Shifted_degree_two_succ (n : Nat) :
    2 ≤ (a358623Shifted (n + 1)).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (ne_of_gt (a358623Shifted_coeff_two_pos_succ n))

/-- Adjacent `Prec` invariant for the shifted recurrence-defined `A358623`
active family. -/
theorem a358623Shifted_prec :
    ∀ n : Nat, Prec (a358623Shifted n) (a358623Shifted (n + 1)) := by
  rr_prec_wagner_derivative_gap_lag_sequence using
    base := a358623Shifted_base,
    nonneg_coeffs := a358623Shifted_nonneg,
    degree_two := a358623Shifted_degree_two_succ,
    lag_coeff_pos := rr_wagner_pos_seq,
    derivative_coeff_pos := rr_wagner_pos_seq,
    recurrence := a358623Shifted_succ_succ

/-- Real-rootedness of the shifted recurrence-defined `A358623` active family. -/
theorem a358623Shifted_realRooted :
    ∀ n : Nat, a358623Shifted n ≠ 0 ∧ (a358623Shifted n).Splits := by
  rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
    base := a358623Shifted_base,
    nonneg_coeffs := a358623Shifted_nonneg,
    degree_two := a358623Shifted_degree_two_succ,
    lag_coeff_pos := rr_wagner_pos_seq,
    derivative_coeff_pos := rr_wagner_pos_seq,
    recurrence := a358623Shifted_succ_succ

/-- Active-range sequence shell with a positive scalar on the left side. -/
example {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_wagner_derivative_gap_lag_sequence_den using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec

/-- Real-rootedness endpoint for the scalar-left active-range shell. -/
example {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec

/-!
### `X^2 * P'` cross-row derivative-lag obstruction

The naive degree-matched cross-row lag `X^2 * P'_{n-1}` cannot be placed in
proper position with the current row `P_n` in either orientation once the
current row has a nonzero constant term.  These examples exercise both
obstruction theorems. -/

/-- Orientation `X^2 * f' ≪ g` is impossible when `g(0) ≠ 0`. -/
example {f g : ℝ[X]}
    (hgnn : HasNonnegCoeffs g)
    (hgc0 : g.coeff 0 ≠ 0) :
    ¬ Prec (X ^ 2 * f.derivative) g :=
  not_prec_X_sq_mul_derivative_left hgnn hgc0

/-- Orientation `g ≪ X^2 * f'` is impossible in the degree-matched candidate
setting when `g(0) ≠ 0`. -/
example {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hf2 : 2 ≤ f.natDegree)
    (hgc0 : g.coeff 0 ≠ 0) :
    ¬ Prec g (X ^ 2 * f.derivative) :=
  not_prec_X_sq_mul_derivative_right hfnn hgnn hdeg hf2 hgc0

end Tactic
end RealRooted
