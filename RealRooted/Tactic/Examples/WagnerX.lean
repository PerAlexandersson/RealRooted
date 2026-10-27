module

public import RealRooted.Tactic.WagnerX
public import RealRooted.Tactic.RowInterlacing

/-!
# Wagner `X`-shift tactic examples

Smoke tests for the same-degree plateau bridge used by positive `t`-lag
recurrences.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    StrictInterl g (X * f) := by
  rr_strict_interl_mul_X using
    proper := hfg,
    left_nonneg := hfnn,
    right_nonneg := hgnn

example {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    StrictInterl g (X * f) := by
  rr_strict_interl_mul_X

example {f g : ℝ[X]} (hfg : StrictInterl f g) :
    StrictInterl (X * f) (X * g) := by
  rr_strict_interl_mul_X_both using proper := hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) :
    StrictInterl (X * f) (X * g) := by
  rr_strict_interl_mul_X_both

namespace WagnerXInferenceSmoke

@[rr_base_strict_interl] theorem one_strictInterl_one : StrictInterl (1 : ℝ[X]) 1 :=
  StrictInterl.refl (by simp) (by simp)

@[rr_nonneg] theorem one_nonneg : HasNonnegCoeffs (1 : ℝ[X]) :=
  hasNonnegCoeffs_one

@[rr_nonneg] theorem zero_nonneg : HasNonnegCoeffs (0 : ℝ[X]) :=
  hasNonnegCoeffs_zero

example : StrictInterl (1 : ℝ[X]) (X * 1) := by rr_strict_interl_mul_X

end WagnerXInferenceSmoke

/-- `A358623`, active offset: the recurrence
`P_{n+5}=t(P'_{n+4}+(n+4)P_{n+3})` preserves the shifted adjacent
`StrictInterl` invariant from the base pair `P_3 ≪ P_4`. -/
theorem a358623_activeOffset_strictInterl {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 3) (P 4))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 4)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 5) =
        X * (C (1 : ℝ) * (P (n + 4)).derivative + C ((n : ℝ) + 4) * P (n + 3))) :
    ∀ n : Nat, StrictInterl (P (n + 3)) (P (n + 4)) := by
  let Q : Nat → ℝ[X] := fun n => P (n + 3)
  have hQbase : StrictInterl (Q 0) (Q 1) := by simpa [Q] using hbase
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
  have hQstrictInterl : ∀ n : Nat, StrictInterl (Q n) (Q (n + 1)) := by
    exact RealRooted.strictInterl_wagner_derivative_gap_lag_sequence
      hQbase hQnonneg hQdeg (fun _ => by positivity) (fun _ => by positivity) hQrec
  intro n
  simpa [Q] using hQstrictInterl n

/-- `A358623`, active offset: real-rootedness of all shifted active rows
`P_{n+3}` from the same base and recurrence certificates. -/
theorem a358623_activeOffset_realRooted {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 3) (P 4))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 4)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 5) =
        X * (C (1 : ℝ) * (P (n + 4)).derivative + C ((n : ℝ) + 4) * P (n + 3))) :
    ∀ n : Nat, P (n + 3) ≠ 0 ∧ (P (n + 3)).Splits := by
  let Q : Nat → ℝ[X] := fun n => P (n + 3)
  have hQbase : StrictInterl (Q 0) (Q 1) := by simpa [Q] using hbase
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
    exact RealRooted.isRealRooted_of_strictInterl_wagner_derivative_gap_lag_sequence
      hQbase hQnonneg hQdeg (fun _ => by positivity) (fun _ => by positivity) hQrec
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
lemma a358623Shifted_base : StrictInterl (a358623Shifted 0) (a358623Shifted 1) := by
  have hlin : Interlaces (1 : ℝ[X]) (1 + C (3 : ℝ) * X) :=
    interlaces_one_linear (by simp)
  have hstrictInterl : StrictInterl (1 : ℝ[X]) (1 + C (3 : ℝ) * X) := hlin.toStrictInterl
  have hmul : StrictInterl (X * (1 : ℝ[X])) (X * (1 + C (3 : ℝ) * X)) := by
    rr_strict_interl_mul_X_both using proper := hstrictInterl
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
      linarith [hprev, show (0 : ℝ) < (n : ℝ) + 4 by positivity]

/-- Active shifted rows have degree at least two, as required by Rolle. -/
lemma a358623Shifted_degree_two_succ (n : Nat) :
    2 ≤ (a358623Shifted (n + 1)).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (ne_of_gt (a358623Shifted_coeff_two_pos_succ n))

/-- Adjacent `StrictInterl` invariant for the shifted recurrence-defined `A358623`
active family. -/
theorem a358623Shifted_strictInterl :
    ∀ n : Nat, StrictInterl (a358623Shifted n) (a358623Shifted (n + 1)) := by
  intro n
  rr_row_strictInterl

/-- Real-rootedness of the shifted recurrence-defined `A358623` active family. -/
theorem a358623Shifted_realRooted :
    ∀ n : Nat, a358623Shifted n ≠ 0 ∧ (a358623Shifted n).Splits := by
  intro n
  exact ⟨by rr_row_ne_zero, by rr_row_splits⟩

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
    ¬ StrictInterl (X ^ 2 * f.derivative) g :=
  not_strictInterl_X_sq_mul_derivative_left hgnn hgc0

/-- Orientation `g ≪ X^2 * f'` is impossible in the degree-matched candidate
setting when `g(0) ≠ 0`. -/
example {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hf2 : 2 ≤ f.natDegree)
    (hgc0 : g.coeff 0 ≠ 0) :
    ¬ StrictInterl g (X ^ 2 * f.derivative) :=
  not_strictInterl_X_sq_mul_derivative_right hfnn hgnn hdeg hf2 hgc0

end Tactic
end RealRooted

/- Deprecated theorem aliases retained for the #984 Prec migration. -/
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted

