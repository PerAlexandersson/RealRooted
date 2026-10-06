import RealRooted.LiuWangRecursion

/-!
# No common roots of consecutive recurrence rows

Positive-lag Liu–Wang sequence theorems such as
`RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_signs` take the
hypothesis

`hno : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`.

This file proves it for the two common recurrence shapes.

* Three-term rows `P (n + 2) = a n * P (n + 1) + b n * P n`: a common root of
  `P (n + 1)` and `P (n + 2)` is a root of `b n * P n`.  If `b n` does not vanish
  there, it is a root of `P n` as well, and the argument descends to rows `0`
  and `1` (`threeTerm_not_isRoot_of_isRoot_succ`).  The usual situation is that
  `b n` vanishes only at `0` while no row vanishes at `0`
  (`threeTerm_not_isRoot_of_isRoot_succ_of_eval_zero_ne`).
* Derivative-lag rows `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n`:
  at a common root `r` of `P (n + 1)` and `P (n + 2)`,
  `V n (r) (P (n + 1))'(r) + W n (r) P n (r) = 0`.  Since `P n` and
  `(P (n + 1))'` both interlace `P (n + 1)`, they have the same sign at `r`, so
  `V n ≤ 0` and `W n < 0` at `r` make the left side nonzero.  The interlacing is
  proved in the same induction (`derivLag_not_isRoot_of_isRoot_succ`).
-/

open Polynomial

namespace RealRooted

variable {P : ℕ → ℝ[X]}

section ThreeTerm

variable {a b : ℕ → ℝ[X]}

/-- Consecutive rows of `P (n + 2) = a n * P (n + 1) + b n * P n` have no common
root when rows `0` and `1` have none and `b n` does not vanish at the roots of
`P (n + 1)`. -/
theorem threeTerm_not_isRoot_of_isRoot_succ
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hb : ∀ n r, (P (n + 1)).IsRoot r → (b n).eval r ≠ 0)
    (h01 : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) :
    ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r
  | 0 => h01
  | n + 1 => fun r h2 h1 => by
      have hev : (P (n + 2)).eval r =
          (a n).eval r * (P (n + 1)).eval r + (b n).eval r * (P n).eval r := by
        rw [hrec n, eval_add, eval_mul, eval_mul]
      rw [h2.eq_zero, h1.eq_zero, mul_zero, zero_add, eq_comm, mul_eq_zero] at hev
      exact threeTerm_not_isRoot_of_isRoot_succ hrec hb h01 n r h1
        (hev.resolve_left (hb n r h1))

/-- The common special case of `threeTerm_not_isRoot_of_isRoot_succ`: `b n`
vanishes at most at `0`, and no row vanishes at `0`. -/
theorem threeTerm_not_isRoot_of_isRoot_succ_of_eval_zero_ne
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hb : ∀ n r, (b n).eval r = 0 → r = 0) (hP : ∀ n, (P n).eval 0 ≠ 0)
    (h01 : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) :
    ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r :=
  threeTerm_not_isRoot_of_isRoot_succ hrec
    (fun n r hr hbr => hP (n + 1) (hb n r hbr ▸ hr.eq_zero)) h01

end ThreeTerm

section DerivativeLag

variable {U V W : ℕ → ℝ[X]}

/-- Consecutive rows of the derivative-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` have no common root.

The hypotheses are those of
`RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_signs`, in the
same order, with two changes: `W n` is strictly negative at the roots of
`P (n + 1)`, and the no-common-root hypothesis is only required for rows `0` and
`1`.  The interlacing `P n ≪ P (n + 1)` is proved alongside, by the same
induction. -/
theorem derivLag_not_isRoot_of_isRoot_succ
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos : ∀ n, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
      ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_neg : ∀ n, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
      ∀ r, (P (n + 1)).IsRoot r → (W n).eval r < 0)
    (hdeg_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (h01 : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) :
    ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  have key : ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
    intro n
    induction n with
    | zero => exact ⟨hbase, h01⟩
    | succ n ih =>
        obtain ⟨hint, hno⟩ := ih
        have hsrc : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := hint.2.1
        have hder : Interlaces (P (n + 1)).derivative (P (n + 1)) :=
          derivative_interlaces hsrc.2 (hdeg_two n)
        have hder_pos : HasPosLeadingCoeff (P (n + 1)).derivative :=
          (hpos (n + 1)).derivative (by linarith [hdeg_two n])
        have hdeg_next := hdeg_succ (n + 1)
        rw [hrec n] at hdeg_next
        have hstep := LiuWang.strictInterl_derivative_lag_of_nonpos hsrc.2 (hdeg_two n)
          (hint.toInterlaces (hdeg_succ n)) (hpos n) (hpos (n + 1))
          (by rw [← hrec n]; exact hpos (n + 2)) (by lia) (by lia) hno
          (hV_nonpos n hsrc) (fun r hr => (hW_neg n hsrc r hr).le)
        rw [← hrec n] at hstep
        refine ⟨hstep, fun r h2 h1 => hno r h1 ?_⟩
        by_contra hne
        have hev : (P (n + 2)).eval r = (U n).eval r * (P (n + 1)).eval r +
            (V n).eval r * (P (n + 1)).derivative.eval r + (W n).eval r * (P n).eval r := by
          rw [hrec n, eval_add, eval_add, eval_mul, eval_mul, eval_mul]
        rw [h2.eq_zero, h1.eq_zero, mul_zero, zero_add] at hev
        have hsign : 0 ≤ (P n).eval r * (P (n + 1)).derivative.eval r :=
          eval_mul_eval_nonneg_of_strictInterl_right hint hder.toStrictInterl (hpos n)
            hder_pos h1
        have hsq : 0 < (P n).eval r ^ 2 := sq_pos_of_ne_zero hne
        have hV := mul_nonpos_of_nonpos_of_nonneg (hV_nonpos n hsrc r h1) hsign
        have hW := mul_neg_of_neg_of_pos (hW_neg n hsrc r h1) hsq
        have hzero : (P n).eval r * ((V n).eval r * (P (n + 1)).derivative.eval r +
            (W n).eval r * (P n).eval r) = 0 := by rw [← hev, mul_zero]
        linarith
  exact fun n => (key n).2

end DerivativeLag

section Examples

/-- Delannoy-type rows `P (n + 2) = (1 + X) P (n + 1) + X P n` (OEIS A008288),
which never vanish at `0`. -/
example (P : ℕ → ℝ[X]) (hrec : ∀ n, P (n + 2) = (1 + X) * P (n + 1) + X * P n)
    (hP : ∀ n, (P n).eval 0 ≠ 0) (hP0 : P 0 = 1) :
    ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r :=
  threeTerm_not_isRoot_of_isRoot_succ_of_eval_zero_ne (a := fun _ => 1 + X)
    (b := fun _ => X) hrec (fun _ r h => by simpa using h) hP
    (fun r _ h0 => by simp [hP0] at h0)

end Examples

end RealRooted
