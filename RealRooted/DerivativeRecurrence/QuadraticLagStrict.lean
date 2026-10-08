import RealRooted.Derivative.Interlacing
import RealRooted.GeneralizedLiuWang
import RealRooted.SimpleRoots
import RealRooted.WagnerRightSum

/-!
# Strict interlacing for quadratic derivative recurrences with a lag

This module isolates the root-sign argument for second-order recurrences whose
derivative multiplier is `a X - b X^2` and whose lag multiplier is `c X`.
The middle multiplier is arbitrary because it vanishes at every root used by
the generalized Liu--Wang step.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A quadratic derivative recurrence with an arbitrary middle multiplier has
strict adjacent interlacing once its elementary rankwise invariants and
base pair are known. -/
theorem strictInterl_and_noCommonRoot_of_quadratic_lag
    (P : ℕ → ℝ[X]) (a b c : ℝ) (Q : ℕ → ℝ[X])
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hdeg : ∀ n, (P n).natDegree = n)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hroot : ∀ n r, (P n).IsRoot r → r < 0)
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        Q n * P (n + 1) + (C c * X) * P n) :
    ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  intro n
  induction n with
  | zero => exact ⟨hbase, hbaseNo⟩
  | succ n ih =>
      obtain ⟨ihstrictInterl, ihno⟩ := ih
      have hinter : Interlaces (P n) (P (n + 1)) :=
        ihstrictInterl.toInterlaces (by rw [hdeg, hdeg])
      have hderiv_inter : Interlaces ((P (n + 1)).derivative) (P (n + 1)) :=
        interlaces_derivative_of_pos_natDegree (hpos (n + 1)).ne_zero
          ihstrictInterl.2.1.2 (hpos (n + 1)) (by rw [hdeg]; lia)
      have hderiv_pos : HasPosLeadingCoeff ((P (n + 1)).derivative) :=
        (hpos (n + 1)).derivative (by rw [hdeg]; lia)
      have hV : ∀ r : ℝ, (P (n + 1)).IsRoot r →
          eval r (C a * X + C (-b) * X ^ 2) ≤ 0 := by
        intro r hr
        have hrneg := hroot (n + 1) r hr
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
        nlinarith [sq_nonneg r]
      have hW : ∀ r : ℝ, (P (n + 1)).IsRoot r → eval r (C c * X) ≤ 0 := by
        intro r hr
        simp only [eval_mul, eval_C, eval_X]
        exact mul_nonpos_of_nonneg_of_nonpos hc (hroot (n + 1) r hr).le
      have hsum : P (n + 2) =
          Q n * P (n + 1) +
            polynomialWeightedSum
              ((C c * X, P n) ::
                [(C a * X + C (-b) * X ^ 2, (P (n + 1)).derivative)]) := by
        rw [hrec n]
        simp only [polynomialWeightedSum]
        ring
      have hstrictInterl : StrictInterl (P (n + 1)) (P (n + 2)) := by
        rw [hsum]
        refine strictInterl_generalizedLiuWang_of_no_common
          hinter (hpos n) ?_ ?_ ?_ ?_ ?_ ?_ ihno hW
        · intro bg hmem
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hderiv_inter
        · intro bg hmem
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hderiv_pos
        · intro bg hmem r hr
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hV r hr
        · rw [← hsum]
          exact hpos (n + 2)
        · rw [← hsum, hdeg, hdeg]
          lia
        · rw [← hsum, hdeg, hdeg]
      refine ⟨hstrictInterl, ?_⟩
      intro r hr2 hr1
      have hrneg : r < 0 := hroot (n + 1) r hr1
      have hkey :
          (a - b * r) * eval r ((P (n + 1)).derivative) +
            c * eval r (P n) = 0 := by
        have h := hr2
        rw [Polynomial.IsRoot.def, hrec n] at h
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at h
        rw [Polynomial.IsRoot.def] at hr1
        rw [hr1] at h
        have hr0 : r ≠ 0 := ne_of_lt hrneg
        have hfactor :
            r * ((a - b * r) * eval r ((P (n + 1)).derivative) +
              c * eval r (P n)) = 0 := by
          linarith [h]
        exact (mul_eq_zero.mp hfactor).resolve_left hr0
      have hne : eval r (P n) ≠ 0 := fun hroot0 => ihno r hr1 hroot0
      have hsign : 0 ≤ eval r (P n) * eval r ((P (n + 1)).derivative) :=
        eval_mul_eval_nonneg_of_strictInterl_right ihstrictInterl hderiv_inter.toStrictInterl
          (hpos n) hderiv_pos hr1
      have hpref : 0 < a - b * r := by nlinarith
      have hmul :
          0 ≤ (a - b * r) *
            (eval r (P n) * eval r ((P (n + 1)).derivative)) :=
        mul_nonneg hpref.le hsign
      have hlag_square : 0 ≤ c * (eval r (P n)) ^ 2 :=
        mul_nonneg hc (sq_nonneg _)
      have hsum_zero :
          (a - b * r) *
              (eval r (P n) * eval r ((P (n + 1)).derivative)) +
            c * (eval r (P n)) ^ 2 = 0 := by
        calc
          _ = eval r (P n) *
              ((a - b * r) * eval r ((P (n + 1)).derivative) +
                c * eval r (P n)) := by ring
          _ = 0 := by rw [hkey, mul_zero]
      have hfirst_zero :
          (a - b * r) *
            (eval r (P n) * eval r ((P (n + 1)).derivative)) = 0 := by
        linarith
      have hproduct_zero :
          eval r (P n) * eval r ((P (n + 1)).derivative) = 0 :=
        (mul_eq_zero.mp hfirst_zero).resolve_left hpref.ne'
      have hderiv_zero : eval r ((P (n + 1)).derivative) = 0 :=
        (mul_eq_zero.mp hproduct_zero).resolve_left hne
      have hsimple : HasSimpleRoots (P (n + 1)) :=
        (ihstrictInterl.hasSimpleRoots_of_no_common_root fun x hx =>
          ihno x hx.2 hx.1).2
      exact (hsimple.eval_derivative_ne_zero hr1 hderiv_zero).elim

/-- A quadratic derivative recurrence whose degree stays fixed or rises by
one has strict adjacent interlacing.  This version uses the derivative as
the strict Liu--Wang interlacer, so the lag polynomial may have the same degree
as the current row. -/
theorem strictInterl_and_noCommonRoot_of_quadratic_lag_degree_step
    (P : ℕ → ℝ[X]) (a b c : ℝ) (Q : ℕ → ℝ[X])
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hdegreePos : ∀ n, 0 < (P (n + 1)).natDegree)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hroot : ∀ n r, (P n).IsRoot r → r < 0)
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        Q n * P (n + 1) + (C c * X) * P n) :
    ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  intro n
  induction n with
  | zero => exact ⟨hbase, hbaseNo⟩
  | succ n ih =>
      obtain ⟨ihstrictInterl, ihno⟩ := ih
      have hsimple : HasSimpleRoots (P (n + 1)) :=
        (ihstrictInterl.hasSimpleRoots_of_no_common_root fun x hx =>
          ihno x hx.2 hx.1).2
      have hderiv_inter : Interlaces ((P (n + 1)).derivative) (P (n + 1)) :=
        interlaces_derivative_of_pos_natDegree (hpos (n + 1)).ne_zero
          ihstrictInterl.2.1.2 (hpos (n + 1)) (hdegreePos n)
      have hderiv_pos : HasPosLeadingCoeff ((P (n + 1)).derivative) :=
        (hpos (n + 1)).derivative (by exact (hdegreePos n).ne')
      have hrootSign : ∀ r, (P (n + 1)).IsRoot r →
          eval r (P (n + 2)) * eval r ((P (n + 1)).derivative) < 0 := by
        intro r hr
        have hrneg := hroot (n + 1) r hr
        have hprevDeriv :
            0 ≤ eval r (P n) * eval r ((P (n + 1)).derivative) :=
          eval_mul_eval_nonneg_of_strictInterl_right ihstrictInterl hderiv_inter.toStrictInterl
            (hpos n) hderiv_pos hr
        have hderivNe : eval r ((P (n + 1)).derivative) ≠ 0 :=
          hsimple.eval_derivative_ne_zero hr
        have hpref : 0 < a - b * r := by nlinarith
        have hpositive :
            0 < (a - b * r) * eval r ((P (n + 1)).derivative) ^ 2 +
              c * (eval r (P n) * eval r ((P (n + 1)).derivative)) := by
          have hsquare : 0 < eval r ((P (n + 1)).derivative) ^ 2 := sq_pos_of_ne_zero hderivNe
          positivity
        have heval :
            eval r (P (n + 2)) =
              r * ((a - b * r) * eval r ((P (n + 1)).derivative) +
                c * eval r (P n)) := by
          rw [hrec n]
          rw [Polynomial.IsRoot.def] at hr
          simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
          rw [hr]
          ring
        rw [heval]
        nlinarith
      have hstrictInterl : StrictInterl (P (n + 1)) (P (n + 2)) := by
        rcases hstep (n + 1) with hsame | hsucc
        · exact strictInterl_of_interlaces_eval_mul_neg_same
            hderiv_inter hderiv_pos (hpos (n + 2)) hsame hrootSign
        · exact strictInterl_of_interlaces_eval_mul_neg_succ
            hderiv_inter hderiv_pos (hpos (n + 2)) hsucc hrootSign
      refine ⟨hstrictInterl, ?_⟩
      intro r hr2 hr1
      have hsign := hrootSign r hr1
      rw [Polynomial.IsRoot.def] at hr2
      rw [hr2, zero_mul] at hsign
      exact (lt_irrefl 0 hsign).elim

end RealRooted

/-!
## Strict interlacing for derivative-lag recurrences with negative roots

For `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with rows of nonnegative
coefficients and positive value at `0`, the roots are negative, and `V n < 0`, `W n ≤ 0` on
`(-∞, 0)` give the strict adjacent interlacing `P n ≪ P (n + 1)` by the Liu--Wang step with
the derivative of the current row as the strict interlacer.  The degrees may stay or rise by
one, so that half growth `D₀ + (n + e) / 2` is covered; for growth one the rows interlace in
the sense of `Interlaces`.

## Main results

* `derivLag_strictInterl_and_noCommonRoot`: the induction.
* `derivLag_strictInterl_of_nonnegCoeffs`, `derivLag_strictInterl_of_nonnegCoeffs_half`:
  the versions for rows of degree `D₀ + n` and `D₀ + (n + e) / 2`.
* `derivLag_eval_zero_pos`: positivity of the rows at `0`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Strict adjacent interlacing for the derivative-lag rows
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with negative roots: `V n` is
negative and `W n` nonpositive on `(-∞, 0)`, the degrees stay or rise by one and the leading
coefficients are positive.  The rows `P (n + 1)` must have positive degree.  Unlike
`LiuWang.strictInterl_derivative_lag_sequence_of_root_signs`, the lag row may have the same
degree as the current row, and the no-common-root condition is proved alongside.  The step
uses the derivative of the current row as the strict interlacer (compare
`strictInterl_and_noCommonRoot_of_quadratic_lag_degree_step`, the case `V n = a X - b X ^ 2`,
`W n = c X`). -/
theorem derivLag_strictInterl_and_noCommonRoot
    {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hdegPos : ∀ n, 0 < (P (n + 1)).natDegree)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hroot : ∀ n r, (P n).IsRoot r → r < 0)
    (hV : ∀ n x, x < 0 → (V n).eval x < 0) (hW : ∀ n x, x < 0 → (W n).eval x ≤ 0)
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) :
    ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  intro n
  induction n with
  | zero => exact ⟨hbase, hbaseNo⟩
  | succ n ih =>
      obtain ⟨ihstrictInterl, ihno⟩ := ih
      have hsimple : HasSimpleRoots (P (n + 1)) :=
        (ihstrictInterl.hasSimpleRoots_of_no_common_root fun x hx =>
          ihno x hx.2 hx.1).2
      have hderiv_inter : Interlaces ((P (n + 1)).derivative) (P (n + 1)) :=
        interlaces_derivative_of_pos_natDegree (hpos (n + 1)).ne_zero
          ihstrictInterl.2.1.2 (hpos (n + 1)) (hdegPos n)
      have hderiv_pos : HasPosLeadingCoeff ((P (n + 1)).derivative) :=
        (hpos (n + 1)).derivative (hdegPos n).ne'
      have hrootSign : ∀ r, (P (n + 1)).IsRoot r →
          eval r (P (n + 2)) * eval r ((P (n + 1)).derivative) < 0 := by
        intro r hr
        have hrneg := hroot (n + 1) r hr
        have hprevDeriv : 0 ≤ eval r (P n) * eval r ((P (n + 1)).derivative) :=
          eval_mul_eval_nonneg_of_strictInterl_right ihstrictInterl hderiv_inter.toStrictInterl
            (hpos n) hderiv_pos hr
        have hsquare : 0 < eval r ((P (n + 1)).derivative) ^ 2 :=
          sq_pos_of_ne_zero (hsimple.eval_derivative_ne_zero hr)
        have heval : eval r (P (n + 2)) * eval r ((P (n + 1)).derivative) =
            (V n).eval r * eval r ((P (n + 1)).derivative) ^ 2 +
              (W n).eval r * (eval r (P n) * eval r ((P (n + 1)).derivative)) := by
          rw [hrec n]
          rw [Polynomial.IsRoot.def] at hr
          simp only [eval_add, eval_mul, hr]
          ring
        rw [heval]
        have h1 := mul_neg_of_neg_of_pos (hV n r hrneg) hsquare
        have h2 := mul_nonpos_of_nonpos_of_nonneg (hW n r hrneg) hprevDeriv
        linarith
      have hstrictInterl : StrictInterl (P (n + 1)) (P (n + 2)) := by
        rcases hstep (n + 1) with hsame | hsucc
        · exact strictInterl_of_interlaces_eval_mul_neg_same
            hderiv_inter hderiv_pos (hpos (n + 2)) hsame hrootSign
        · exact strictInterl_of_interlaces_eval_mul_neg_succ
            hderiv_inter hderiv_pos (hpos (n + 2)) hsucc hrootSign
      refine ⟨hstrictInterl, fun r hr2 hr1 => ?_⟩
      have hsign := hrootSign r hr1
      rw [(Polynomial.IsRoot.def.mp hr2), zero_mul] at hsign
      exact (lt_irrefl 0 hsign).elim

/-- Nonnegative coefficients and a positive value at `0` put every root of a row to the left
of `0`. -/
theorem derivLag_roots_neg {P : ℕ → ℝ[X]} (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (he0 : ∀ n, 0 < (P n).eval 0) :
    ∀ n r, (P n).IsRoot r → r < 0 := by
  intro n r hr
  have hne : P n ≠ 0 := leadingCoeff_ne_zero.mp (hpos n).ne'
  have hle : r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs (hnn n) r ((mem_roots hne).mpr hr)
  refine lt_of_le_of_ne hle fun h0 => ?_
  subst h0
  have := he0 n
  rw [Polynomial.IsRoot.def.mp hr] at this
  exact lt_irrefl _ this

/-- Strict adjacent interlacing of derivative-lag rows with nonnegative coefficients and a
positive value at `0`, for degrees that stay or rise by one. -/
theorem derivLag_strictInterl_of_nonnegCoeffs_of_step
    {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hdegPos : ∀ n, 0 < (P (n + 1)).natDegree) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (he0 : ∀ n, 0 < (P n).eval 0)
    (hV : ∀ n x, x < 0 → (V n).eval x < 0) (hW : ∀ n x, x < 0 → (W n).eval x ≤ 0)
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) :=
  (derivLag_strictInterl_and_noCommonRoot hrec hstep hdegPos hpos
    (derivLag_roots_neg hpos hnn he0) hV hW hbase hbaseNo n).1

/-- `derivLag_strictInterl_of_nonnegCoeffs_of_step` for rows of degree `D₀ + n`. -/
theorem derivLag_strictInterl_of_nonnegCoeffs {D₀ : ℕ}
    {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (he0 : ∀ n, 0 < (P n).eval 0)
    (hV : ∀ n x, x < 0 → (V n).eval x < 0) (hW : ∀ n x, x < 0 → (W n).eval x ≤ 0)
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) :=
  derivLag_strictInterl_of_nonnegCoeffs_of_step hrec
    (fun n => Or.inr (by rw [hdeg, hdeg]; lia)) (fun n => by rw [hdeg]; lia) hpos hnn he0
    hV hW hbase hbaseNo n

/-- `derivLag_strictInterl_of_nonnegCoeffs_of_step` for rows of degree `D₀ + (n + e) / 2`. -/
theorem derivLag_strictInterl_of_nonnegCoeffs_half {D₀ e : ℕ}
    {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + (n + e) / 2) (hD : 0 < D₀ + (1 + e) / 2)
    (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (he0 : ∀ n, 0 < (P n).eval 0)
    (hV : ∀ n x, x < 0 → (V n).eval x < 0) (hW : ∀ n x, x < 0 → (W n).eval x ≤ 0)
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) :=
  derivLag_strictInterl_of_nonnegCoeffs_of_step hrec
    (fun n => by rw [hdeg, hdeg]; lia) (fun n => by rw [hdeg]; lia) hpos hnn he0
    hV hW hbase hbaseNo n

/-- Rows of a derivative-lag recurrence have a positive value at `0` when the multipliers
`U n`, `V n`, `W n` are nonnegative at `0`, `U n` or `W n` is positive there, the rows have
nonnegative coefficients and the first two rows are positive at `0`. -/
theorem derivLag_eval_zero_pos {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (hU : ∀ n, 0 ≤ (U n).eval 0)
    (hV : ∀ n, 0 ≤ (V n).eval 0) (hW : ∀ n, 0 ≤ (W n).eval 0)
    (hUW : ∀ n, 0 < (U n).eval 0 + (W n).eval 0)
    (h0 : 0 < (P 0).eval 0) (h1 : 0 < (P 1).eval 0) : ∀ n, 0 < (P n).eval 0 := by
  have key : ∀ n, 0 < (P n).eval 0 ∧ 0 < (P (n + 1)).eval 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      obtain ⟨ha, hb⟩ := ih
      refine ⟨hb, ?_⟩
      have hd : 0 ≤ (P (n + 1)).derivative.eval 0 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        exact HasNonnegCoeffs.derivative (hnn (n + 1)) 0
      have hev : (P (n + 2)).eval 0 = (U n).eval 0 * (P (n + 1)).eval 0 +
          (V n).eval 0 * (P (n + 1)).derivative.eval 0 + (W n).eval 0 * (P n).eval 0 := by
        rw [hrec n]
        simp only [eval_add, eval_mul]
      rw [hev]
      have hUW' := hUW n
      have h2 := mul_nonneg (hV n) hd
      rcases (hU n).lt_or_eq with hu | hu
      · nlinarith [mul_pos hu hb, mul_nonneg (hW n) ha.le]
      · rw [← hu] at hUW'
        nlinarith [mul_pos hUW' ha, mul_nonneg (hU n) hb.le]
  exact fun n => (key n).1

end RealRooted
