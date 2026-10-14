import RealRooted.DerivativeRecurrence.MultiLagCancel
import RealRooted.Recurrence.Uniqueness

/-!
# Periodic top-coefficient rows

This file applies the multi-lag top-window degree law to the remaining OEIS recurrences
from issue 1343.  The definitions are normalized copies of the downstream recurrences.
-/

open Polynomial

namespace RealRooted.Tactic.RowParityDegree

noncomputable section

/-- The downstream A177040 recurrence. -/
def A177040 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 2 + X
  | 3 => 3 + X
  | n + 4 =>
      let r : ℝ := n
      (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * (A177040 (n + 3)).derivative
        + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * (A177040 (n + 2)).derivative
        + (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * (A177040 (n + 1)).derivative
        + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * (A177040 n).derivative
        + (C (2 / 5 - 1 / 5 * r) + C (3 / 5 + 1 / 5 * r) * X) * A177040 (n + 3)
        + (C (2 + 2 / 5 * r) + C (-2 / 5 * r) * X) * A177040 (n + 2)
        + (C (2 / 5 + 1 / 5 * r) + C (-7 / 5 - 1 / 5 * r) * X) * A177040 (n + 1)
        + (C (-13 / 5 - 2 / 5 * r) + C (8 / 5 + 2 / 5 * r) * X) * A177040 n

private def d3 (_ : ℕ) : ℝ[X] := C (2 / 5) * X + C (-2 / 5) * X ^ 2

private def d2 (_ : ℕ) : ℝ[X] := C (-4 / 5) * X + C (4 / 5) * X ^ 2

private def d1 (_ : ℕ) : ℝ[X] := C (2 / 5) * X + C (-2 / 5) * X ^ 2

private def d0 (_ : ℕ) : ℝ[X] := C (-4 / 5) * X + C (4 / 5) * X ^ 2

private def a3 (n : ℕ) : ℝ[X] :=
  C (2 / 5 - 1 / 5 * (n : ℝ)) + C (3 / 5 + 1 / 5 * (n : ℝ)) * X

private def a2 (n : ℕ) : ℝ[X] :=
  C (2 + 2 / 5 * (n : ℝ)) + C (-2 / 5 * (n : ℝ)) * X

private def a1 (n : ℕ) : ℝ[X] :=
  C (2 / 5 + 1 / 5 * (n : ℝ)) + C (-7 / 5 - 1 / 5 * (n : ℝ)) * X

private def a0 (n : ℕ) : ℝ[X] :=
  C (-13 / 5 - 2 / 5 * (n : ℝ)) + C (8 / 5 + 2 / 5 * (n : ℝ)) * X

private def terms177 : List (ℕ × ℕ × (ℕ → ℝ[X])) :=
  [(3, 1, d3), (2, 1, d2), (1, 1, d1), (0, 1, d0),
    (3, 0, a3), (2, 0, a2), (1, 0, a1), (0, 0, a0)]

private lemma A177040_rhs (n : ℕ) :
    A177040 (n + 4) = RealRooted.LinRec.rhs terms177 A177040 n := by
  simp only [terms177, RealRooted.LinRec.rhs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Function.iterate_one, Function.iterate_zero,
    id_eq, add_zero]
  rw [A177040]
  simp only [d3, d2, d1, d0, a3, a2, a1, a0]
  ring

private lemma natDegree_quadratic_le (a b : ℝ) :
    (C a * X + C b * X ^ 2).natDegree ≤ 2 := by
  compute_degree!

private lemma natDegree_linear_le (a b : ℝ) :
    (C a + C b * X).natDegree ≤ 1 := by
  compute_degree!

private lemma A177040_coeff_succ (n k : ℕ) :
    (A177040 (n + 4)).coeff (k + 2) =
      ((2 / 5) * ((k : ℝ) + 2) * (A177040 (n + 3)).coeff (k + 2)
        + (-2 / 5) * ((k : ℝ) + 1) * (A177040 (n + 3)).coeff (k + 1))
      + ((-4 / 5) * ((k : ℝ) + 2) * (A177040 (n + 2)).coeff (k + 2)
        + (4 / 5) * ((k : ℝ) + 1) * (A177040 (n + 2)).coeff (k + 1))
      + ((2 / 5) * ((k : ℝ) + 2) * (A177040 (n + 1)).coeff (k + 2)
        + (-2 / 5) * ((k : ℝ) + 1) * (A177040 (n + 1)).coeff (k + 1))
      + ((-4 / 5) * ((k : ℝ) + 2) * (A177040 n).coeff (k + 2)
        + (4 / 5) * ((k : ℝ) + 1) * (A177040 n).coeff (k + 1))
      + ((2 / 5 - 1 / 5 * (n : ℝ)) * (A177040 (n + 3)).coeff (k + 2)
        + (3 / 5 + 1 / 5 * (n : ℝ)) * (A177040 (n + 3)).coeff (k + 1))
      + ((2 + 2 / 5 * (n : ℝ)) * (A177040 (n + 2)).coeff (k + 2)
        + (-2 / 5 * (n : ℝ)) * (A177040 (n + 2)).coeff (k + 1))
      + ((2 / 5 + 1 / 5 * (n : ℝ)) * (A177040 (n + 1)).coeff (k + 2)
        + (-7 / 5 - 1 / 5 * (n : ℝ)) * (A177040 (n + 1)).coeff (k + 1))
      + ((-13 / 5 - 2 / 5 * (n : ℝ)) * (A177040 n).coeff (k + 2)
        + (8 / 5 + 2 / 5 * (n : ℝ)) * (A177040 n).coeff (k + 1)) := by
  conv_lhs => rw [A177040]
  change
    (d3 n * (A177040 (n + 3)).derivative
          + d2 n * (A177040 (n + 2)).derivative
          + d1 n * (A177040 (n + 1)).derivative
          + d0 n * (A177040 n).derivative
          + a3 n * A177040 (n + 3) + a2 n * A177040 (n + 2)
          + a1 n * A177040 (n + 1) + a0 n * A177040 n).coeff (k + 2) = _
  rw [show
      (d3 n * (A177040 (n + 3)).derivative
          + d2 n * (A177040 (n + 2)).derivative
          + d1 n * (A177040 (n + 1)).derivative
          + d0 n * (A177040 n).derivative
          + a3 n * A177040 (n + 3) + a2 n * A177040 (n + 2)
          + a1 n * A177040 (n + 1) + a0 n * A177040 n) =
        C (2 / 5) * (X * (A177040 (n + 3)).derivative)
          + C (-2 / 5) * (X ^ 2 * (A177040 (n + 3)).derivative)
          + C (-4 / 5) * (X * (A177040 (n + 2)).derivative)
          + C (4 / 5) * (X ^ 2 * (A177040 (n + 2)).derivative)
          + C (2 / 5) * (X * (A177040 (n + 1)).derivative)
          + C (-2 / 5) * (X ^ 2 * (A177040 (n + 1)).derivative)
          + C (-4 / 5) * (X * (A177040 n).derivative)
          + C (4 / 5) * (X ^ 2 * (A177040 n).derivative)
          + C (2 / 5 - 1 / 5 * (n : ℝ)) * A177040 (n + 3)
          + C (3 / 5 + 1 / 5 * (n : ℝ)) * (X * A177040 (n + 3))
          + C (2 + 2 / 5 * (n : ℝ)) * A177040 (n + 2)
          + C (-2 / 5 * (n : ℝ)) * (X * A177040 (n + 2))
          + C (2 / 5 + 1 / 5 * (n : ℝ)) * A177040 (n + 1)
          + C (-7 / 5 - 1 / 5 * (n : ℝ)) * (X * A177040 (n + 1))
          + C (-13 / 5 - 2 / 5 * (n : ℝ)) * A177040 n
          + C (8 / 5 + 2 / 5 * (n : ℝ)) * (X * A177040 n) by
      simp only [d3, d2, d1, d0, a3, a2, a1, a0]
      ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul', coeff_derivative,
    show (2 ≤ k + 2) = True by simp, ite_true, show k + 2 - 2 = k by lia]
  grind

/-- The normalized A330798 lag-two update. -/
def A330798Next (n : ℕ) (u v : ℝ[X]) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  (C (q * (25 / 8 + 7 / 8 * r)) * X + C (9 / 8 * q * (3 + r)) * X ^ 2)
      * u.derivative.derivative
    + (C (1 / 4 * r * q) + C (-1 / 2 * q) * X) * v.derivative.derivative
    + (C (q * (21 / 2 - 1 / 8 * (3 + r) ^ 2 + 11 / 2 * r))
        + C (q * (99 / 4 - 9 / 8 * (3 + r) ^ 2 + 39 / 4 * r)) * X
        + C (q * (-75 / 4 - 99 / 4 * r)) * X ^ 2
        + C (q * (-36 - 36 * r)) * X ^ 3) * u.derivative
    + (C (q * (-1 - 2 * r)) + C (18 * q) * X + C (33 * q) * X ^ 2
        + C (q * (-9 - 27 / 2 * r)) * X ^ 3) * v.derivative
    + (C (q * (57 / 2 + 15 * r - 15 / 8 * (3 + r) ^ 2))
        + C (q * (-150 - 75 * r + 81 / 4 * (3 + r) ^ 2)) * X
        + C (q * (-288 - 144 * r + 36 * (3 + r) ^ 2)) * X ^ 2) * u
    + (C (q * (-63 + 9 * (3 + r) ^ 2 - 27 / 2 * r))
        + C (q * (-48 + 9 * (3 + r) ^ 2 + 33 / 2 * r)) * X
        + C (q * (234 - 27 * (3 + r) ^ 2 + 261 / 2 * r)) * X ^ 2) * v

/-- The downstream A330798 recurrence. -/
def A330798 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | n + 2 =>
      let r : ℝ := n
      let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
      (C (q * (25 / 8 + 7 / 8 * r)) * X + C (9 / 8 * q * (3 + r)) * X ^ 2)
          * ((A330798 (n + 1)).derivative).derivative
        + (C (1 / 4 * r * q) + C (-1 / 2 * q) * X) * ((A330798 n).derivative).derivative
        + (C (q * (21 / 2 - 1 / 8 * (3 + r) ^ 2 + 11 / 2 * r))
            + C (q * (99 / 4 - 9 / 8 * (3 + r) ^ 2 + 39 / 4 * r)) * X
            + C (q * (-75 / 4 - 99 / 4 * r)) * X ^ 2
            + C (q * (-36 - 36 * r)) * X ^ 3) * (A330798 (n + 1)).derivative
        + (C (q * (-1 - 2 * r)) + C (18 * q) * X + C (33 * q) * X ^ 2
            + C (q * (-9 - 27 / 2 * r)) * X ^ 3) * (A330798 n).derivative
        + (C (q * (57 / 2 + 15 * r - 15 / 8 * (3 + r) ^ 2))
            + C (q * (-150 - 75 * r + 81 / 4 * (3 + r) ^ 2)) * X
            + C (q * (-288 - 144 * r + 36 * (3 + r) ^ 2)) * X ^ 2)
          * A330798 (n + 1)
        + (C (q * (-63 + 9 * (3 + r) ^ 2 - 27 / 2 * r))
            + C (q * (-48 + 9 * (3 + r) ^ 2 + 33 / 2 * r)) * X
            + C (q * (234 - 27 * (3 + r) ^ 2 + 261 / 2 * r)) * X ^ 2) * A330798 n

/-- The normalized update is the defining recurrence for `A330798`. -/
theorem A330798_succ_succ (n : ℕ) :
    A330798 (n + 2) = A330798Next n (A330798 (n + 1)) (A330798 n) := by
  rw [A330798]
  rfl

/-- A sequence with the generated A330798 initial rows and normalized update is the library
model sequence. -/
theorem sequence_eq_A330798_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + 2 * X)
    (hrec : ∀ n, P (n + 2) = A330798Next n (P (n + 1)) (P n)) :
    ∀ n, P n = A330798 n :=
  sequence_eq_of_same_lag_two_recurrence A330798Next
    (hzero.trans (show (1 : ℝ[X]) = A330798 0 by rfl))
    (hone.trans (show (2 + 2 * X : ℝ[X]) = A330798 1 by rfl))
    hrec A330798_succ_succ

private def A330798d (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3)

private def A330798D (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) * (2 * (n : ℝ) + 5)

private def A330798SimpleNum (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (C (((n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (7 * (n : ℝ) + 6))
      + C (3 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 1) *
          (3 * (n : ℝ) + 2)) * X) * p
    + (C ((n : ℝ) * ((n : ℝ) + 2))
      + C (2 * ((n : ℝ) + 2) * (5 * (n : ℝ) + 3)) * X
      + C (3 * ((n : ℝ) + 2) * (3 * (n : ℝ) + 2)) * X ^ 2) * p.derivative

private def A330798ODE (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  X * (1 + X) * p.derivative.derivative
    + C ((n : ℝ) + 2) * (1 + X) * p.derivative
    - C ((n : ℝ) * (2 * (n : ℝ) + 1)) * p

private def A330798StepNum (n : ℕ) (q p : ℝ[X]) : ℝ[X] :=
  (C (7 * (n : ℝ) + 25) * X + C (9 * ((n : ℝ) + 3)) * X ^ 2) *
      q.derivative.derivative
    + (C (2 * (n : ℝ)) + C (-4) * X) * p.derivative.derivative
    + (C (-((n : ℝ) ^ 2) + 38 * (n : ℝ) + 75)
        + C (-3 * (3 * (n : ℝ) ^ 2 - 8 * (n : ℝ) - 39)) * X
        + C (-6 * (33 * (n : ℝ) + 25)) * X ^ 2
        + C (-288 * ((n : ℝ) + 1)) * X ^ 3) * q.derivative
    + (C (-8 * (2 * (n : ℝ) + 1)) + C 144 * X + C 264 * X ^ 2
        + C (-36 * (3 * (n : ℝ) + 2)) * X ^ 3) * p.derivative
    + (C (-3 * (5 * (n : ℝ) ^ 2 - 10 * (n : ℝ) - 31))
        + C (6 * (27 * (n : ℝ) ^ 2 + 62 * (n : ℝ) + 43)) * X
        + C (288 * ((n : ℝ) + 1) ^ 2) * X ^ 2) * q
    + (C (36 * ((n : ℝ) + 4) * (2 * (n : ℝ) + 1))
        + C (12 * (2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 22)) * X
        + C (-36 * (2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)) * X ^ 2) * p

private def A330798SimpleResidualA (n : ℕ) : ℝ[X] :=
  C (-4 * ((n : ℝ) + 2) ^ 2 * (2 * (n : ℝ) + 5)) *
    (C (-181 * (n : ℝ) ^ 3 - 778 * (n : ℝ) ^ 2 - 1053 * (n : ℝ) - 402)
      + C (27 * (n : ℝ) ^ 3 - 63 * (n : ℝ) ^ 2 - 432 * (n : ℝ) - 288) * X
      + C (1197 * (n : ℝ) ^ 3 + 4347 * (n : ℝ) ^ 2
          + 4590 * (n : ℝ) + 1440) * X ^ 2
      + C (1296 * (n : ℝ) ^ 3 + 4752 * (n : ℝ) ^ 2
          + 5184 * (n : ℝ) + 1728) * X ^ 3)

private def A330798SimpleResidualB (n : ℕ) : ℝ[X] :=
  C (2 * ((n : ℝ) + 2) ^ 3 * (2 * (n : ℝ) + 5)) *
    (C (n : ℝ) + C (9 * (n : ℝ) + 6) * X) *
    (C (7 * (n : ℝ) + 25) + C (9 * (n : ℝ) + 27) * X)

private lemma A330798_simple_algebra (n : ℕ) (p : ℝ[X]) :
    C (A330798d (n + 1)) *
        A330798StepNum n (A330798SimpleNum n p) (C (A330798d n) * p)
      - C (8 * A330798D n) *
          A330798SimpleNum (n + 1) (A330798SimpleNum n p)
    =
      A330798SimpleResidualA n * A330798ODE n p
        + A330798SimpleResidualB n * (A330798ODE n p).derivative := by
  dsimp [A330798d, A330798D, A330798StepNum, A330798SimpleNum,
    A330798SimpleResidualA, A330798SimpleResidualB, A330798ODE]
  push_cast
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.derivative_one,
    Polynomial.derivative_pow, zero_mul, mul_zero, zero_add, add_zero]
  norm_num [map_ofNat, map_add, map_mul, map_neg, map_sub, map_pow]
  ring

private lemma A330798_ode_algebra (n : ℕ) (p : ℝ[X]) :
    A330798ODE (n + 1) (A330798SimpleNum n p) =
      (C (2 * ((n : ℝ) + 2) *
          (7 * (n : ℝ) ^ 2 + 19 * (n : ℝ) + 9))
        + C (2 * ((n : ℝ) + 2) *
            (9 * (n : ℝ) ^ 2 + 24 * (n : ℝ) + 12)) * X) * A330798ODE n p
      + (C ((n : ℝ) + 2) * (1 + X) *
          (C (n : ℝ) + C (9 * (n : ℝ) + 6) * X)) *
            (A330798ODE n p).derivative := by
  dsimp [A330798ODE, A330798SimpleNum]
  push_cast
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.derivative_one,
    Polynomial.derivative_pow, zero_mul, mul_zero, zero_add, add_zero]
  norm_num [map_ofNat, map_add, map_mul, map_neg, map_sub, map_pow]
  ring

private lemma A330798_simpleNum_C_mul (n : ℕ) (c : ℝ) (p : ℝ[X]) :
    A330798SimpleNum n (C c * p) = C c * A330798SimpleNum n p := by
  dsimp [A330798SimpleNum]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  ring

private lemma A330798_stepNum_C_mul (n : ℕ) (c : ℝ) (q p : ℝ[X]) :
    A330798StepNum n (C c * q) (C c * p) =
      C c * A330798StepNum n q p := by
  dsimp [A330798StepNum]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  ring

private lemma A330798_ode_C_mul (n : ℕ) (c : ℝ) (p : ℝ[X]) :
    A330798ODE n (C c * p) = C c * A330798ODE n p := by
  dsimp [A330798ODE]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  ring

private lemma A330798_step_num (n : ℕ) :
    C (8 * A330798D n) * A330798 (n + 2) =
      A330798StepNum n (A330798 (n + 1)) (A330798 n) := by
  rw [A330798]
  apply Polynomial.funext
  intro r
  simp only [A330798D, A330798StepNum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h5 : (0 : ℝ) < 2 * (n : ℝ) + 5 := by positivity
  have hden :
      -8 - 3 * (n : ℝ) + 2 * (3 + (n : ℝ)) ^ 2 =
        ((n : ℝ) + 2) * (2 * (n : ℝ) + 5) := by ring
  rw [hden]
  field_simp [h2.ne', h5.ne']
  ring

private theorem A330798_simple_and_ode : ∀ n : ℕ,
    (C (A330798d n) * A330798 (n + 1) =
      A330798SimpleNum n (A330798 n))
      ∧ A330798ODE n (A330798 n) = 0 := by
  intro n
  induction n with
  | zero =>
      constructor
      · norm_num [A330798d, A330798SimpleNum, A330798, map_ofNat, map_mul]
        ring
      · norm_num [A330798ODE, A330798]
  | succ n ih =>
      rcases ih with ⟨hsimple, hode⟩
      have hd : A330798d n ≠ 0 := by
        dsimp [A330798d]
        positivity
      have hD : 8 * A330798D n ≠ 0 := by
        dsimp [A330798D]
        positivity
      constructor
      · have halg := A330798_simple_algebra n (A330798 n)
        simp only [hode, Polynomial.derivative_zero, mul_zero, zero_add] at halg
        have halg' :
            C (A330798d (n + 1)) *
                A330798StepNum n (A330798SimpleNum n (A330798 n))
                  (C (A330798d n) * A330798 n)
              =
            C (8 * A330798D n) *
                A330798SimpleNum (n + 1) (A330798SimpleNum n (A330798 n)) :=
          sub_eq_zero.mp halg
        rw [show n + 1 + 1 = n + 2 by lia]
        apply mul_left_cancel₀ (show C (8 * A330798D n * A330798d n) ≠ 0 by
          simp_all)
        calc
          C (8 * A330798D n * A330798d n) *
                (C (A330798d (n + 1)) * A330798 (n + 2))
              =
              C (A330798d (n + 1)) * C (A330798d n) *
                (C (8 * A330798D n) * A330798 (n + 2)) := by grind
          _ = C (A330798d (n + 1)) * C (A330798d n) *
                A330798StepNum n (A330798 (n + 1)) (A330798 n) := by
              rw [A330798_step_num]
          _ = C (A330798d (n + 1)) *
                A330798StepNum n
                  (C (A330798d n) * A330798 (n + 1))
                  (C (A330798d n) * A330798 n) := by
              rw [A330798_stepNum_C_mul]
              ring
          _ = C (A330798d (n + 1)) *
                A330798StepNum n (A330798SimpleNum n (A330798 n))
                  (C (A330798d n) * A330798 n) := by simp_all
          _ = C (8 * A330798D n) *
                A330798SimpleNum (n + 1) (A330798SimpleNum n (A330798 n)) :=
              halg'
          _ = C (8 * A330798D n) *
                A330798SimpleNum (n + 1)
                  (C (A330798d n) * A330798 (n + 1)) := by simp_all
          _ = C (8 * A330798D n) * C (A330798d n) *
                A330798SimpleNum (n + 1) (A330798 (n + 1)) := by
              rw [A330798_simpleNum_C_mul]
              ring
          _ = C (8 * A330798D n * A330798d n) *
                A330798SimpleNum (n + 1) (A330798 (n + 1)) := by
                  simp
      · apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hd)
        calc
          C (A330798d n) * A330798ODE (n + 1) (A330798 (n + 1))
              = A330798ODE (n + 1)
                  (C (A330798d n) * A330798 (n + 1)) := by
                    rw [A330798_ode_C_mul]
          _ = A330798ODE (n + 1) (A330798SimpleNum n (A330798 n)) := by simp_all
          _ = (C (2 * ((n : ℝ) + 2) *
                    (7 * (n : ℝ) ^ 2 + 19 * (n : ℝ) + 9))
                  + C (2 * ((n : ℝ) + 2) *
                      (9 * (n : ℝ) ^ 2 + 24 * (n : ℝ) + 12)) * X) *
                A330798ODE n (A330798 n)
              + (C ((n : ℝ) + 2) * (1 + X) *
                  (C (n : ℝ) + C (9 * (n : ℝ) + 6) * X)) *
                (A330798ODE n (A330798 n)).derivative :=
                  A330798_ode_algebra n (A330798 n)
          _ = C (A330798d n) * 0 := by simp_all

private lemma A330798_simple_succ (n : ℕ) :
    C (A330798d n) * A330798 (n + 1) =
      A330798SimpleNum n (A330798 n) :=
  (A330798_simple_and_ode n).1

private lemma A330798_ode (n : ℕ) : A330798ODE n (A330798 n) = 0 :=
  (A330798_simple_and_ode n).2

private lemma A330798_ode_coeff (n k : ℕ) (p : ℝ[X]) :
    (A330798ODE n p).coeff k =
      (((k : ℝ) + 1) * ((k : ℝ) + (n : ℝ) + 2)) * p.coeff (k + 1)
        + ((k : ℝ) * ((k : ℝ) + (n : ℝ) + 1)
          - (n : ℝ) * (2 * (n : ℝ) + 1)) * p.coeff k := by
  rw [A330798ODE]
  rw [show X * (1 + X) * p.derivative.derivative =
      X * p.derivative.derivative
        + X * (X * p.derivative.derivative) by ring]
  rw [show C ((n : ℝ) + 2) * (1 + X) * p.derivative =
      C ((n : ℝ) + 2) * p.derivative
        + X * (C ((n : ℝ) + 2) * p.derivative) by ring]
  cases k with
  | zero =>
      simp [coeff_derivative]
      ring
  | succ k =>
      cases k with
      | zero =>
          simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul,
            coeff_derivative]
          rw [coeff_X_mul_zero]
          grind
      | succ k =>
          simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul,
            coeff_derivative]
          grind

private lemma A330798_ode_natDegree_le
    (n : ℕ) {p : ℝ[X]} (hp : p ≠ 0)
    (hode : A330798ODE n p = 0) :
    p.natDegree ≤ n := by
  by_contra hdeg
  have hmn : n < p.natDegree := by lia
  have : p.coeff p.natDegree ≠ 0 := by simp_all
  have habove : p.coeff (p.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by lia)
  have hc := congrArg (fun f : ℝ[X] ↦ f.coeff p.natDegree) hode
  rw [A330798_ode_coeff, Polynomial.coeff_zero, habove, mul_zero,
    zero_add] at hc
  have hfac :
      0 < (p.natDegree : ℝ) * ((p.natDegree : ℝ) + (n : ℝ) + 1)
          - (n : ℝ) * (2 * (n : ℝ) + 1) := by
    have : (n : ℝ) < (p.natDegree : ℝ) := by simp_all
    nlinarith
  simp_all


private lemma A330798_const_coeff_pos : ∀ n : ℕ, 0 < (A330798 n).coeff 0
  | 0 => by norm_num [A330798]
  | n + 1 => by
      have hprev := A330798_const_coeff_pos n
      have hs := congrArg (fun p : ℝ[X] => p.coeff 0)
        (A330798_simple_succ n)
      have ho := congrArg (fun p : ℝ[X] => p.coeff 0)
        (A330798_ode n)
      rw [A330798_ode_coeff, Polynomial.coeff_zero] at ho
      norm_num at ho
      simp only [A330798d, map_mul, map_pow, map_add, map_natCast, map_one,
        mul_coeff_zero, coeff_C_zero, coeff_add, coeff_natCast_ite, ↓reduceIte,
        A330798SimpleNum, coeff_one_zero, coeff_X_zero, mul_zero, add_zero,
        coeff_X_pow, OfNat.zero_ne_ofNat, coeff_derivative, zero_add,
        CharP.cast_eq_zero, mul_one] at hs
      have hcoeff :
          ((((n : ℕ) : ℝ[X]) + 1) ^ 2).coeff 0 =
            ((n : ℝ) + 1) ^ 2 := by
        rw [coeff_zero_eq_eval_zero]
        simp
      rw [hcoeff] at hs
      have hd : 0 < A330798d n := by
        rw [A330798d]
        positivity
      have hpone : 0 ≤ (A330798 n).coeff 1 := by
        have hfac : 0 < (n : ℝ) + 2 := by positivity
        have hrhs :
            0 ≤ (n : ℝ) * (2 * (n : ℝ) + 1) *
              (A330798 n).coeff 0 := by positivity
        nlinarith
      have hright1 :
          0 < ((n : ℝ) + 2) * (2 * (n : ℝ) + 1) *
            (7 * (n : ℝ) + 6) * (A330798 n).coeff 0 := by
        positivity
      have hright2 :
          0 ≤ (n : ℝ) * ((n : ℝ) + 2) * (A330798 n).coeff 1 := by
        positivity
      have hleftfac :
          0 < 2 * ((n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3) := by
        positivity
      nlinarith

private lemma A330798_coeff_pos_of_le (n k : ℕ) (hk : k ≤ n) :
    0 < (A330798 n).coeff k := by
  induction k with
  | zero => exact A330798_const_coeff_pos n
  | succ k ih =>
      have hkn : k < n := by lia
      have hkcast : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
      have hprev := ih (by lia)
      have hode := congrArg (fun p : ℝ[X] => p.coeff k) (A330798_ode n)
      rw [A330798_ode_coeff, Polynomial.coeff_zero] at hode
      have hleft : 0 < ((k : ℝ) + 1) * ((k : ℝ) + (n : ℝ) + 2) := by
        positivity
      have hright :
          (k : ℝ) * ((k : ℝ) + (n : ℝ) + 1) -
              (n : ℝ) * (2 * (n : ℝ) + 1) < 0 := by
        nlinarith
      nlinarith

private lemma A330798_degree_and_leadingCoeff_pos (n : ℕ) :
    (A330798 n).natDegree = n ∧ 0 < (A330798 n).leadingCoeff := by
  have hzero := A330798_const_coeff_pos n
  have hne : A330798 n ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ[X] => p.coeff 0) h
    simp_all
  have hle := A330798_ode_natDegree_le n hne (A330798_ode n)
  have htop := A330798_coeff_pos_of_le n n (le_refl n)
  have hdeg : (A330798 n).natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hle htop.ne'
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg]
  exact htop

private def b1dd (n : ℕ) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  C (q * (25 / 8 + 7 / 8 * r)) * X + C (9 / 8 * q * (3 + r)) * X ^ 2

private def b0dd (n : ℕ) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  C (1 / 4 * r * q) + C (-1 / 2 * q) * X

private def b1d (n : ℕ) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  C (q * (21 / 2 - 1 / 8 * (3 + r) ^ 2 + 11 / 2 * r))
    + C (q * (99 / 4 - 9 / 8 * (3 + r) ^ 2 + 39 / 4 * r)) * X
    + C (q * (-75 / 4 - 99 / 4 * r)) * X ^ 2
    + C (q * (-36 - 36 * r)) * X ^ 3

private def b0d (n : ℕ) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  C (q * (-1 - 2 * r)) + C (18 * q) * X + C (33 * q) * X ^ 2
    + C (q * (-9 - 27 / 2 * r)) * X ^ 3

private def b1 (n : ℕ) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  C (q * (57 / 2 + 15 * r - 15 / 8 * (3 + r) ^ 2))
    + C (q * (-150 - 75 * r + 81 / 4 * (3 + r) ^ 2)) * X
    + C (q * (-288 - 144 * r + 36 * (3 + r) ^ 2)) * X ^ 2

private def b0 (n : ℕ) : ℝ[X] :=
  let r : ℝ := n
  let q : ℝ := 1 / (-8 - 3 * r + 2 * (3 + r) ^ 2)
  C (q * (-63 + 9 * (3 + r) ^ 2 - 27 / 2 * r))
    + C (q * (-48 + 9 * (3 + r) ^ 2 + 33 / 2 * r)) * X
    + C (q * (234 - 27 * (3 + r) ^ 2 + 261 / 2 * r)) * X ^ 2

private def terms330 : List (ℕ × ℕ × (ℕ → ℝ[X])) :=
  [(1, 2, b1dd), (0, 2, b0dd), (1, 1, b1d),
    (0, 1, b0d), (1, 0, b1), (0, 0, b0)]

private lemma A330798_rhs (n : ℕ) :
    A330798 (n + 2) = RealRooted.LinRec.rhs terms330 A330798 n := by
  simp only [terms330, RealRooted.LinRec.rhs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Function.iterate_succ_apply,
    Function.iterate_zero, id_eq, add_zero]
  rw [A330798]
  simp only [b1dd, b0dd, b1d, b0d, b1, b0]
  ring

private lemma natDegree_cubic_le (a b c d : ℝ) :
    (C a + C b * X + C c * X ^ 2 + C d * X ^ 3).natDegree ≤ 3 := by
  compute_degree!

private lemma natDegree_quadratic_full_le (a b c : ℝ) :
    (C a + C b * X + C c * X ^ 2).natDegree ≤ 2 := by
  compute_degree!

private lemma b1dd_natDegree_le (n : ℕ) : (b1dd n).natDegree ≤ 2 := by
  exact natDegree_quadratic_le _ _

private lemma b0dd_natDegree_le (n : ℕ) : (b0dd n).natDegree ≤ 1 := by
  exact natDegree_linear_le _ _

private lemma b1d_natDegree_le (n : ℕ) : (b1d n).natDegree ≤ 3 := by
  exact natDegree_cubic_le _ _ _ _

private lemma b0d_natDegree_le (n : ℕ) : (b0d n).natDegree ≤ 3 := by
  exact natDegree_cubic_le _ _ _ _

private lemma b1_natDegree_le (n : ℕ) : (b1 n).natDegree ≤ 2 := by
  exact natDegree_quadratic_full_le _ _ _

private lemma b0_natDegree_le (n : ℕ) : (b0 n).natDegree ≤ 2 := by
  exact natDegree_quadratic_full_le _ _ _

private lemma terms330_natDegree_le (t : ℕ × ℕ × (ℕ → ℝ[X]))
    (ht : t ∈ terms330) (n : ℕ) :
    (t.2.2 n).natDegree ≤ n + 2 + 1 - (n + t.1) + t.2.1 := by
  simp only [terms330, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (b1dd_natDegree_le n).trans (by lia)
  · exact (b0dd_natDegree_le n).trans (by lia)
  · exact (b1d_natDegree_le n).trans (by lia)
  · exact (b0d_natDegree_le n).trans (by lia)
  · exact (b1_natDegree_le n).trans (by lia)
  · exact (b0_natDegree_le n).trans (by lia)

/-- The A330798 rows have degree `n` and positive leading coefficient.  The proof applies
the multi-lag cancellation law with one excess degree; the differential-equation invariant
certifies cancellation only after all six recurrence summands have been combined. -/
theorem A330798_natDegree_eq_and_leadingCoeff_pos (n : ℕ) :
    (A330798 n).natDegree = n ∧ 0 < (A330798 n).leadingCoeff := by
  have h := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_pos_of_topWindow
    (k := 2) (e := 1) (D := fun m => m) (P := A330798) (terms := terms330)
    (S := fun m p => A330798ODE m p = 0 ∧ 0 < p.coeff 0)
    A330798_rhs (by simp [terms330])
    (by intro m j hj; lia) terms330_natDegree_le (by
      intro j hj
      interval_cases j
      · norm_num [A330798, A330798ODE]
      · norm_num [A330798, A330798ODE]
        constructor
        · compute_degree!
        · ring) (by
      intro m _
      rw [← A330798_rhs m]
      have hrow := A330798_degree_and_leadingCoeff_pos (m + 2)
      refine ⟨?_, ?_, A330798_ode (m + 2), A330798_const_coeff_pos (m + 2)⟩
      · intro r hr hre
        have hr' : r = 1 := by lia
        subst r
        exact coeff_eq_zero_of_natDegree_lt (by rw [hrow.1]; lia)
      · have hpos := hrow.2
        rw [leadingCoeff, hrow.1] at hpos
        exact hpos) n
  exact ⟨h.1, h.2.1⟩

/-- The natural degree of the A330798 row indexed by `n` is `n`. -/
theorem A330798_natDegree (n : ℕ) : (A330798 n).natDegree = n :=
  (A330798_natDegree_eq_and_leadingCoeff_pos n).1

/-- The A330798 row indexed by `n` has positive leading coefficient. -/
theorem A330798_leadingCoeff_pos (n : ℕ) : 0 < (A330798 n).leadingCoeff :=
  (A330798_natDegree_eq_and_leadingCoeff_pos n).2

end

end RealRooted.Tactic.RowParityDegree
