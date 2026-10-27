module

import RealRooted.EulerBidiagonal.GeneralRows
public import RealRooted.GarloffWagner
import RealRooted.Interlacing.Reversal
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
import RealRooted.GarloffWagner.Theorem12
public import RealRooted.Basic.ProperPosition

/-!
# The row polynomials of OEIS A394813

The generated order-two recurrence hides a first-order general Euler row after
factorial scaling and reversal.  The general Euler theorem gives strict
interlacing, factorial division preserves it, and reversal transports it back.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A394813

/-- The generated order-two update for A394813. -/
def nextRow (n : ℕ) (q p : ℝ[X]) : ℝ[X] :=
  (C 1 * X ^ 3) * p.derivative.derivative +
    (C (-1) * X ^ 3) * q.derivative.derivative +
    (C (-3 - 2 * (n : ℝ)) * X ^ 2) * p.derivative +
    (C (2 * (n : ℝ)) * X ^ 2) * q.derivative +
    (C 2 + C (-5 + (3 + (n : ℝ)) ^ 2 - 2 * (n : ℝ)) * X) * p +
    (C (-1) + C (9 - (3 + (n : ℝ)) ^ 2 + 5 * (n : ℝ)) * X) * q

/-- The recurrence model for A394813. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | n + 2 => nextRow n (polynomial n) (polynomial (n + 1))

private lemma polynomial_succ_normalized (n : ℕ) :
    polynomial (n + 2) =
      X ^ 3 * ((polynomial (n + 1)).derivative.derivative -
        (polynomial n).derivative.derivative)
      - C (2 * (n : ℝ) + 3) * X ^ 2 * (polynomial (n + 1)).derivative
      + C (2 * (n : ℝ)) * X ^ 2 * (polynomial n).derivative
      + (C 2 + C (((n : ℝ) + 2) ^ 2) * X) * polynomial (n + 1)
      + (C (-1) - C ((n : ℝ) * ((n : ℝ) + 1)) * X) * polynomial n := by
  rw [polynomial]
  unfold nextRow
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
  ring

private lemma coeff_succ (n k : ℕ) (hk : 1 ≤ k) :
    (polynomial (n + 2)).coeff k =
      2 * (polynomial (n + 1)).coeff k - (polynomial n).coeff k
        + (((k : ℝ) - (n : ℝ) - 3) ^ 2) * (polynomial (n + 1)).coeff (k - 1)
        - (((k : ℝ) - (n : ℝ) - 2) * ((k : ℝ) - (n : ℝ) - 1)) *
            (polynomial n).coeff (k - 1) := by
  rw [polynomial_succ_normalized]
  rw [show
      X ^ 3 * ((polynomial (n + 1)).derivative.derivative -
          (polynomial n).derivative.derivative)
        - C (2 * (n : ℝ) + 3) * X ^ 2 * (polynomial (n + 1)).derivative
        + C (2 * (n : ℝ)) * X ^ 2 * (polynomial n).derivative
        + (C 2 + C (((n : ℝ) + 2) ^ 2) * X) * polynomial (n + 1)
        + (C (-1) - C ((n : ℝ) * ((n : ℝ) + 1)) * X) * polynomial n =
      X ^ 3 * (polynomial (n + 1)).derivative.derivative
        - X ^ 3 * (polynomial n).derivative.derivative
        - C (2 * (n : ℝ) + 3) * (X ^ 2 * (polynomial (n + 1)).derivative)
        + C (2 * (n : ℝ)) * (X ^ 2 * (polynomial n).derivative)
        + C 2 * polynomial (n + 1)
        + C (((n : ℝ) + 2) ^ 2) * (X * polynomial (n + 1))
        - polynomial n
        - C ((n : ℝ) * ((n : ℝ) + 1)) * (X * polynomial n) by grind]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  cases j with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
        coeff_X_mul, coeff_derivative, ite_eq_right (by lia : ¬3 ≤ 1),
        ite_eq_right (by lia : ¬2 ≤ 1)]
      grind
  | succ j =>
      cases j with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
            coeff_derivative, coeff_X_pow_mul', ite_eq_right (by lia : ¬3 ≤ 2),
            ite_eq_left (by lia : 2 ≤ 2)]
          grind
      | succ j =>
          simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_derivative,
            coeff_X_pow_mul', ite_eq_left (by lia : 3 ≤ (j + 1 + 1) + 1),
            ite_eq_left (by lia : 2 ≤ (j + 1 + 1) + 1)]
          rw [show j + 1 + 1 + 1 = (j + 1 + 1) + 1 by lia,
            coeff_X_mul, coeff_X_mul]
          grind

private lemma coeff_zero_succ (n : ℕ) :
    (polynomial (n + 2)).coeff 0 =
      2 * (polynomial (n + 1)).coeff 0 - (polynomial n).coeff 0 := by
  rw [polynomial_succ_normalized]
  simp
  ring

private lemma coeff_invariant :
    ∀ n : ℕ,
      (polynomial n).coeff 0 = (n : ℝ) + 1 ∧
        (polynomial n).coeff n = 1 ∧
          (∀ k > n, (polynomial n).coeff k = 0) ∧
            ∀ k, 1 ≤ k → k ≤ n →
              ((n : ℝ) - (k : ℝ) + 1) * (polynomial (n + 1)).coeff k =
                ((n : ℝ) - (k : ℝ) + 2) * (polynomial n).coeff k +
                  ((n : ℝ) - (k : ℝ) + 1) *
                    ((n : ℝ) - (k : ℝ) + 2) ^ 2 *
                      (polynomial n).coeff (k - 1)
  | 0 => by
      refine ⟨by simp [polynomial], by simp [polynomial], ?_, ?_⟩
      · intro k hk
        rw [show polynomial 0 = 1 from rfl, coeff_one]
        grind
      · grind
  | n + 1 => by
      rcases coeff_invariant n with ⟨hc0, htop, habove, hstep⟩
      have hc0_succ : (polynomial (n + 1)).coeff 0 = (n : ℝ) + 2 := by
        cases n with
        | zero => simp [polynomial]
        | succ n =>
            have hprev := (coeff_invariant n).1
            rw [coeff_zero_succ n, hc0, hprev]
            grind
      have htop_succ : (polynomial (n + 1)).coeff (n + 1) = 1 := by
        cases n with
        | zero => simp [polynomial]
        | succ n =>
            rw [coeff_succ n (n + 2) (by lia), habove (n + 2) (by lia),
              (coeff_invariant n).2.2.1 (n + 2) (by lia),
              show n + 2 - 1 = n + 1 by lia, htop]
            grind
      have habove_succ : ∀ k > n + 1, (polynomial (n + 1)).coeff k = 0 := by
        intro k hk
        cases n with
        | zero =>
            rw [show polynomial 1 = 2 + X from rfl]
            apply coeff_eq_zero_of_natDegree_lt
            rwa [show (2 + X : ℝ[X]).natDegree = 1 by compute_degree!]
        | succ n =>
            rw [coeff_succ n k (by lia), habove k (by lia),
              (coeff_invariant n).2.2.1 k (by lia), habove (k - 1) (by lia),
              (coeff_invariant n).2.2.1 (k - 1) (by lia)]
            ring
      refine ⟨?_, htop_succ, habove_succ, ?_⟩
      · grind
      intro k hk hkn
      by_cases hkn1 : k = n + 1
      · subst k
        rw [coeff_succ n (n + 1) (by assumption), habove (n + 1) (by lia),
          show n + 1 - 1 = n by lia, htop, htop_succ]
        grind
      · have hkn' : k ≤ n := by lia
        have ih := hstep k hk hkn'
        rw [coeff_succ n k hk]
        grind

/-- The recurrence row indexed by `n` has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  rcases coeff_invariant n with ⟨_, htop, habove, _⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun k hk ↦ habove k hk))
    (by simp_all)

private def scaledReversal : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      thetaPlusOne (thetaPlusOne (scaledReversal n) + X * scaledReversal n)

private lemma coeff_scaledReversal_succ (n k : ℕ) :
    (scaledReversal (n + 1)).coeff k =
      ((k : ℝ) + 1) ^ 2 * (scaledReversal n).coeff k +
        (if 1 ≤ k then ((k : ℝ) + 1) * (scaledReversal n).coeff (k - 1) else 0) := by
  rw [scaledReversal, coeff_thetaPlusOne, coeff_add]
  by_cases hk : 1 ≤ k
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    simp only [coeff_thetaPlusOne, coeff_X_mul]
    rw [ite_eq_left (by lia : 1 ≤ j + 1)]
    grind
  · simp_all

private lemma scaledReversal_top_and_above :
    ∀ n : ℕ,
      0 < (scaledReversal n).coeff n ∧
        ∀ k > n, (scaledReversal n).coeff k = 0
  | 0 => by
      constructor
      · simp [scaledReversal]
      · intro k hk
        rw [show scaledReversal 0 = 1 from rfl, coeff_one]
        grind
  | n + 1 => by
      rcases scaledReversal_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [coeff_scaledReversal_succ, habove (n + 1) (by lia),
          ite_eq_left (by lia), show n + 1 - 1 = n by lia]
        positivity
      · intro k hk
        rw [coeff_scaledReversal_succ, habove k (by lia)]
        grind

private lemma scaledReversal_natDegree (n : ℕ) :
    (scaledReversal n).natDegree = n := by
  rcases scaledReversal_top_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => habove k hk))
    htop.ne'

private lemma scaledReversal_ne_zero (n : ℕ) : scaledReversal n ≠ 0 := by
  intro hzero
  have htop := (scaledReversal_top_and_above n).1
  simp_all

private lemma scaledReversal_coeff_eq_factorial_mul :
    ∀ n k : ℕ, k ≤ n →
      (scaledReversal n).coeff k =
        (Nat.factorial k : ℝ) * (polynomial n).coeff (n - k)
  | 0, k, hk => by
      have hk0 : k = 0 := by lia
      subst k
      simp [scaledReversal, polynomial]
  | n + 1, k, hk => by
      by_cases hk0 : k = 0
      · subst k
        rw [coeff_scaledReversal_succ]
        simp only [Nat.cast_zero, zero_add, one_pow,
          ite_eq_right (by lia : ¬1 ≤ 0),
          add_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
        rw [scaledReversal_coeff_eq_factorial_mul n 0 (by lia)]
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero]
        rw [(coeff_invariant n).2.1, (coeff_invariant (n + 1)).2.1]
      · have hk1 : 1 ≤ k := by lia
        by_cases hktop : k = n + 1
        · subst k
          rw [coeff_scaledReversal_succ, ite_eq_left (by assumption),
            (scaledReversal_top_and_above n).2 (n + 1) (by lia),
            show n + 1 - 1 = n by lia,
            scaledReversal_coeff_eq_factorial_mul n n (by lia),
            show n - n = 0 by lia, (coeff_invariant n).1,
            show n + 1 - (n + 1) = 0 by lia, (coeff_invariant (n + 1)).1]
          rw [Nat.factorial_succ]
          grind
        · have hkle : k ≤ n := by lia
          rw [coeff_scaledReversal_succ, ite_eq_left hk1,
            scaledReversal_coeff_eq_factorial_mul n k hkle,
            scaledReversal_coeff_eq_factorial_mul n (k - 1) (by lia)]
          have hstep := (coeff_invariant n).2.2.2
            (n - k + 1) (by lia) (by lia)
          have hsub0 : n + 1 - k = n - k + 1 := by lia
          have hsub3 : n - (k - 1) = n - k + 1 := by lia
          have hsub4 : n - k + 1 - 1 = n - k := by lia
          rw [hsub0, hsub3]
          rw [hsub4] at hstep
          have hfac : (Nat.factorial k : ℝ) =
              (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
            rw [Nat.factorial_succ]
            simp
          rw [hfac]
          push_cast [Nat.cast_sub hkle,
            Nat.cast_sub (by lia : k - 1 ≤ n)] at hstep ⊢
          nlinarith

private lemma divFactorial_scaledReversal_eq_reflect (n : ℕ) :
    divFactorial (scaledReversal n) = Polynomial.reflect n (polynomial n) := by
  apply Polynomial.ext
  intro k
  rw [coeff_divFactorial, Polynomial.coeff_reflect]
  by_cases hk : k ≤ n
  · rw [Polynomial.revAt_le hk, scaledReversal_coeff_eq_factorial_mul n k hk]
    have hfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    simp_all
  · have hkn : n < k := by lia
    rw [Polynomial.revAt_eq_self_of_lt hkn,
      (scaledReversal_top_and_above n).2 k hkn,
      (coeff_invariant n).2.2.1 k hkn]
    simp

private lemma scaledReversal_eq_generalRows (n : ℕ) :
    scaledReversal n = EulerBidiagonal.generalRows 1 1 1 2 1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [scaledReversal, EulerBidiagonal.generalRows, ih]
      rw [EulerBidiagonal.generalStep_eq_second_derivative]
      simp only [thetaPlusOne, theta, derivative_add, derivative_mul,
        derivative_X, one_mul, C_1, C_ofNat]
      norm_num [map_ofNat]
      ring

private lemma generalRows_data (n : ℕ) :
    IsNegativeSimple (EulerBidiagonal.generalRows 1 1 1 2 1 n) ∧
      (EulerBidiagonal.generalRows 1 1 1 2 1 n).natDegree = n ∧
      StrictInterl (EulerBidiagonal.generalRows 1 1 1 2 1 n)
        (EulerBidiagonal.generalRows 1 1 1 2 1 (n + 1)) := by
  have hQ : ∀ t : ℝ, t ≤ 0 →
      EulerBidiagonal.comparisonDefect 1 1 1 2 1 t < 0 :=
    EulerBidiagonal.comparisonDefect_neg_of_two_mul_u_ge
      1 1 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := EulerBidiagonal.generalRows_spec 1 1 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (fun k => by positivity) hQ n
  exact ⟨h.1, h.2.1, h.2.2.1⟩

private lemma generalRows_nonneg : ∀ n : ℕ,
    HasNonnegCoeffs (EulerBidiagonal.generalRows 1 1 1 2 1 n)
  | 0 => by
      simpa [EulerBidiagonal.generalRows] using hasNonnegCoeffs_one
  | n + 1 => by
      rw [EulerBidiagonal.generalRows]
      apply EulerBidiagonal.hasNonnegCoeffs_generalStep 1 1 1 2 1
        (EulerBidiagonal.generalRows 1 1 1 2 1 n) n
      · exact (generalRows_data n).2.1
      · norm_num
      · norm_num
      · norm_num
      · intro k hk
        positivity
      · exact generalRows_nonneg n

/-- Consecutive A394813 recurrence rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) := by
  let R : ℕ → ℝ[X] := fun m => divFactorial (scaledReversal m)
  have hRdeg : ∀ m, (R m).natDegree = m := by
    intro m
    change (divFactorial (scaledReversal m)).natDegree = m
    rw [natDegree_divFactorial (scaledReversal_ne_zero m),
      scaledReversal_natDegree]
  have hRnn : ∀ m, HasNonnegCoeffs (R m) := by
    intro m
    apply HasNonnegCoeffs.divFactorial
    rw [scaledReversal_eq_generalRows]
    exact generalRows_nonneg m
  have hRinterlaces : ∀ m, Interlaces (R m) (R (m + 1)) := by
    intro m
    apply StrictInterl.toInterlaces
    · apply StrictInterl.divFactorial
      rw [scaledReversal_eq_generalRows, scaledReversal_eq_generalRows]
      exact (generalRows_data m).2.2
    · rw [hRdeg, hRdeg]
  apply interlaces_of_eq_reflect (P := polynomial) (R := R) (D₀ := 0)
    (fun m => by
      dsimp only [R]
      simp only [Nat.zero_add]
      rw [divFactorial_scaledReversal_eq_reflect]
      exact reflect_reflect.symm)
    (fun m => by simpa using hRdeg m) hRnn
    (fun m => by simpa using polynomial_natDegree m)
    (fun m => by
      rw [leadingCoeff, polynomial_natDegree]
      rw [(coeff_invariant m).2.1]
      norm_num)
    hRinterlaces n

private lemma polynomial_zero : polynomial 0 = 1 := rfl

private lemma polynomial_one : polynomial 1 = 2 + X := rfl

private lemma polynomial_step (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial n) (polynomial (n + 1)) := rfl

/-- Any sequence satisfying the generated A394813 recurrence has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P n) (P (n + 1)))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence
    (P := P) (Q := polynomial) (fun m p q => nextRow m q p)
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_step
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A394813
