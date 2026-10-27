module

import RealRooted.LiuWang.FiniteFamily
import RealRooted.WagnerX.AffineFactors
import RealRooted.Linear
public import RealRooted.Basic.ProperPosition

/-!
# A derivative--lag OEIS row

This file proves real-rootedness and the nonexceptional consecutive interlacing for A271697.
The row at index one is zero, so the interlacing chain starts at index two.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined A271697 row family. -/
def A271697 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      (X - X ^ 2) * (A271697 (n + 1)).derivative +
        C (1 + (n : ℝ)) * X * A271697 (n + 1) +
          C (1 + (n : ℝ)) * X * A271697 n

/-- The defining derivative--lag recurrence for A271697. -/
theorem A271697_add_two (n : ℕ) :
    A271697 (n + 2) =
      C (1 + (n : ℝ)) * X * A271697 (n + 1) +
        (X - X ^ 2) * (A271697 (n + 1)).derivative +
          C (1 + (n : ℝ)) * X * A271697 n := by
  rw [A271697]
  ring_nf

private theorem A271697_coeff_add_two (n k : ℕ) :
    (A271697 (n + 2)).coeff (k + 1) =
      ((k : ℝ) + 1) * (A271697 (n + 1)).coeff (k + 1) +
        ((n : ℝ) + 1 - (k : ℝ)) * (A271697 (n + 1)).coeff k +
          ((n : ℝ) + 1) * (A271697 n).coeff k := by
  rw [A271697_add_two]
  have hsplit :
      C (1 + (n : ℝ)) * X * A271697 (n + 1) +
          (X - X ^ 2) * (A271697 (n + 1)).derivative +
          C (1 + (n : ℝ)) * X * A271697 n =
        X * (A271697 (n + 1)).derivative -
          X ^ 2 * (A271697 (n + 1)).derivative +
          C ((n : ℝ) + 1) * (X * A271697 (n + 1)) +
          C ((n : ℝ) + 1) * (X * A271697 n) := by
    ring_nf
  rw [hsplit]
  rcases k with _ | k
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative]
    simp
  · rw [show k + 1 + 1 = k + 2 by ring_nf]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative]
    rw [ite_eq_left (by lia : 2 ≤ k + 2), show k + 2 - 2 = k by lia]
    push_cast
    ring_nf

private theorem A271697_coeff_above (n N : ℕ) (hN : n - 1 < N) :
    (A271697 n).coeff N = 0 := by
  revert N
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro N hN
      match n with
      | 0 =>
          rw [A271697, coeff_one]
          rw [ite_eq_right (Nat.ne_of_gt hN)]
      | 1 => simp [A271697]
      | k + 2 =>
          rcases N with _ | j
          · simp at hN
          · rw [A271697_coeff_add_two]
            rw [ih (k + 1) (by lia) (j + 1) (by lia),
              ih (k + 1) (by lia) j (by lia), ih k (by lia) j (by lia)]
            simp

private theorem A271697_top_coeff_ne (n : ℕ) (hn : n ≠ 1) :
    (A271697 n).coeff (n - 1) ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => simp [A271697]
      | 1 => contradiction
      | k + 2 =>
          rcases k with _ | k
          · norm_num [A271697]
          · rw [show (k + 1 + 2) - 1 = k + 2 by lia, A271697_coeff_add_two]
            rw [A271697_coeff_above (k + 2) (k + 2) (by lia),
              A271697_coeff_above (k + 1) (k + 1) (by lia)]
            have htop := ih (k + 2) (by lia) (by lia)
            rw [show k + 2 - 1 = k + 1 by lia] at htop
            push_cast
            ring_nf
            simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htop

/-- The degree of A271697, including its exceptional zero row. -/
theorem A271697_natDegree (n : ℕ) : (A271697 n).natDegree = n - 1 := by
  rcases n with _ | n
  · simp [A271697]
  rcases n with _ | n
  · simp [A271697]
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr
      (fun N hN ↦ A271697_coeff_above (n + 2) N hN))
    (A271697_top_coeff_ne (n + 2) (by lia))

private theorem A271697_hasNonnegCoeffs : ∀ n, HasNonnegCoeffs (A271697 n)
  | 0 => by simpa [A271697] using hasNonnegCoeffs_one
  | 1 => by simpa [A271697] using hasNonnegCoeffs_zero
  | n + 2 => by
      have hnext := A271697_hasNonnegCoeffs (n + 1)
      have hprev := A271697_hasNonnegCoeffs n
      intro k
      rcases k with _ | k
      · simp [A271697]
      · rw [A271697_coeff_add_two]
        have hfirst : 0 ≤ ((k : ℝ) + 1) * (A271697 (n + 1)).coeff (k + 1) :=
          mul_nonneg (by positivity) (hnext (k + 1))
        have hthird : 0 ≤ ((n : ℝ) + 1) * (A271697 n).coeff k :=
          mul_nonneg (by positivity) (hprev k)
        by_cases hk : k ≤ n + 1
        · have hkR : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk
          have hsecond :
              0 ≤ ((n : ℝ) + 1 - (k : ℝ)) * (A271697 (n + 1)).coeff k :=
            mul_nonneg (sub_nonneg.mpr hkR) (hnext k)
          linarith
        · have hk' : n < k := by lia
          rw [A271697_coeff_above (n + 1) k (by simpa using hk')]
          linarith

private theorem A271697_ne_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) : A271697 n ≠ 0 := by
  intro hzero
  have htop := A271697_top_coeff_ne n (by lia)
  simp [hzero] at htop

private theorem A271697_hasPosLeadingCoeff_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    HasPosLeadingCoeff (A271697 n) :=
  (A271697_hasNonnegCoeffs n).pos_leadingCoeff (A271697_ne_zero_of_two_le hn)

private theorem A271697_two : A271697 2 = X := by
  simp [A271697]

private theorem A271697_three : A271697 3 = X + X ^ 2 := by
  rw [A271697, A271697_two, show A271697 1 = 0 by rfl]
  simp only [derivative_X, mul_one, mul_zero, add_zero, Nat.cast_one]
  norm_num [map_ofNat]
  ring_nf

private theorem A271697_base_strictInterl : StrictInterl (A271697 2) (A271697 3) := by
  rw [A271697_two, A271697_three]
  have hlinear : StrictInterl (1 : ℝ[X]) (X + 1) :=
    (interlaces_one_linear (p := (X + 1 : ℝ[X])) (by simp)).toStrictInterl
  have hmul := hlinear.mul_common_factor X_ne_zero Splits.X
  convert hmul using 1 <;> ring_nf

private theorem A271697_derivative_eval_nonpos (n : ℕ) {r : ℝ}
    (hr : (A271697 (n + 3)).IsRoot r) : (X - X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hr_nonpos : r ≤ 0 := isRoot_nonpos_of_hasNonnegCoeffs
    (A271697_hasNonnegCoeffs (n + 3)) (A271697_ne_zero_of_two_le (by lia)) hr
  simp only [eval_sub, eval_X, eval_pow]
  nlinarith [sq_nonneg r]

/-- Consecutive A271697 rows strictly interlace from row two onward. -/
theorem A271697_strictInterl_add_two (m : ℕ) :
    StrictInterl (A271697 (m + 2)) (A271697 (m + 3)) := by
  induction m with
  | zero => exact A271697_base_strictInterl
  | succ n hprev =>
      have hrec : A271697 (n + 4) =
          (C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 3) +
            (X - X ^ 2) * (A271697 (n + 3)).derivative +
              (C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 2) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using A271697_add_two (n + 2)
      have hF_pos : HasPosLeadingCoeff
          ((C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 3) +
            (X - X ^ 2) * (A271697 (n + 3)).derivative +
              (C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 2)) := by
        rw [← hrec]
        exact A271697_hasPosLeadingCoeff_of_two_le (by lia)
      have hdeg_lo : (A271697 (n + 3)).natDegree ≤
          ((C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 3) +
            (X - X ^ 2) * (A271697 (n + 3)).derivative +
              (C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 2)).natDegree := by
        rw [← hrec, A271697_natDegree, A271697_natDegree]
        lia
      have hdeg_hi :
          ((C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 3) +
            (X - X ^ 2) * (A271697 (n + 3)).derivative +
              (C (1 + ((n + 2 : ℕ) : ℝ)) * X) * A271697 (n + 2)).natDegree ≤
            (A271697 (n + 3)).natDegree + 1 := by
        rw [← hrec, A271697_natDegree, A271697_natDegree]
        lia
      have hw : ∀ r, (A271697 (n + 3)).IsRoot r →
          (C (1 + ((n + 2 : ℕ) : ℝ)) * X).eval r ≤ 0 := by
        intro r hr
        have hr_nonpos : r ≤ 0 := isRoot_nonpos_of_hasNonnegCoeffs
          (A271697_hasNonnegCoeffs (n + 3))
          (A271697_ne_zero_of_two_le (by lia)) hr
        simp only [eval_mul, eval_C, eval_X]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hr_nonpos
      have hstep := LiuWang.strictInterl_derivative_lag_of_eval_nonpos
        (f := A271697 (n + 3)) (g := A271697 (n + 2))
        (u := C (1 + ((n + 2 : ℕ) : ℝ)) * X) (v := X - X ^ 2)
        (w := C (1 + ((n + 2 : ℕ) : ℝ)) * X)
        (A271697_ne_zero_of_two_le (by lia)) hprev.2.1.2
        (A271697_hasPosLeadingCoeff_of_two_le (by lia)) hprev
        (A271697_hasPosLeadingCoeff_of_two_le (by lia)) hF_pos hdeg_lo hdeg_hi
        (fun r hr ↦ A271697_derivative_eval_nonpos n hr) hw
      rw [← hrec] at hstep
      exact hstep

/-- Consecutive A271697 rows interlace from row two onward. -/
theorem A271697_interlaces_add_two (n : ℕ) :
    Interlaces (A271697 (n + 2)) (A271697 (n + 3)) :=
  (A271697_strictInterl_add_two n).toInterlaces (by
    rw [A271697_natDegree, A271697_natDegree]
    lia)

/-- Every A271697 row splits over the reals; row one is the zero polynomial. -/
theorem A271697_splits (n : ℕ) : (A271697 n).Splits := by
  rcases n with _ | n
  · simp [A271697]
  rcases n with _ | n
  · simp [A271697]
  exact (A271697_strictInterl_add_two n).1.2

end RealRooted.Applications.OEIS
