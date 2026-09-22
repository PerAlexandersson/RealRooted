import RealRooted.JacobiDeformation.Collocation

/-!
# Same-parameter lowering for monic shifted Jacobi polynomials

This file derives the first-order lowering identity from the shifted-Jacobi
differential operator and the monic Favard recurrence.  Keeping the lower
coefficient in terms of `shiftedJacobiSubdiag` preserves its degree-one branch.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem jacobiDifferentialOperator_X_mul_sub_X_mul
    (c s : ℝ) (p : ℝ[X]) :
    jacobiDifferentialOperator c s (X * p) -
        X * jacobiDifferentialOperator c s p =
      2 * X * (1 - X) * p.derivative + (C c - C s * X) * p := by
  simp only [jacobiDifferentialOperator, derivative_mul, derivative_X,
    one_mul, derivative_add]
  ring

private theorem jacobiDifferentialOperator_shiftedJacobiMonic
    (n : ℕ) (α β : ℝ) :
    jacobiDifferentialOperator (α + 1) (α + β + 2)
        (shiftedJacobiMonic n α β) =
      -C (eigenvalue (α + β + 2) n) * shiftedJacobiMonic n α β := by
  have h := positiveJacobiOperator_shiftedJacobiMonic n α β
  change -jacobiDifferentialOperator (α + 1) (α + β + 2)
      (shiftedJacobiMonic n α β) = _ at h
  simpa only [neg_neg, neg_mul] using congrArg Neg.neg h

/-- The same-parameter first-order lowering identity in positive degree.
The successor presentation includes the degree-one case by taking `n = 0`. -/
theorem shiftedJacobiMonic_lowering_succ (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (X : ℝ[X]) * (1 - X) * (shiftedJacobiMonic (n + 1) α β).derivative =
      (-C ((n + 1 : ℕ) : ℝ) * X +
          C (((2 * (n + 1) + (α + β + 2)) *
            shiftedJacobiDiag (n + 1) α β - (α + 1)) / 2)) *
          shiftedJacobiMonic (n + 1) α β +
        C ((2 * (n + 1) + (α + β + 2) - 1) *
          shiftedJacobiSubdiag (n + 1) α β) *
          shiftedJacobiMonic n α β := by
  have hrec :
      X * shiftedJacobiMonic (n + 1) α β =
        shiftedJacobiMonic (n + 2) α β +
          C (shiftedJacobiDiag (n + 1) α β) *
            shiftedJacobiMonic (n + 1) α β +
          C (shiftedJacobiSubdiag (n + 1) α β) *
            shiftedJacobiMonic n α β := by
    simpa only [smul_eq_C_mul] using
      (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).X_mul_succ n
  have hnext :
      shiftedJacobiMonic (n + 2) α β =
        X * shiftedJacobiMonic (n + 1) α β -
          C (shiftedJacobiDiag (n + 1) α β) *
            shiftedJacobiMonic (n + 1) α β -
          C (shiftedJacobiSubdiag (n + 1) α β) *
            shiftedJacobiMonic n α β := by
    linear_combination -hrec
  have hEig (k : ℕ) :
      jacobiDifferentialOperator (α + 1) (α + β + 2)
          (shiftedJacobiMonic k α β) =
        -C (eigenvalue (α + β + 2) k) * shiftedJacobiMonic k α β :=
    jacobiDifferentialOperator_shiftedJacobiMonic k α β
  have hLXP :
      jacobiDifferentialOperator (α + 1) (α + β + 2)
          (X * shiftedJacobiMonic (n + 1) α β) =
        -C (eigenvalue (α + β + 2) (n + 2)) *
            shiftedJacobiMonic (n + 2) α β +
          C (shiftedJacobiDiag (n + 1) α β) *
            (-C (eigenvalue (α + β + 2) (n + 1)) *
              shiftedJacobiMonic (n + 1) α β) +
          C (shiftedJacobiSubdiag (n + 1) α β) *
            (-C (eigenvalue (α + β + 2) n) *
              shiftedJacobiMonic n α β) := by
    rw [hrec]
    simp only [jacobiDifferentialOperator_add,
      jacobiDifferentialOperator_C_mul]
    rw [hEig (n + 2), hEig (n + 1), hEig n]
  have hXL :
      X * jacobiDifferentialOperator (α + 1) (α + β + 2)
          (shiftedJacobiMonic (n + 1) α β) =
        -C (eigenvalue (α + β + 2) (n + 1)) *
          (X * shiftedJacobiMonic (n + 1) α β) := by
    rw [hEig (n + 1)]
    ring
  have hcomm := jacobiDifferentialOperator_X_mul_sub_X_mul
    (α + 1) (α + β + 2) (shiftedJacobiMonic (n + 1) α β)
  rw [hLXP, hXL, hrec, hnext] at hcomm
  have hclear :
      C (2 : ℝ) *
          ((X : ℝ[X]) * (1 - X) * (shiftedJacobiMonic (n + 1) α β).derivative) =
        (-C (2 * ((n + 1 : ℕ) : ℝ)) * X +
          C ((2 * (n + 1) + (α + β + 2)) *
            shiftedJacobiDiag (n + 1) α β - (α + 1))) *
          shiftedJacobiMonic (n + 1) α β +
        C (2 * (2 * (n + 1) + (α + β + 2) - 1) *
          shiftedJacobiSubdiag (n + 1) α β) *
          shiftedJacobiMonic n α β := by
    unfold eigenvalue at hcomm
    norm_num [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul, map_neg,
      map_ofNat] at hcomm ⊢
    linear_combination -hcomm
  let A : ℝ := ((2 * (n + 1) + (α + β + 2)) *
    shiftedJacobiDiag (n + 1) α β - (α + 1)) / 2
  let B : ℝ := (2 * (n + 1) + (α + β + 2) - 1) *
    shiftedJacobiSubdiag (n + 1) α β
  change (X : ℝ[X]) * (1 - X) * (shiftedJacobiMonic (n + 1) α β).derivative =
    (-C ((n + 1 : ℕ) : ℝ) * X + C A) * shiftedJacobiMonic (n + 1) α β +
      C B * shiftedJacobiMonic n α β
  have htwo : (C (2 : ℝ) : ℝ[X]) ≠ 0 := by norm_num
  apply (mul_left_cancel₀ htwo)
  have hA : C (2 : ℝ) * C A =
      C ((2 * (n + 1) + (α + β + 2)) *
        shiftedJacobiDiag (n + 1) α β - (α + 1)) := by
    rw [← C_mul]
    dsimp only [A]
    congr 1
    ring
  have hB : C (2 : ℝ) * C B =
      C (2 * (2 * (n + 1) + (α + β + 2) - 1) *
        shiftedJacobiSubdiag (n + 1) α β) := by
    rw [← C_mul]
    dsimp only [B]
    congr 1
    ring
  have hscale :
      C (2 : ℝ) *
          ((-C ((n + 1 : ℕ) : ℝ) * X + C A) * shiftedJacobiMonic (n + 1) α β +
            C B * shiftedJacobiMonic n α β) =
        (-C (2 * ((n + 1 : ℕ) : ℝ)) * X +
          C ((2 * (n + 1) + (α + β + 2)) *
            shiftedJacobiDiag (n + 1) α β - (α + 1))) *
          shiftedJacobiMonic (n + 1) α β +
        C (2 * (2 * (n + 1) + (α + β + 2) - 1) *
          shiftedJacobiSubdiag (n + 1) α β) *
          shiftedJacobiMonic n α β := by
    have hN : C (2 : ℝ) * C ((n + 1 : ℕ) : ℝ) =
        C (2 * ((n + 1 : ℕ) : ℝ)) := by
      rw [← C_mul]
    calc
      _ = (C (2 : ℝ) * (-C ((n + 1 : ℕ) : ℝ) * X + C A)) *
            shiftedJacobiMonic (n + 1) α β +
          (C (2 : ℝ) * C B) * shiftedJacobiMonic n α β := by ring
      _ = (-C (2 * ((n + 1 : ℕ) : ℝ)) * X +
            C ((2 * (n + 1) + (α + β + 2)) *
              shiftedJacobiDiag (n + 1) α β - (α + 1))) *
            shiftedJacobiMonic (n + 1) α β +
          C (2 * (2 * (n + 1) + (α + β + 2) - 1) *
            shiftedJacobiSubdiag (n + 1) α β) *
            shiftedJacobiMonic n α β := by
        rw [show C (2 : ℝ) * (-C ((n + 1 : ℕ) : ℝ) * X + C A) =
            -C (2 * ((n + 1 : ℕ) : ℝ)) * X +
              C ((2 * (n + 1) + (α + β + 2)) *
                shiftedJacobiDiag (n + 1) α β - (α + 1)) by
          calc
            C (2 : ℝ) * (-C ((n + 1 : ℕ) : ℝ) * X + C A) =
                -(C (2 : ℝ) * C ((n + 1 : ℕ) : ℝ)) * X +
                  C (2 : ℝ) * C A := by
              ring
            _ = _ := by rw [hN, hA], hB]
  rw [hscale]
  exact hclear

/-- The lower coefficient in `shiftedJacobiMonic_lowering_succ` is positive.
This includes degree one, with no restriction such as `α + β + 1 ≠ 0`. -/
theorem shiftedJacobiMonic_lowering_succ_subdiag_pos (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    0 < (2 * (n + 1) + (α + β + 2) - 1) *
      shiftedJacobiSubdiag (n + 1) α β := by
  apply mul_pos
  · have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · exact shiftedJacobiSubdiag_pos (n + 1) (by lia) hα hβ

/-- The same-parameter lowering identity, indexed by an arbitrary nonzero
degree. -/
theorem shiftedJacobiMonic_lowering (n : ℕ) {α β : ℝ}
    (hn : n ≠ 0) (hα : -1 < α) (hβ : -1 < β) :
    (X : ℝ[X]) * (1 - X) * (shiftedJacobiMonic n α β).derivative =
      (-C (n : ℝ) * X +
          C (((2 * n + (α + β + 2)) * shiftedJacobiDiag n α β -
            (α + 1)) / 2)) *
          shiftedJacobiMonic n α β +
        C ((2 * n + (α + β + 2) - 1) * shiftedJacobiSubdiag n α β) *
          shiftedJacobiMonic (n - 1) α β := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ m =>
      convert shiftedJacobiMonic_lowering_succ m hα hβ using 1;
        norm_num [Nat.cast_succ]

/-- The lower coefficient in `shiftedJacobiMonic_lowering` is positive. -/
theorem shiftedJacobiMonic_lowering_subdiag_pos (n : ℕ) {α β : ℝ}
    (hn : n ≠ 0) (hα : -1 < α) (hβ : -1 < β) :
    0 < (2 * n + (α + β + 2) - 1) * shiftedJacobiSubdiag n α β := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ m =>
      norm_num [Nat.cast_succ]
      exact shiftedJacobiMonic_lowering_succ_subdiag_pos m hα hβ

end RealRooted.JacobiDeformation
