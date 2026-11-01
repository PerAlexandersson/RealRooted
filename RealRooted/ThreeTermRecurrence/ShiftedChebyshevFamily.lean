module

public import RealRooted.Favard
public import RealRooted.Interlacing.Reversal
public import RealRooted.SimpleRoots
import RealRooted.DegreeDropReversal

/-!
# Shifted Chebyshev families with a perturbed first row

This file packages the constant negative-lag recurrence from issues #2290 and
#2294 as a Favard family, then identifies its coefficient reflection with the
quadratic-lag recurrence.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The monic recurrence with center `d`, lag `-b ^ 2`, and a perturbation `c`
in its first row. -/
@[expose] def constantLagFamily (b d c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + C (d + c)
  | n + 2 => (X + C d) * constantLagFamily b d c (n + 1) -
      C (b ^ 2) * constantLagFamily b d c n

/-- The zeroth row of the constant-lag family. -/
@[simp] theorem constantLagFamily_zero (b d c : ℝ) :
    constantLagFamily b d c 0 = 1 := rfl

/-- The first row of the constant-lag family. -/
@[simp] theorem constantLagFamily_one (b d c : ℝ) :
    constantLagFamily b d c 1 = X + C (d + c) := rfl

/-- The defining recurrence of the constant-lag family. -/
theorem constantLagFamily_add_two (b d c : ℝ) (n : ℕ) :
    constantLagFamily b d c (n + 2) =
      (X + C d) * constantLagFamily b d c (n + 1) -
        C (b ^ 2) * constantLagFamily b d c n := rfl

/-- A polynomial sequence with the same two seeds and recurrence is the
constant-lag family. -/
theorem eq_constantLagFamily_of_recurrence
    {P : ℕ → ℝ[X]} (b d c : ℝ)
    (hzero : P 0 = 1) (hone : P 1 = X + C (d + c))
    (hrec : ∀ n, P (n + 2) =
      (X + C d) * P (n + 1) - C (b ^ 2) * P n) :
    ∀ n, P n = constantLagFamily b d c n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => simpa using hone
  | more n ih ih_succ =>
      rw [hrec n, constantLagFamily_add_two, ih, ih_succ]

private def constantLagDiagonal (d c : ℝ) : ℕ → ℝ
  | 0 => -(d + c)
  | _ + 1 => -d

private def constantLagSubdiag (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | _ + 1 => b ^ 2

private theorem constantLagFamily_satisfiesFavardRecurrence (b d c : ℝ) :
    SatisfiesFavardRecurrence (constantLagFamily b d c)
      (constantLagDiagonal d c) (constantLagSubdiag b) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [constantLagFamily, constantLagDiagonal]
    ring
  · intro n
    simp [constantLagFamily_add_two, constantLagDiagonal, constantLagSubdiag]

/-- Every constant-lag row is monic of degree equal to its index. -/
theorem constantLagFamily_isMonicOfDegree (b d c : ℝ) (n : ℕ) :
    (constantLagFamily b d c n).IsMonicOfDegree n :=
  (constantLagFamily_satisfiesFavardRecurrence b d c).isMonicOfDegree n

/-- A nonzero lag gives interlacing of every pair of consecutive rows. -/
theorem constantLagFamily_strictInterl {b : ℝ} (hb : b ≠ 0) (d c : ℝ) (n : ℕ) :
    StrictInterl (constantLagFamily b d c n) (constantLagFamily b d c (n + 1)) := by
  apply favardInterlacing (constantLagFamily_satisfiesFavardRecurrence b d c)
  intro m
  simp [constantLagSubdiag, sq_pos_of_ne_zero hb]

/-- A nonzero lag gives simple real roots in every row. -/
theorem constantLagFamily_hasSimpleRoots {b : ℝ} (hb : b ≠ 0) (d c : ℝ) (n : ℕ) :
    HasSimpleRoots (constantLagFamily b d c n) := by
  intro r hr
  apply rootMultiplicity_eq_one_of_favard
    (constantLagFamily_satisfiesFavardRecurrence b d c) _ n hr
  intro m
  simp [constantLagSubdiag, sq_pos_of_ne_zero hb]

/-- The specialization with center two and unit lag from issue #2290. -/
@[expose] def shiftedChebyshevFamily (c : ℝ) (n : ℕ) : ℝ[X] :=
  constantLagFamily 1 2 c n

/-- The value at zero of the shifted unit-lag family. -/
theorem shiftedChebyshevFamily_eval_zero (c : ℝ) : ∀ n : ℕ,
    (shiftedChebyshevFamily c n).eval 0 = n + 1 + n * c
  | 0 => by simp [shiftedChebyshevFamily]
  | 1 => by
      simp [shiftedChebyshevFamily]
      ring
  | n + 2 => by
      rw [shiftedChebyshevFamily, constantLagFamily_add_two]
      simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C, zero_add, one_pow]
      have ih₁ := shiftedChebyshevFamily_eval_zero c (n + 1)
      have ih₀ := shiftedChebyshevFamily_eval_zero c n
      simp only [shiftedChebyshevFamily] at ih₁ ih₀
      rw [ih₁, ih₀]
      simp only [one_mul]
      push_cast
      ring

/-- The reflected recurrence from issue #2294. -/
@[expose] def reflectedShiftedChebyshevFamily (c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + C (2 + c) * X
  | n + 2 => (1 + C 2 * X) * reflectedShiftedChebyshevFamily c (n + 1) -
      X ^ 2 * reflectedShiftedChebyshevFamily c n

private theorem reflect_one_one_add_two_mul_X :
    reflect 1 (1 + C 2 * X : ℝ[X]) = X + C 2 := by
  rw [show (1 + C 2 * X : ℝ[X]) = C 1 * X ^ 0 + C 2 * X ^ 1 by simp,
    Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  norm_num [Polynomial.revAt_le]

private theorem reflect_two_neg_X_sq :
    reflect 2 (-X ^ 2 : ℝ[X]) = -1 := by
  rw [Polynomial.reflect_neg, show (X ^ 2 : ℝ[X]) = C 1 * X ^ 2 by simp,
    Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le (by lia)]
  simp

private theorem reflect_one_X_add_C (a : ℝ) :
    reflect 1 (X + C a : ℝ[X]) = 1 + C a * X := by
  rw [show (X + C a : ℝ[X]) = C 1 * X ^ 1 + C a * X ^ 0 by simp,
    Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  norm_num [Polynomial.revAt_le]

/-- The reflected recurrence is coefficient reversal of the shifted unit-lag family. -/
theorem reflectedShiftedChebyshevFamily_eq_reflect (c : ℝ) (n : ℕ) :
    reflectedShiftedChebyshevFamily c n =
      reflect n (shiftedChebyshevFamily c n) := by
  have hall : ∀ m, reflectedShiftedChebyshevFamily c m =
      reflect (0 + m) (shiftedChebyshevFamily c m) := by
    apply eq_reflect_of_threeTerm
      (P := reflectedShiftedChebyshevFamily c) (R := shiftedChebyshevFamily c)
      (a := fun _ ↦ 1 + C 2 * X) (b := fun _ ↦ -X ^ 2)
      (a' := fun _ ↦ X + C 2) (b' := fun _ ↦ -1) (D₀ := 0)
    · intro m
      simp [reflectedShiftedChebyshevFamily]
      ring
    · intro m
      simp [shiftedChebyshevFamily, constantLagFamily_add_two]
      ring
    · intro m
      simp
    · intro m
      simp
    · intro m
      exact reflect_one_one_add_two_mul_X.symm
    · intro m
      exact reflect_two_neg_X_sq.symm
    · intro m
      simpa [shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 c m).natDegree_eq.le
    · simp [reflectedShiftedChebyshevFamily, shiftedChebyshevFamily]
    · simpa [reflectedShiftedChebyshevFamily, shiftedChebyshevFamily] using
        (reflect_one_X_add_C (2 + c)).symm
  simpa using hall n

/-- Every reflected row has constant coefficient one. -/
theorem reflectedShiftedChebyshevFamily_coeff_zero (c : ℝ) (n : ℕ) :
    (reflectedShiftedChebyshevFamily c n).coeff 0 = 1 := by
  rw [reflectedShiftedChebyshevFamily_eq_reflect, coeff_reflect]
  have hmono := constantLagFamily_isMonicOfDegree 1 2 c n
  rw [Polynomial.revAt_le (Nat.zero_le n)]
  simpa [shiftedChebyshevFamily, hmono.natDegree_eq] using
    hmono.monic.coeff_natDegree

/-- Away from the unique cancellation parameter, a reflected row has full degree. -/
theorem reflectedShiftedChebyshevFamily_natDegree_eq_of_ne
    (c : ℝ) (n : ℕ) (h : n + 1 + n * c ≠ 0) :
    (reflectedShiftedChebyshevFamily c n).natDegree = n := by
  rw [reflectedShiftedChebyshevFamily_eq_reflect]
  apply DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne
  · exact (constantLagFamily_isMonicOfDegree 1 2 c n).natDegree_eq.le
  · rw [coeff_zero_eq_eval_zero, shiftedChebyshevFamily_eval_zero]
    exact h

/-- At the exceptional parameter, a positive-index reflected row loses exactly
one degree. -/
theorem reflectedShiftedChebyshevFamily_natDegree_eq_sub_one
    (c : ℝ) (n : ℕ) (hn : 0 < n) (h : n + 1 + n * c = 0) :
    (reflectedShiftedChebyshevFamily c n).natDegree = n - 1 := by
  let p := shiftedChebyshevFamily c n
  have hpdeg : p.natDegree = n := by
    simpa [p, shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 c n).natDegree_eq
  have hproot : p.IsRoot 0 := by
    change (shiftedChebyshevFamily c n).IsRoot 0
    rw [Polynomial.IsRoot.def, shiftedChebyshevFamily_eval_zero]
    exact h
  have hpsimple : HasSimpleRoots p := by
    simpa [p, shiftedChebyshevFamily] using
      constantLagFamily_hasSimpleRoots (b := 1) one_ne_zero 2 c n
  have hpcoeff_one : p.coeff 1 ≠ 0 := by
    have hder := hpsimple.eval_derivative_ne_zero hproot
    rw [← coeff_zero_eq_eval_zero] at hder
    simpa [coeff_derivative] using hder
  rw [reflectedShiftedChebyshevFamily_eq_reflect]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_reflect]
    by_cases hkn : k ≤ n
    · rw [revAt_le hkn]
      have hnk : n - k = 0 := by lia
      rw [hnk, coeff_zero_eq_eval_zero]
      change (shiftedChebyshevFamily c n).eval 0 = 0
      rw [shiftedChebyshevFamily_eval_zero, h]
    · rw [revAt_eq_self_of_lt (by lia)]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpdeg]
      lia
  · rw [coeff_reflect, revAt_le (by lia)]
    have hsub : n - (n - 1) = 1 := by lia
    simpa [hsub] using hpcoeff_one

/-- Every reflected row is real-rooted, including at the degree-cancellation
parameter. -/
theorem reflectedShiftedChebyshevFamily_splits (c : ℝ) (n : ℕ) :
    (reflectedShiftedChebyshevFamily c n).Splits := by
  rw [reflectedShiftedChebyshevFamily_eq_reflect]
  apply Polynomial.Splits.reflect
  · exact (constantLagFamily_strictInterl (b := 1) one_ne_zero 2 c n).1.2
  · simpa [shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 c n).natDegree_eq.le

end RealRooted
