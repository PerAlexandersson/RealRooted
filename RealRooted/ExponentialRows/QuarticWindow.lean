module

public import RealRooted.ExponentialRows.ProductInsertion
import RealRooted.ExponentialRows.QuarticCoefficients
import RealRooted.ExponentialRows.QuarticRecurrence
import RealRooted.PosCombo
import RealRooted.WagnerRightSum.Sign
import RealRooted.ExponentialRows.ProductStrict
import RealRooted.Derivative.Interlacing
import Mathlib.Tactic

/-!
# From adjacent quartic alternation to a three-row window

We formalize the distance-two induction in Section 2 of the unpublished manuscript
discussed in RealRooted #2415 (round two) and #2649:
https://github.com/PerAlexandersson/RealRooted/issues/2649.

This is an implication, not a proof of adjacent strictness in the completed-square
region. Its adjacent hypotheses are explicit. Wagner's cone theorem supplies the
weak distance-two comparison. At a root of the pivot, the nonzero adjacent row
prevents cancellation among the remaining summands and makes that comparison strict.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- The four-term recurrence closes the weak distance-two comparison at a pivot. -/
private theorem quartic_add_two_step {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ)
    (hnext : StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2))
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 3)))
    (hprev : StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 1))
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)))
    (hold : StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n)
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2))) :
    StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2))
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 4)) := by
  let R := insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4))
  have hnn := hasNonnegCoeffs_insertionRow_quartic ha hb hc
  have hs := strictInterl_self_X_mul_of_nonneg hnext.1.1 hnext.1.2 (hnn (n + 2))
  have hp := strictInterl_mul_X_of_strictInterl_of_nonneg hprev (hnn (n + 1)) (hnn (n + 2))
  have ho := strictInterl_mul_X_of_strictInterl_of_nonneg hold (hnn n) (hnn (n + 2))
  have h := Interl.sum_left_of_common_left_of_nonneg
    [R (n + 3), C (2 * a * (n + 3)) * (X * R (n + 2)),
      C (3 * b * (n + 3) * (n + 2)) * (X * R (n + 1)),
      C (4 * c * (n + 3) * (n + 2) * (n + 1)) * (X * R n)] (R (n + 2)) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl
      · exact hnext.toInterl
      · exact hs.toInterl.C_mul_right_of_nonneg (by positivity)
      · exact hp.toInterl.C_mul_right_of_nonneg (by positivity)
      · exact ho.toInterl.C_mul_right_of_nonneg (by positivity)) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl
      · exact hnn (n + 3)
      · exact hasNonnegCoeffs_C_mul (by positivity) (hnn (n + 2)).X_mul
      · exact hasNonnegCoeffs_C_mul (by positivity) (hnn (n + 1)).X_mul
      · exact hasNonnegCoeffs_C_mul (by positivity) (hnn n).X_mul)
  simp only [List.sum_cons, List.sum_nil, add_zero] at h
  have hrec := insertionRow_quartic_add_four a b c n
  change R (n + 4) = _ at hrec
  rw [← add_assoc, ← add_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← hrec] at h
  exact h.toStrictInterl_of_ne hnext.1.1 (by
    intro hz
    have h0 := insertionRow_quartic_coeff_zero a b c (n + 4)
    change (R (n + 4)).coeff 0 = 1 at h0
    simp [hz] at h0)

/-- At a pivot root, the nonzero adjacent summand prevents cancellation. -/
private theorem quartic_add_two_no_common_root {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ)
    (hnext : StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2))
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 3)))
    (hprev : StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 1))
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)))
    (hold : StrictInterl
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n)
      (insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)))
    (hno : ∀ x, ¬ ((insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)).IsRoot x ∧
      (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 3)).IsRoot x)) :
    ∀ x, ¬ ((insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)).IsRoot x ∧
      (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 4)).IsRoot x) := by
  let R := insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4))
  have hnn := hasNonnegCoeffs_insertionRow_quartic ha hb hc
  have href := strictInterl_mul_X_of_strictInterl_of_nonneg hnext (hnn (n + 2)) (hnn (n + 3))
  have h₀ := hold.toInterl.mul_X_both
  have h₁ := hprev.toInterl.mul_X_both
  intro x hx
  have hxzero : (R (n + 2)).eval x = 0 := hx.1.eq_zero
  have hx' : (X * R (n + 2)).IsRoot x := by simp [IsRoot.def, hxzero]
  have hne : (R (n + 3)).eval x ≠ 0 := fun hz => hno x ⟨hx.1, hz⟩
  have hright := (hnn (n + 3)).pos_leadingCoeff hnext.2.1.1
  have hsign₀ : 0 ≤ (X * R n).eval x * (R (n + 3)).eval x := by
    exact eval_mul_eval_nonneg_of_strictInterl_right
      (h₀.toStrictInterl_of_ne (mul_ne_zero X_ne_zero hold.1.1)
        (mul_ne_zero X_ne_zero hold.2.1.1)) href
      ((hnn n).X_mul.pos_leadingCoeff (mul_ne_zero X_ne_zero hold.1.1)) hright hx'
  have hsign₁ : 0 ≤ (X * R (n + 1)).eval x * (R (n + 3)).eval x := by
    exact eval_mul_eval_nonneg_of_strictInterl_right
      (h₁.toStrictInterl_of_ne (mul_ne_zero X_ne_zero hprev.1.1)
        (mul_ne_zero X_ne_zero hprev.2.1.1)) href
      ((hnn (n + 1)).X_mul.pos_leadingCoeff (mul_ne_zero X_ne_zero hprev.1.1)) hright hx'
  have hpos := mul_self_pos.mpr hne
  have heq := hx.2.eq_zero
  rw [insertionRow_quartic_add_four] at heq
  change (R (n + 3) + C (2 * a * (n + 3)) * X * R (n + 2) +
    C (3 * b * (n + 3) * (n + 2)) * X * R (n + 1) +
    C (4 * c * (n + 3) * (n + 2) * (n + 1)) * X * R n).eval x = 0 at heq
  simp only [eval_add, eval_mul, eval_C, eval_X, hxzero, mul_zero, add_zero] at heq
  have hsum := congrArg (fun y : ℝ => y * (R (n + 3)).eval x) heq
  have hterm₀ := mul_nonneg
    (show 0 ≤ 4 * c * (n + 3 : ℝ) * (n + 2) * (n + 1) by positivity) hsign₀
  have hterm₁ := mul_nonneg
    (show 0 ≤ 3 * b * (n + 3 : ℝ) * (n + 2) by positivity) hsign₁
  simp only [eval_mul, eval_X] at hterm₀ hterm₁
  nlinarith only [hsum, hpos, hterm₀, hterm₁]

/-- Genuine strict adjacency implies genuine strict distance-two alternation for
quartic rows. The adjacent hypothesis is the remaining target in the square region. -/
theorem insertionRow_strictInterl_quartic_add_two_of_succ {a b c : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsucc : ∀ n,
      StrictInterl (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n)
        (insertionRow (markedBlockWeights
          (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 1)) ∧
      ∀ x, ¬ ((insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).IsRoot x ∧
        (insertionRow (markedBlockWeights
          (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 1)).IsRoot x)) (n : ℕ) :
    StrictInterl (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n)
      (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)) ∧
    ∀ x, ¬ ((insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).IsRoot x ∧
      (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)).IsRoot x) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | n
    · refine ⟨?_, by simp⟩
      exact StrictInterl.of_degree_zero_right_of_degree_one
        (hsucc 0).1.1.1 (hsucc 0).1.1.2 (hsucc 2).1.1.1 (hsucc 2).1.1.2 (by simp)
        (by simpa using natDegree_insertionRow_quartic ha hb hc 2)
    · refine ⟨?_, ?_⟩
      · exact StrictInterl.of_degree_zero_right_of_degree_one
          (hsucc 1).1.1.1 (hsucc 1).1.1.2 (hsucc 3).1.1.1 (hsucc 3).1.1.2
          (by simpa using natDegree_insertionRow_quartic ha hb hc 1)
          (by simpa using natDegree_insertionRow_quartic ha hb hc 3)
      · intro x hx
        have h0 := hx.1.eq_zero
        norm_num [insertionRow_succ, Finset.sum_range_succ] at h0
    · have hold := (ih n (by lia)).1
      exact ⟨quartic_add_two_step ha.le hb hc n (hsucc (n + 2)).1 (hsucc (n + 1)).1 hold,
        quartic_add_two_no_common_root ha.le hb hc n (hsucc (n + 2)).1
          (hsucc (n + 1)).1 hold (hsucc (n + 2)).2⟩

/-- Cubic exponential rows with positive pair weight also strictly alternate at
distance two. In particular every three consecutive cap-two rows form a strict window. -/
theorem insertionRow_strictInterl_cubic_add_two {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3)
    StrictInterl (insertionRow w n) (insertionRow w (n + 2)) ∧
      ∀ x, ¬ ((insertionRow w n).IsRoot x ∧ (insertionRow w (n + 2)).IsRoot x) := by
  have hsucc : ∀ j,
      StrictInterl (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C (0 : ℝ) * X ^ 4)) j)
        (insertionRow (markedBlockWeights
          (C a * X ^ 2 + C b * X ^ 3 + C (0 : ℝ) * X ^ 4)) (j + 1)) ∧
      ∀ x, ¬ ((insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C (0 : ℝ) * X ^ 4)) j).IsRoot x ∧
        (insertionRow (markedBlockWeights
          (C a * X ^ 2 + C b * X ^ 3 + C (0 : ℝ) * X ^ 4)) (j + 1)).IsRoot x) := by
    intro j
    simpa using insertionRow_strictInterl_cubic ha hb j
  simpa using insertionRow_strictInterl_quartic_add_two_of_succ ha hb le_rfl hsucc n

end RealRooted.ExponentialRows
