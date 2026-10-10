import RealRooted.AffineFamily.Basic
import RealRooted.Wagner.LeftSum

/-!
# Lag recurrences with a feedback term

Rows of `P (n + p) = α P (n + p - 1) + c n X P n` with `α > 0` and `c n > 0`, such as
`P (n + 3) = P (n + 2) + 3 X P n` (A317496), keep their windows `(P n, …, P (n + p - 1))`
pairwise interlacing (`strictInterl_of_lagFeedback`).  For `0 < i < p`, `P (n + i)` precedes
`P (n + p - 1)` and, since `P n` precedes `P (n + i)`, also `X P n`; a common left
interleaver passes to the sum `P (n + p)` (`StrictInterl.add_of_left`).  This is the
transition matrix of Brändén's criterion (shift rows and one feedback row
`(c n X, 0, …, 0, α)`) argued directly.

The rows have no three-term recurrence: their degrees grow by one every `p` steps.
-/

open Polynomial

namespace RealRooted

private lemma hasPosLeadingCoeff_of_nonneg {f : ℝ[X]} (hf : HasNonnegCoeffs f) (h0 : f ≠ 0) :
    HasPosLeadingCoeff f :=
  lt_of_le_of_ne (hf _) (leadingCoeff_ne_zero.mpr h0).symm

/-- Windows of a lag recurrence with a feedback term stay pairwise interlacing. -/
theorem strictInterl_of_lagFeedback {P : ℕ → ℝ[X]} {p : ℕ} {α : ℝ} {c : ℕ → ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hc : ∀ n, 0 < c n)
    (hrec : ∀ n, P (n + p) = C α * P (n + (p - 1)) + C (c n) * X * P n)
    (h0 : ∀ i j, i < j → j < p → StrictInterl (P i) (P j))
    (hnn0 : ∀ i, i < p → HasNonnegCoeffs (P i)) :
    ∀ n i j, i < j → j < p → StrictInterl (P (n + i)) (P (n + j)) := by
  have key : ∀ n, (∀ i j, i < j → j < p → StrictInterl (P (n + i)) (P (n + j))) ∧
      ∀ i, i < p → HasNonnegCoeffs (P (n + i)) := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using h0, by simpa using hnn0⟩
    | succ n ih =>
      obtain ⟨hI, hN⟩ := ih
      have hPn0 : P n ≠ 0 := (hI 0 1 (by lia) (by lia)).1.1
      have hNn : HasNonnegCoeffs (P n) := by simpa using hN 0 (by lia)
      have hlast : HasNonnegCoeffs (P (n + p)) := by
        rw [hrec n]
        exact (nonnegCoeffs_C_mul hα.le (hN (p - 1) (by lia))).add
          ((nonnegCoeffs_C_mul (hc n).le hasNonnegCoeffs_X).mul hNn)
      -- the new pairs `P (n + 1 + i) ≺ P (n + p)`
      have hnew : ∀ i, i + 1 < p → StrictInterl (P (n + (i + 1))) (P (n + p)) := by
        intro i hi
        have hA : HasNonnegCoeffs (P (n + (i + 1))) := hN (i + 1) hi
        have h1 : StrictInterl (P (n + (i + 1))) (P (n + (p - 1))) := by
          rcases Nat.lt_or_ge (i + 1) (p - 1) with h | h
          · exact hI (i + 1) (p - 1) h (by lia)
          · rw [show i + 1 = p - 1 by lia]
            have hs := hI 0 (p - 1) (by lia) (by lia)
            exact StrictInterl.refl hs.2.1.1 hs.2.1.2
        have h2 : StrictInterl (P (n + (i + 1))) (X * P n) :=
          strictInterl_to_strictInterl_mul_X_of_nonneg (by simpa using hI 0 (i + 1) (by lia) hi)
            hNn hA
        have hf := h1.C_mul_right hα.ne'
        have hg := h2.C_mul_right (hc n).ne'
        rw [hrec n, mul_assoc (C (c n))]
        exact hf.add_of_left hg
          (hasPosLeadingCoeff_of_nonneg (nonnegCoeffs_C_mul hα.le (hN (p - 1) (by lia)))
            hf.2.1.1)
          (hasPosLeadingCoeff_of_nonneg
            ((nonnegCoeffs_C_mul (hc n).le (hasNonnegCoeffs_X.mul hNn))) hg.2.1.1)
      refine ⟨fun i j hij hj => ?_, fun i hi => ?_⟩
      · rcases Nat.lt_or_ge (j + 1) p with h | h
        · rw [show n + 1 + i = n + (i + 1) by lia, show n + 1 + j = n + (j + 1) by lia]
          exact hI (i + 1) (j + 1) (by lia) h
        · rw [show n + 1 + i = n + (i + 1) by lia, show n + 1 + j = n + p by lia]
          exact hnew i (by lia)
      · rcases Nat.lt_or_ge (i + 1) p with h | h
        · rw [show n + 1 + i = n + (i + 1) by lia]
          exact hN (i + 1) h
        · rw [show n + 1 + i = n + p by lia]
          exact hlast
  exact fun n => (key n).1

/-- Rows of a lag recurrence with a feedback term split, from positive constant first rows. -/
theorem splits_of_lagFeedback {P : ℕ → ℝ[X]} {p : ℕ} {α : ℝ} {c : ℕ → ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hc : ∀ n, 0 < c n)
    (hrec : ∀ n, P (n + p) = C α * P (n + (p - 1)) + C (c n) * X * P n)
    (h0 : ∀ i, i < p → ∃ a : ℝ, 0 < a ∧ P i = C a) (n : ℕ) : (P n).Splits := by
  have hI := strictInterl_of_lagFeedback hp hα hc hrec (fun i j _ hj => ?_)
    (fun i hi => ?_) n 0 1 (by lia) (by lia)
  · exact hI.1.2
  · obtain ⟨a, ha, hPi⟩ := h0 i (by lia)
    obtain ⟨b, hb, hPj⟩ := h0 j hj
    rw [hPi, hPj, show C a = C (a / b) * C b by rw [← C_mul, div_mul_cancel₀ _ hb.ne']]
    exact (StrictInterl.refl (C_ne_zero.mpr hb.ne') (Splits.C b)).C_mul_left
      (div_ne_zero ha.ne' hb.ne')
  · obtain ⟨a, ha, hPi⟩ := h0 i hi
    rw [hPi]
    exact hasNonnegCoeffs_C ha.le

end RealRooted
