module

public import RealRooted.LiuWang.FiniteFamily

/-!
# Derivative--lag recurrences with common roots

This file packages the repeated-root-safe finite-family Liu--Wang step as a
sequence induction.  Unlike the strict negative-root route, it allows a root
at zero to persist through every row.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Adjacent rows of a derivative--lag recurrence strictly interlace when the
derivative and lag multipliers are nonpositive at every nonpositive real
number.  Common roots of adjacent rows are allowed. -/
theorem derivativeLag_strictInterl_of_nonnegCoeffs_of_step
    {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) =
      U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hnn : ∀ n, HasNonnegCoeffs (P n))
    (hV : ∀ n x, x ≤ 0 → (V n).eval x ≤ 0)
    (hW : ∀ n x, x ≤ 0 → (W n).eval x ≤ 0)
    (hbase : StrictInterl (P 0) (P 1)) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hroot : ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 := by
        intro r hr
        exact isRoot_nonpos_of_hasNonnegCoeffs
          (hnn (n + 1)) (hpos (n + 1)).ne_zero hr
      have hF_pos : HasPosLeadingCoeff
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n) := by
        rw [← hrec n]
        exact hpos (n + 2)
      have hdeg_lo : (P (n + 1)).natDegree ≤
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n).natDegree := by
        rw [← hrec n]
        rcases hstep (n + 1) with hsame | hsucc <;> lia
      have hdeg_hi :
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n).natDegree ≤
            (P (n + 1)).natDegree + 1 := by
        rw [← hrec n]
        rcases hstep (n + 1) with hsame | hsucc <;> lia
      have hnext := LiuWang.strictInterl_derivative_lag_of_eval_nonpos
        (hpos (n + 1)).ne_zero ih.2.1.2 (hpos (n + 1)) ih (hpos n) hF_pos
        hdeg_lo hdeg_hi (fun r hr ↦ hV n r (hroot r hr))
        (fun r hr ↦ hW n r (hroot r hr))
      rw [← hrec n] at hnext
      exact hnext

/-- A derivative-free affine lag can be translated to a nonnegative `X`-lag.  It is enough
to check coefficientwise nonnegativity of the two translated base rows; the translated
recurrence propagates it. -/
theorem derivativeLag_strictInterl_of_affine_lag_of_base_nonneg
    {P : Nat → ℝ[X]} {a c : Nat → ℝ} {r : ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hzero : HasNonnegCoeffs ((P 0).comp (X + C r)))
    (hone : HasNonnegCoeffs ((P 1).comp (X + C r)))
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (ha : ∀ n, 0 < a n) (hc : ∀ n, 0 ≤ c n)
    (hrec : ∀ n,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n) :
    ∀ n, StrictInterl (P n) (P (n + 1)) := by
  let Q : Nat → ℝ[X] := fun n => (P n).comp (X + C r)
  have hQrec : ∀ n, Q (n + 2) =
      C (a n) * Q (n + 1) + 0 * (Q (n + 1)).derivative + (C (c n) * X) * Q n := by
    intro n
    have h := congrArg (fun p : ℝ[X] => p.comp (X + C r)) (hrec n)
    simpa [Q, add_comp, mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
      add_assoc] using h
  have hQnonneg : ∀ n, HasNonnegCoeffs (Q n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simpa [Q] using hzero
    | one => simpa [Q] using hone
    | more n hn hn1 =>
        rw [hQrec n]
        simpa using ((hasNonnegCoeffs_C (ha n).le).mul hn1).add
          (((hasNonnegCoeffs_C (hc n)).mul hasNonnegCoeffs_X).mul hn)
  have hQbase : StrictInterl (Q 0) (Q 1) := by
    simpa [Q] using (StrictInterl.comp_X_add_C_iff (f := P 0) (g := P 1) r).2 hbase
  have hQstep : ∀ n, (Q (n + 1)).natDegree = (Q n).natDegree ∨
      (Q (n + 1)).natDegree = (Q n).natDegree + 1 := by
    intro n
    simpa [Q, natDegree_comp, natDegree_X_add_C] using hstep n
  have hQpos : ∀ n, HasPosLeadingCoeff (Q n) := fun n => by
    simpa [Q] using (hpos n).comp_X_add_C r
  have hQstrict := derivativeLag_strictInterl_of_nonnegCoeffs_of_step hQrec hQstep hQpos
    hQnonneg (by simp) (by
      intro n x hx
      simp only [eval_mul, eval_C, eval_X]
      exact mul_nonpos_of_nonneg_of_nonpos (hc n) hx) hQbase
  intro n
  exact (StrictInterl.comp_X_add_C_iff (f := P n) (g := P (n + 1)) r).1 (hQstrict n)

end RealRooted
