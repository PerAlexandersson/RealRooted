module

public import RealRooted.EulerBidiagonal.Basic
import RealRooted.MaWang.Strong
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
import RealRooted.DerivativeRecurrence.Interlacing
import RealRooted.Wronskian.Forward

/-!
# Euler bidiagonal rows with varying parameters

Positive parameters with nondecreasing sum give negative-simple rows of degree equal to
their index, with consecutive rows interlacing without common roots. At an input root `r`,
changing the parameters adds only `δ r p'(r)` to the step value, where `δ ≥ 0` is the
increment in their sum. No condition on the products of the parameters is needed.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- The difference of two Euler steps is a linear combination of `theta p` and `p`. -/
theorem step_sub_step (a b c d : ℝ) (p : ℝ[X]) :
    step c d p - step a b p =
      C (c + d - (a + b)) * theta p + C (c * d - a * b) * p := by
  simp only [step, C_sub, C_add]
  ring

/-- Rows of the Euler bidiagonal recurrence with index-dependent parameters. -/
def rowsVar (a b : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => step (a n) (b n) (rowsVar a b n)

/-- Every varying-parameter row is negative-simple. -/
theorem isNegativeSimple_rowsVar {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, 0 < a n * b n) :
    ∀ n, IsNegativeSimple (rowsVar a b n) := by
  intro n
  induction n with
  | zero => exact isNegativeSimple_one
  | succ n ih => exact (mapsNegativeSimpleBySucc_step (ha n) (hb n) (hab n) ih).1

/-- Every varying-parameter row has degree equal to its index. -/
theorem natDegree_rowsVar {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, 0 < a n * b n) :
    ∀ n, (rowsVar a b n).natDegree = n := by
  intro n
  induction n with
  | zero => simp [rowsVar]
  | succ n ih =>
      have hd := (mapsNegativeSimpleBySucc_step (ha n) (hb n) (hab n)
        (isNegativeSimple_rowsVar ha hb hab n)).2
      simpa only [stepLinearMap_apply, rowsVar, ih] using hd

/-- Increasing the parameter sum keeps the strict critical sign at input roots. -/
private theorem eval_step_mul_derivative_neg_of_sum_le
    {a b c d : ℝ} {p : ℝ[X]} (hp : IsNegativeSimple p)
    (hH : IsNegativeSimple (step a b p))
    (hdeg : (step a b p).natDegree = p.natDegree + 1)
    (hi : StrictInterl p (step a b p))
    (hno : ∀ r, ¬ (p.IsRoot r ∧ (step a b p).IsRoot r))
    (hsum : a + b ≤ c + d) {r : ℝ} (hr : p.IsRoot r) :
    (step c d p).eval r * p.derivative.eval r < 0 := by
  have hW := wronskian_pos_of_strictInterl_succ hH.2.2.2.1 hp.2.2.2.1 hdeg hi
    hH.2.2.1.roots_nodup hp.2.2.1.roots_nodup (fun r hH hp => hno r ⟨hp, hH⟩) r
  rw [hr.eq_zero] at hW
  have hrneg := hp.2.2.2.2 r ((mem_roots hp.1).mpr hr)
  have hdiff := congrArg (fun q : ℝ[X] => q.eval r) (step_sub_step a b c d p)
  simp only [eval_sub, eval_add, eval_mul, eval_C, theta, eval_X, hr.eq_zero,
    mul_zero, add_zero] at hdiff
  have hnonpos : (c + d - (a + b)) * r * p.derivative.eval r ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hsum) hrneg.le) (sq_nonneg _)
  have hsign : (step c d p).eval r * p.derivative.eval r =
      (step a b p).eval r * p.derivative.eval r +
        (c + d - (a + b)) * r * p.derivative.eval r ^ 2 := by
    rw [sub_eq_iff_eq_add.mp hdiff]
    ring
  rw [hsign]
  linarith

/-- Consecutive rows interlace without common roots when the parameter sums do not decrease. -/
theorem strictInterl_rowsVar_succ {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, 0 < a n * b n)
    (hsum : ∀ n, a n + b n ≤ a (n + 1) + b (n + 1)) :
    ∀ n, StrictInterl (rowsVar a b n) (rowsVar a b (n + 1)) ∧
      ∀ r, ¬ ((rowsVar a b n).IsRoot r ∧ (rowsVar a b (n + 1)).IsRoot r) := by
  have hrows : ∀ n, IsNegativeSimple (rowsVar a b n) ∧ (rowsVar a b n).natDegree = n :=
    fun n => ⟨isNegativeSimple_rowsVar ha hb hab n, natDegree_rowsVar ha hb hab n⟩
  intro n
  induction n with
  | zero =>
      refine ⟨StrictInterl.of_degree_zero_right_of_degree_one one_ne_zero Splits.one
        (hrows 1).1.1 (hrows 1).1.2.1 (by simp [rowsVar]) (hrows 1).2, ?_⟩
      simp [rowsVar, Polynomial.IsRoot.def]
  | succ n ih =>
      have hp := (hrows (n + 1)).1
      obtain ⟨hH, hHdeg⟩ := mapsNegativeSimpleBySucc_step (ha n) (hb n) (hab n) hp
      obtain ⟨hi, hno⟩ := strictInterl_step_of_strictInterl (ha n) (hb n) (hab n) ih.1
        (by rw [(hrows n).2, (hrows (n + 1)).2]) ih.2 (hrows n).1 hp
      have hsign : ∀ r, (rowsVar a b (n + 1)).IsRoot r →
          (rowsVar a b (n + 2)).eval r * (rowsVar a b (n + 1)).derivative.eval r < 0 := by
        intro r hr
        exact eval_step_mul_derivative_neg_of_sum_le hp hH hHdeg hi hno (hsum n) hr
      refine ⟨MaWang.strictInterl_of_interlaces_eval_mul_neg_succ
        (derivative_interlaces_of_pos hp.2.1 hp.2.2.2.1 (by rw [(hrows (n + 1)).2]; lia))
        (hp.2.2.2.1.derivative (by rw [(hrows (n + 1)).2]; lia))
        (hrows (n + 2)).1.2.2.2.1
        (by rw [(hrows (n + 2)).2, (hrows (n + 1)).2]) hsign, ?_⟩
      intro r hr
      have h := hsign r hr.1
      rw [hr.2.eq_zero, zero_mul] at h
      exact (lt_irrefl 0) h

end RealRooted.EulerBidiagonal
