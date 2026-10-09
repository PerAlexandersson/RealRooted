import RealRooted.EulerBidiagonal

open Polynomial

noncomputable section

namespace RealRooted.EulerTypeRows

/-- The rows obtained from an Euler-bidiagonal family by positive scaling. -/
def scaledRows (κ a b : ℝ) (n : ℕ) : ℝ[X] :=
  C (κ ^ n) * (EulerBidiagonal.rows a b n).comp (C (κ⁻¹) * X)

/-- The recurrence `X P + κ (θ+a) (θ+b) P` in Euler-operator form. -/
def recurrenceRows (κ a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X * recurrenceRows κ a b n +
        C κ * (theta (theta (recurrenceRows κ a b n)) +
          C (a + b) * theta (recurrenceRows κ a b n) +
          C (a * b) * recurrenceRows κ a b n)

private theorem theta_comp_C_mul_X (κ : ℝ) (p : ℝ[X]) :
    theta (p.comp (C (κ⁻¹) * X)) = (theta p).comp (C (κ⁻¹) * X) := by
  simp only [theta, Polynomial.derivative_comp, derivative_mul, derivative_C,
    derivative_X, mul_one, mul_comp, X_comp]
  ring

private theorem scaledRows_zero (κ a b : ℝ) : scaledRows κ a b 0 = 1 := by
  simp [scaledRows, EulerBidiagonal.rows]

private theorem scaledRows_succ (κ a b : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    scaledRows κ a b (n + 1) =
      X * scaledRows κ a b n +
        C κ * (theta (theta (scaledRows κ a b n)) +
          C (a + b) * theta (scaledRows κ a b n) +
          C (a * b) * scaledRows κ a b n) := by
  simp only [scaledRows, EulerBidiagonal.rows, EulerBidiagonal.step, map_add,
    map_mul, C_comp, add_comp, mul_comp, X_comp, theta_C_mul,
    theta_comp_C_mul_X]
  rw [pow_succ]
  have hC : C κ * C κ⁻¹ = (1 : ℝ[X]) := by
    rw [← C_mul, mul_inv_cancel₀ hκ, C_1]
  simp only [mul_add]
  have hCprod : C (κ ^ n * κ) = C (κ ^ n) * C κ := by
    rw [C_mul]
  rw [hCprod]
  have hfirst (q : ℝ[X]) :
      C (κ ^ n) * C κ * (C κ⁻¹ * X * q) = C (κ ^ n) * X * q := by
    calc
      C (κ ^ n) * C κ * (C κ⁻¹ * X * q) =
          C (κ ^ n) * (C κ * C κ⁻¹) * X * q := by ring
      _ = C (κ ^ n) * X * q := by rw [hC]; ring
  rw [hfirst]
  ring_nf

/-- The Euler-operator recurrence agrees with the scaled Euler rows. -/
theorem recurrenceRows_eq_scaledRows (κ a b : ℝ) (hκ : κ ≠ 0) :
    ∀ n, recurrenceRows κ a b n = scaledRows κ a b n := by
  intro n
  induction n with
  | zero => exact (scaledRows_zero κ a b).symm
  | succ n ih =>
      rw [recurrenceRows, scaledRows_succ κ a b hκ n, ih]

private theorem noCommon_comp_C_mul_X {f g : ℝ[X]}
    (h : ∀ r, ¬ (f.IsRoot r ∧ g.IsRoot r)) {c : ℝ} :
    ∀ r, ¬ ((f.comp (C c * X)).IsRoot r ∧ (g.comp (C c * X)).IsRoot r) := by
  intro r hr
  apply h (c * r)
  constructor
  · rw [Polynomial.IsRoot.def] at hr ⊢
    simpa only [Polynomial.eval_comp, eval_mul, eval_C, eval_X, mul_one] using hr.1
  · have hgr := hr.2
    rw [Polynomial.IsRoot.def] at hgr ⊢
    simpa only [Polynomial.eval_comp, eval_mul, eval_C, eval_X, mul_one] using hgr

private theorem noCommon_C_mul {f g : ℝ[X]}
    (h : ∀ r, ¬ (f.IsRoot r ∧ g.IsRoot r)) {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ r, ¬ ((C c * f).IsRoot r ∧ (C d * g).IsRoot r) := by
  intro r hr
  apply h r
  constructor
  · have hfr := hr.1
    rw [Polynomial.IsRoot.def] at hfr ⊢
    simpa only [eval_mul, eval_C, one_mul, mul_eq_zero, hc, false_or] using hfr
  · have hgr := hr.2
    rw [Polynomial.IsRoot.def] at hgr ⊢
    simpa only [eval_mul, eval_C, one_mul, mul_eq_zero, hd, false_or] using hgr

/-- Positive scaling transports strict interlacing and coprimality of Euler rows. -/
theorem strictInterl_scaledRows (κ a b : ℝ) (hκ : 0 < κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a * b) (n : ℕ) :
    StrictInterl (scaledRows κ a b n) (scaledRows κ a b (n + 1)) ∧
      ∀ r, ¬ ((scaledRows κ a b n).IsRoot r ∧
        (scaledRows κ a b (n + 1)).IsRoot r) := by
  have hbase := EulerBidiagonal.strictInterl_rows ha hb hab n
  have hcomp := hbase.1.comp_C_mul_X (by positivity : 0 < κ⁻¹)
  have hscaled := StrictInterl.C_mul_right
    (StrictInterl.C_mul_left hcomp (by positivity : κ ^ n ≠ 0))
    (by positivity : κ ^ (n + 1) ≠ 0)
  refine ⟨?_, ?_⟩
  · simpa [scaledRows] using hscaled
  · apply noCommon_C_mul (noCommon_comp_C_mul_X hbase.2)
    · positivity
    · positivity

/-- Every positive scaled Euler row has the same degree as its unscaled row. -/
theorem scaledRows_natDegree (κ a b : ℝ) (hκ : 0 < κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a * b) (n : ℕ) :
    (scaledRows κ a b n).natDegree = n := by
  have hrows := EulerBidiagonal.isNegativeSimple_rows ha hb hab n
  have hcomp := Polynomial.natDegree_comp_eq_of_mul_ne_zero
    (p := EulerBidiagonal.rows a b n) (q := C (κ⁻¹) * X) (by
      simp [hrows.1.1, hκ.ne'])
  rw [scaledRows, Polynomial.natDegree_C_mul (pow_ne_zero _ hκ.ne'), hcomp, hrows.2]
  simp [hκ.ne']

/-- The scaled Euler rows also satisfy the downstream `Interlaces` relation. -/
theorem interlaces_scaledRows (κ a b : ℝ) (hκ : 0 < κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a * b) (n : ℕ) :
    Interlaces (scaledRows κ a b n) (scaledRows κ a b (n + 1)) := by
  have h := strictInterl_scaledRows κ a b hκ ha hb hab n
  apply h.1.toInterlaces
  rw [scaledRows_natDegree κ a b hκ ha hb hab n,
    scaledRows_natDegree κ a b hκ ha hb hab (n + 1)]

/-- The A080248 rows, in the normalized Euler-operator recurrence. -/
def A080248Rows : ℕ → ℝ[X] := recurrenceRows (1 / 2) 1 2

/-- The A160562 rows, in the normalized Euler-operator recurrence. -/
def A160562Rows : ℕ → ℝ[X] := recurrenceRows 4 (1 / 2) (1 / 2)

/-- The A269945 rows after removing their persistent factor `X`. -/
def A269945QuotientRows : ℕ → ℝ[X] := recurrenceRows 1 1 1

/-- The A080248 recurrence is `X P + (1/2) (θ+1) (θ+2) P`. -/
theorem A080248Rows_succ (n : ℕ) :
    A080248Rows (n + 1) = X * A080248Rows n +
      C (1 / 2) * (theta (theta (A080248Rows n)) +
      C 3 * theta (A080248Rows n) + C 2 * A080248Rows n) := by
  simp only [A080248Rows, recurrenceRows]
  norm_num

/-- The A160562 recurrence is `X P + 4 (θ+1/2)^2 P`. -/
theorem A160562Rows_succ (n : ℕ) :
    A160562Rows (n + 1) = X * A160562Rows n +
      C 4 * (theta (theta (A160562Rows n)) +
      C 1 * theta (A160562Rows n) + C (1 / 4) * A160562Rows n) := by
  simp only [A160562Rows, recurrenceRows]
  norm_num

/-- The A269945 quotient recurrence is `X Q + (θ+1)^2 Q`. -/
theorem A269945QuotientRows_succ (n : ℕ) :
    A269945QuotientRows (n + 1) = X * A269945QuotientRows n +
      C 1 * (theta (theta (A269945QuotientRows n)) +
      C 2 * theta (A269945QuotientRows n) + C 1 * A269945QuotientRows n) := by
  simp only [A269945QuotientRows, recurrenceRows]
  norm_num

/-- A080248 agrees with the scaled Euler rows for `(κ,a,b)=(1/2,1,2)`. -/
theorem A080248Rows_eq_scaledRows (n : ℕ) :
    A080248Rows n = scaledRows (1 / 2) 1 2 n := by
  simpa [A080248Rows] using recurrenceRows_eq_scaledRows (1 / 2) 1 2 (by norm_num) n

/-- A160562 agrees with the scaled Euler rows for `(κ,a,b)=(4,1/2,1/2)`. -/
theorem A160562Rows_eq_scaledRows (n : ℕ) :
    A160562Rows n = scaledRows 4 (1 / 2) (1 / 2) n := by
  simpa [A160562Rows] using recurrenceRows_eq_scaledRows 4 (1 / 2) (1 / 2) (by norm_num) n

/-- The A269945 quotient rows agree with the `(κ,a,b)=(1,1,1)` scaling. -/
theorem A269945QuotientRows_eq_scaledRows (n : ℕ) :
    A269945QuotientRows n = scaledRows 1 1 1 n := by
  simpa [A269945QuotientRows] using recurrenceRows_eq_scaledRows 1 1 1 (by norm_num) n

/-- Consecutive A080248 rows strictly interlace and have no common root. -/
theorem strictInterl_A080248Rows (n : ℕ) :
    StrictInterl (A080248Rows n) (A080248Rows (n + 1)) ∧
      ∀ r, ¬ ((A080248Rows n).IsRoot r ∧ (A080248Rows (n + 1)).IsRoot r) := by
  rw [A080248Rows_eq_scaledRows n, A080248Rows_eq_scaledRows (n + 1)]
  exact strictInterl_scaledRows (1 / 2) 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) n

/-- Consecutive A160562 rows strictly interlace and have no common root. -/
theorem strictInterl_A160562Rows (n : ℕ) :
    StrictInterl (A160562Rows n) (A160562Rows (n + 1)) ∧
      ∀ r, ¬ ((A160562Rows n).IsRoot r ∧ (A160562Rows (n + 1)).IsRoot r) := by
  rw [A160562Rows_eq_scaledRows n, A160562Rows_eq_scaledRows (n + 1)]
  exact strictInterl_scaledRows 4 (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) n

/-- Consecutive A080248 rows interlace in the downstream orientation. -/
theorem interlaces_A080248Rows (n : ℕ) :
    Interlaces (A080248Rows n) (A080248Rows (n + 1)) := by
  rw [A080248Rows_eq_scaledRows n, A080248Rows_eq_scaledRows (n + 1)]
  exact interlaces_scaledRows (1 / 2) 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) n

/-- Consecutive A160562 rows interlace in the downstream orientation. -/
theorem interlaces_A160562Rows (n : ℕ) :
    Interlaces (A160562Rows n) (A160562Rows (n + 1)) := by
  rw [A160562Rows_eq_scaledRows n, A160562Rows_eq_scaledRows (n + 1)]
  exact interlaces_scaledRows 4 (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) n

/-- Consecutive A269945 quotient rows strictly interlace and have no common root. -/
theorem strictInterl_A269945QuotientRows (n : ℕ) :
    StrictInterl (A269945QuotientRows n) (A269945QuotientRows (n + 1)) ∧
      ∀ r, ¬ ((A269945QuotientRows n).IsRoot r ∧
        (A269945QuotientRows (n + 1)).IsRoot r) := by
  rw [A269945QuotientRows_eq_scaledRows n, A269945QuotientRows_eq_scaledRows (n + 1)]
  exact strictInterl_scaledRows 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) n

/-- Consecutive A269945 quotient rows interlace in the downstream orientation. -/
theorem interlaces_A269945QuotientRows (n : ℕ) :
    Interlaces (A269945QuotientRows n) (A269945QuotientRows (n + 1)) := by
  rw [A269945QuotientRows_eq_scaledRows n, A269945QuotientRows_eq_scaledRows (n + 1)]
  exact interlaces_scaledRows 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) n

end RealRooted.EulerTypeRows
