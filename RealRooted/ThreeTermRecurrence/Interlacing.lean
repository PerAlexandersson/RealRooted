import RealRooted.MaWang
import RealRooted.Linear

/-!
# Interlacing for three-term recurrences

Rows of `P (n + 2) = a n * P (n + 1) + b n * P n` with degrees `D₀ + n` and
positive leading coefficients interlace as soon as the first two rows do and
`b n ≤ 0` at the roots of `P (n + 1)`.  This is the weak-sign Liu–Wang step
`strictInterl_of_interlaces_evalCoeff_nonpos`, iterated.

The root-sign condition holds in particular when `b n ≤ 0` everywhere
(`threeTerm_interlaces_of_eval_nonpos`), or when `b n ≤ 0` on `(-∞, 0]` and the
rows have nonnegative coefficients (`threeTerm_interlaces_of_nonnegCoeffs`).
`threeTerm_hasNonnegCoeffs` gives the latter when `a n` and `b n` have
nonnegative coefficients.
-/

open Polynomial

namespace RealRooted

section Criteria

private theorem eval_eq_of_natDegree_le_two {p : ℝ[X]} (h : p.natDegree ≤ 2) (r : ℝ) :
    p.eval r = p.coeff 2 * r ^ 2 + p.coeff 1 * r + p.coeff 0 := by
  rw [eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]
  ring

/-- A real polynomial of degree at most two with `p₂ ≤ 0`, `p₀ ≤ 0` and
`p₁² ≤ 4 p₂ p₀` is nonpositive everywhere. -/
theorem eval_nonpos_of_natDegree_le_two {p : ℝ[X]} (hdeg : p.natDegree ≤ 2)
    (h2 : p.coeff 2 ≤ 0) (h0 : p.coeff 0 ≤ 0) (hD : p.coeff 1 ^ 2 ≤ 4 * p.coeff 2 * p.coeff 0)
    (r : ℝ) : p.eval r ≤ 0 := by
  rw [eval_eq_of_natDegree_le_two hdeg]
  rcases h2.lt_or_eq with h2 | h2
  · -- `4 p₂ p(r) = (2 p₂ r + p₁)² + (4 p₂ p₀ - p₁²) ≥ 0`
    nlinarith [sq_nonneg (2 * p.coeff 2 * r + p.coeff 1)]
  · have h1 : p.coeff 1 = 0 := by nlinarith [sq_nonneg (p.coeff 1)]
    rw [h2, h1]
    linarith

/-- A real polynomial of degree at most two with `p₀ ≤ 0`, `p₁ ≥ 0` and `p₂ ≤ 0`
is nonpositive on `(-∞, 0]`. -/
theorem eval_nonpos_of_nonpos_of_natDegree_le_two {p : ℝ[X]} (hdeg : p.natDegree ≤ 2)
    (h0 : p.coeff 0 ≤ 0) (h1 : 0 ≤ p.coeff 1) (h2 : p.coeff 2 ≤ 0) {r : ℝ} (hr : r ≤ 0) :
    p.eval r ≤ 0 := by
  rw [eval_eq_of_natDegree_le_two hdeg]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hr, mul_nonpos_of_nonpos_of_nonneg h2 (sq_nonneg r)]

/-- A real polynomial of degree at most two with nonnegative coefficients
`p₀, p₁, p₂`. -/
theorem hasNonnegCoeffs_of_natDegree_le_two {p : ℝ[X]} (hdeg : p.natDegree ≤ 2)
    (h0 : 0 ≤ p.coeff 0) (h1 : 0 ≤ p.coeff 1) (h2 : 0 ≤ p.coeff 2) : HasNonnegCoeffs p := by
  intro i
  rcases i with _ | _ | _ | i
  · exact h0
  · exact h1
  · exact h2
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Sequence form of `eval_nonpos_of_natDegree_le_two`. -/
theorem eval_nonpos_seq {b : ℕ → ℝ[X]} (hdeg : ∀ n, (b n).natDegree ≤ 2)
    (h2 : ∀ n, (b n).coeff 2 ≤ 0) (h0 : ∀ n, (b n).coeff 0 ≤ 0)
    (hD : ∀ n, (b n).coeff 1 ^ 2 ≤ 4 * (b n).coeff 2 * (b n).coeff 0) :
    ∀ n r, (b n).eval r ≤ 0 :=
  fun n => eval_nonpos_of_natDegree_le_two (hdeg n) (h2 n) (h0 n) (hD n)

/-- Sequence form of `eval_nonpos_of_nonpos_of_natDegree_le_two`. -/
theorem eval_nonpos_of_nonpos_seq {b : ℕ → ℝ[X]} (hdeg : ∀ n, (b n).natDegree ≤ 2)
    (h0 : ∀ n, (b n).coeff 0 ≤ 0) (h1 : ∀ n, 0 ≤ (b n).coeff 1) (h2 : ∀ n, (b n).coeff 2 ≤ 0) :
    ∀ n r, r ≤ 0 → (b n).eval r ≤ 0 :=
  fun n _ hr => eval_nonpos_of_nonpos_of_natDegree_le_two (hdeg n) (h0 n) (h1 n) (h2 n) hr

/-- Sequence form of `hasNonnegCoeffs_of_natDegree_le_two`. -/
theorem hasNonnegCoeffs_seq {b : ℕ → ℝ[X]} (hdeg : ∀ n, (b n).natDegree ≤ 2)
    (h0 : ∀ n, 0 ≤ (b n).coeff 0) (h1 : ∀ n, 0 ≤ (b n).coeff 1) (h2 : ∀ n, 0 ≤ (b n).coeff 2) :
    ∀ n, HasNonnegCoeffs (b n) :=
  fun n => hasNonnegCoeffs_of_natDegree_le_two (hdeg n) (h0 n) (h1 n) (h2 n)

/-- A nonzero constant interlaces a linear polynomial. -/
theorem interlaces_of_natDegree_eq_zero_of_natDegree_eq_one {g f : ℝ[X]} (hg0 : g ≠ 0)
    (hg : g.natDegree = 0) (hf : f.natDegree = 1) : Interlaces g f := by
  rw [eq_C_of_natDegree_eq_zero hg] at hg0 ⊢
  exact interlaces_C_linear (fun h => hg0 (by rw [h, C_0])) hf

end Criteria

variable {P a b : ℕ → ℝ[X]} {D₀ : ℕ}

theorem threeTerm_interlaces (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n r, (P (n + 1)).IsRoot r → (b n).eval r ≤ 0)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  induction n with
  | zero => exact h01
  | succ n ih =>
      have hF : P (n + 2) = a n * P (n + 1) + b n * P n := hrec n
      have hprec : StrictInterl (P (n + 1)) (a n * P (n + 1) + b n * P n) :=
        strictInterl_of_interlaces_evalCoeff_nonpos ih (hpos n)
          (by rw [← hF]; exact hpos (n + 2))
          (by rw [← hF, hdeg, hdeg]; omega) (by rw [← hF, hdeg, hdeg]; omega) (hb n)
      rw [← hF] at hprec
      exact hprec.toInterlaces (by rw [hdeg, hdeg]; omega)

theorem threeTerm_interlaces_of_eval_nonpos
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n r, (b n).eval r ≤ 0) (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  threeTerm_interlaces hrec hdeg hpos (fun n r _ => hb n r) h01 n

theorem threeTerm_interlaces_of_nonnegCoeffs
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (hb : ∀ n r, r ≤ 0 → (b n).eval r ≤ 0)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  refine threeTerm_interlaces hrec hdeg hpos (fun n r hr => hb n r ?_) h01 n
  have hne : P (n + 1) ≠ 0 := leadingCoeff_ne_zero.mp (hpos (n + 1)).ne'
  exact roots_nonpos_of_hasNonnegCoeffs (hnn (n + 1)) r ((mem_roots hne).mpr hr)

/-- Rows of a three-term recurrence with nonnegative coefficients. -/
theorem threeTerm_hasNonnegCoeffs (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, HasNonnegCoeffs (a n)) (hb : ∀ n, HasNonnegCoeffs (b n))
    (h0 : HasNonnegCoeffs (P 0)) (h1 : HasNonnegCoeffs (P 1)) :
    ∀ n, HasNonnegCoeffs (P n)
  | 0 => h0
  | 1 => h1
  | n + 2 => by
      rw [hrec n]
      exact ((ha n).mul (threeTerm_hasNonnegCoeffs hrec ha hb h0 h1 (n + 1))).add
        ((hb n).mul (threeTerm_hasNonnegCoeffs hrec ha hb h0 h1 n))

end RealRooted
