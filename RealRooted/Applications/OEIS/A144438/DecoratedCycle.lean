import RealRooted.Applications.OEIS.A144438
import RealRooted.DerivativeRecurrence.QuadraticLagStrict

/-!
# Decorated cycle-q Eulerian recurrence

This file formalizes the polynomial family determined by the initial rows

`C 0 = 1`, `C 1 = q`, `C 2 = q^2 + q X`

and its second-order differential recurrence.  The proof uses a normalized
monic family and the generic quadratic-lag strict-interlacing theorem.  No
permutation, cycle, excedance, or decoration interpretation is asserted.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The monic normalization of the decorated cycle-q recurrence. -/
def normalizedDecoratedCycleEulerian (q : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C q + X
  | n + 2 =>
      (X - X ^ 2) * (normalizedDecoratedCycleEulerian q (n + 1)).derivative +
        (C q + C ((2 : ℝ) + n) * X) * normalizedDecoratedCycleEulerian q (n + 1) +
          (C q * X) * normalizedDecoratedCycleEulerian q n

@[simp]
theorem normalizedDecoratedCycleEulerian_zero (q : ℝ) :
    normalizedDecoratedCycleEulerian q 0 = 1 := rfl

@[simp]
theorem normalizedDecoratedCycleEulerian_one (q : ℝ) :
    normalizedDecoratedCycleEulerian q 1 = C q + X := rfl

/-- The normalized second-order differential recurrence. -/
theorem normalizedDecoratedCycleEulerian_recurrence (q : ℝ) (n : ℕ) :
    normalizedDecoratedCycleEulerian q (n + 2) =
      (X - X ^ 2) * (normalizedDecoratedCycleEulerian q (n + 1)).derivative +
        (C q + C ((2 : ℝ) + n) * X) * normalizedDecoratedCycleEulerian q (n + 1) +
          (C q * X) * normalizedDecoratedCycleEulerian q n := rfl

private theorem normalizedDecoratedCycleEulerian_affine_recurrence (q : ℝ) (n : ℕ) :
    normalizedDecoratedCycleEulerian q (n + 2) =
      (C 1 * X + C (-1) * X ^ 2) *
          (normalizedDecoratedCycleEulerian q (n + 1)).derivative +
        (C q + C ((2 : ℝ) + n) * X) * normalizedDecoratedCycleEulerian q (n + 1) +
          (C q * X) * normalizedDecoratedCycleEulerian q n := by
  simpa only [map_one, map_neg, one_mul, neg_one_mul, sub_eq_add_neg] using
    normalizedDecoratedCycleEulerian_recurrence q n

/-- Coefficient recurrence for the monic normalization. -/
theorem normalizedDecoratedCycleEulerian_coeff_succ_succ (q : ℝ) (n k : ℕ) :
    (normalizedDecoratedCycleEulerian q (n + 2)).coeff (k + 1) =
      ((k : ℝ) + 1 + q) *
          (normalizedDecoratedCycleEulerian q (n + 1)).coeff (k + 1) +
        ((n : ℝ) + 2 - k) *
            (normalizedDecoratedCycleEulerian q (n + 1)).coeff k +
          q * (normalizedDecoratedCycleEulerian q n).coeff k := by
  rw [normalizedDecoratedCycleEulerian_affine_recurrence, coeff_add,
    Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  rw [show (C q * X) * normalizedDecoratedCycleEulerian q n =
      C q * (X * normalizedDecoratedCycleEulerian q n) by ring]
  simp only [coeff_C_mul, coeff_X_mul]
  ring

/-- The top coefficient is one and coefficients above the rank vanish. -/
theorem normalizedDecoratedCycleEulerian_top_and_above (q : ℝ) :
    ∀ n : ℕ,
      (normalizedDecoratedCycleEulerian q n).coeff n = 1 ∧
        ∀ k > n, (normalizedDecoratedCycleEulerian q n).coeff k = 0
  | 0 => by
      constructor
      · simp
      · intro k hk
        simp [coeff_one, show k ≠ 0 by lia]
  | 1 => by
      constructor
      · simp [coeff_add]
      · intro k hk
        simp [coeff_add, coeff_C, coeff_X, show k ≠ 0 by lia, show 1 ≠ k by lia]
  | n + 2 => by
      rcases normalizedDecoratedCycleEulerian_top_and_above q (n + 1) with
        ⟨htop1, habove1⟩
      rcases normalizedDecoratedCycleEulerian_top_and_above q n with
        ⟨_, habove0⟩
      constructor
      · rw [show n + 2 = (n + 1) + 1 by lia,
          normalizedDecoratedCycleEulerian_coeff_succ_succ]
        rw [habove1 (n + 2) (by lia), htop1, habove0 (n + 1) (by lia)]
        push_cast
        ring
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [normalizedDecoratedCycleEulerian_coeff_succ_succ]
        rw [habove1 (k + 1) (by lia), habove1 k (by lia), habove0 k (by lia)]
        ring

/-- The monic normalization has degree equal to its rank. -/
@[simp]
theorem normalizedDecoratedCycleEulerian_natDegree (q : ℝ) (n : ℕ) :
    (normalizedDecoratedCycleEulerian q n).natDegree = n := by
  rcases normalizedDecoratedCycleEulerian_top_and_above q n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => habove k hk) (by simp [htop])

/-- The monic normalization is monic at every rank. -/
theorem normalizedDecoratedCycleEulerian_monic (q : ℝ) (n : ℕ) :
    (normalizedDecoratedCycleEulerian q n).Monic := by
  change (normalizedDecoratedCycleEulerian q n).leadingCoeff = 1
  rw [leadingCoeff, normalizedDecoratedCycleEulerian_natDegree]
  exact (normalizedDecoratedCycleEulerian_top_and_above q n).1

/-- The constant coefficient of normalized rank `n` is `q^n`. -/
@[simp]
theorem normalizedDecoratedCycleEulerian_coeff_zero (q : ℝ) :
    ∀ n : ℕ, (normalizedDecoratedCycleEulerian q n).coeff 0 = q ^ n
  | 0 => by simp
  | 1 => by simp [coeff_add]
  | n + 2 => by
      rw [normalizedDecoratedCycleEulerian_recurrence]
      simp only [coeff_add, coeff_mul]
      simp [normalizedDecoratedCycleEulerian_coeff_zero q (n + 1), pow_succ]
      ring

/-- Positive `q` gives strictly positive coefficients throughout the degree
support of the monic normalization. -/
theorem normalizedDecoratedCycleEulerian_coeff_pos_of_le {q : ℝ} (hq : 0 < q) :
    ∀ n k : ℕ, k ≤ n → 0 < (normalizedDecoratedCycleEulerian q n).coeff k := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro k hk
      have : k = 0 := by lia
      subst k
      simp
  | one =>
      intro k hk
      interval_cases k <;> simp [coeff_add, hq]
  | more n ih0 ih1 =>
      intro k hk
      rcases k with _ | k
      · rw [normalizedDecoratedCycleEulerian_coeff_zero]
        positivity
      · rw [normalizedDecoratedCycleEulerian_coeff_succ_succ]
        have hk_le : k ≤ n + 1 := by lia
        have hk_real : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk_le
        have hfirst :
            0 ≤ ((k : ℝ) + 1 + q) *
              (normalizedDecoratedCycleEulerian q (n + 1)).coeff (k + 1) := by
          refine mul_nonneg (by positivity) ?_
          by_cases hsupp : k + 1 ≤ n + 1
          · exact (ih1 (k + 1) hsupp).le
          · rw [(normalizedDecoratedCycleEulerian_top_and_above q (n + 1)).2
              (k + 1) (by lia)]
        have hmiddle :
            0 < ((n : ℝ) + 2 - k) *
              (normalizedDecoratedCycleEulerian q (n + 1)).coeff k :=
          mul_pos (by linarith) (ih1 k hk_le)
        have hlast :
            0 ≤ q * (normalizedDecoratedCycleEulerian q n).coeff k := by
          refine mul_nonneg hq.le ?_
          by_cases hsupp : k ≤ n
          · exact (ih0 k hsupp).le
          · rw [(normalizedDecoratedCycleEulerian_top_and_above q n).2 k (by lia)]
        linarith

/-- Positive `q` gives nonnegative coefficients at every normalized rank. -/
theorem normalizedDecoratedCycleEulerian_hasNonnegCoeffs {q : ℝ} (hq : 0 < q)
    (n : ℕ) : HasNonnegCoeffs (normalizedDecoratedCycleEulerian q n) := by
  intro k
  by_cases hk : k ≤ n
  · exact (normalizedDecoratedCycleEulerian_coeff_pos_of_le hq n k hk).le
  · rw [(normalizedDecoratedCycleEulerian_top_and_above q n).2 k (by lia)]

/-- Every real root of the normalized family is strictly negative for
positive `q`. -/
theorem normalizedDecoratedCycleEulerian_root_neg {q : ℝ} (hq : 0 < q)
    (n : ℕ) {r : ℝ} (hr : (normalizedDecoratedCycleEulerian q n).IsRoot r) :
    r < 0 := by
  have hp := normalizedDecoratedCycleEulerian_monic q n
  have hmem : r ∈ (normalizedDecoratedCycleEulerian q n).roots :=
    (mem_roots hp.ne_zero).mpr hr
  have hrle := roots_nonpos_of_hasNonnegCoeffs
    (normalizedDecoratedCycleEulerian_hasNonnegCoeffs hq n) r hmem
  apply lt_of_le_of_ne hrle
  intro hr0
  subst r
  rw [Polynomial.IsRoot.def] at hr
  have heval : eval 0 (normalizedDecoratedCycleEulerian q n) = q ^ n := by
    rw [← coeff_zero_eq_eval_zero,
      normalizedDecoratedCycleEulerian_coeff_zero]
  rw [heval] at hr
  exact (pow_pos hq n).ne' hr

private theorem normalizedDecoratedCycleEulerian_base_prec (q : ℝ) :
    Prec (normalizedDecoratedCycleEulerian q 0)
      (normalizedDecoratedCycleEulerian q 1) := by
  rw [normalizedDecoratedCycleEulerian_zero]
  exact (interlaces_one_linear (p := normalizedDecoratedCycleEulerian q 1)
    (normalizedDecoratedCycleEulerian_natDegree q 1)).toPrec

private theorem normalizedDecoratedCycleEulerian_base_noCommon {q : ℝ} :
    ∀ r, (normalizedDecoratedCycleEulerian q 1).IsRoot r →
      ¬ (normalizedDecoratedCycleEulerian q 0).IsRoot r := by
  intro r _ hr0
  simp [Polynomial.IsRoot.def] at hr0

/-- Strict adjacent proper position and no common root for the normalized
family. -/
theorem normalizedDecoratedCycleEulerian_prec_and_noCommonRoot
    {q : ℝ} (hq : 0 < q) (n : ℕ) :
    Prec (normalizedDecoratedCycleEulerian q n)
        (normalizedDecoratedCycleEulerian q (n + 1)) ∧
      ∀ r : ℝ, (normalizedDecoratedCycleEulerian q (n + 1)).IsRoot r →
        ¬ (normalizedDecoratedCycleEulerian q n).IsRoot r := by
  exact prec_and_noCommonRoot_of_quadratic_lag
    (normalizedDecoratedCycleEulerian q) 1 1 q
      (fun m => C q + C ((2 : ℝ) + m) * X) (by norm_num) (by norm_num) hq.le
      (normalizedDecoratedCycleEulerian_natDegree q)
      (fun m => by
        rw [HasPosLeadingCoeff, normalizedDecoratedCycleEulerian_monic]
        norm_num)
      (fun m r hr => normalizedDecoratedCycleEulerian_root_neg hq m hr)
      (normalizedDecoratedCycleEulerian_base_prec q)
      normalizedDecoratedCycleEulerian_base_noCommon
      (normalizedDecoratedCycleEulerian_affine_recurrence q) n

/-- The recurrence-defined decorated cycle-q Eulerian family. -/
def decoratedCycleEulerian (q : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C q * normalizedDecoratedCycleEulerian q n

@[simp]
theorem decoratedCycleEulerian_zero (q : ℝ) : decoratedCycleEulerian q 0 = 1 := rfl

@[simp]
theorem decoratedCycleEulerian_one (q : ℝ) : decoratedCycleEulerian q 1 = C q := by
  simp [decoratedCycleEulerian]

@[simp]
theorem decoratedCycleEulerian_two (q : ℝ) :
    decoratedCycleEulerian q 2 = C (q ^ 2) + C q * X := by
  simp [decoratedCycleEulerian]
  ring

/-- The defining decorated cycle-q recurrence, indexed so the output rank is
`n + 3`. -/
theorem decoratedCycleEulerian_recurrence (q : ℝ) (n : ℕ) :
    decoratedCycleEulerian q (n + 3) =
      (C q + C ((n : ℝ) + 2) * X) * decoratedCycleEulerian q (n + 2) +
        (X - X ^ 2) * (decoratedCycleEulerian q (n + 2)).derivative +
          (C q * X) * decoratedCycleEulerian q (n + 1) := by
  simp only [decoratedCycleEulerian]
  rw [normalizedDecoratedCycleEulerian_recurrence]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  ring_nf

/-- At positive `q`, rank `n + 1` has degree `n`. -/
@[simp]
theorem decoratedCycleEulerian_natDegree {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (decoratedCycleEulerian q (n + 1)).natDegree = n := by
  rw [decoratedCycleEulerian, natDegree_C_mul hq.ne',
    normalizedDecoratedCycleEulerian_natDegree]

/-- The leading coefficient of rank `n + 1` is `q`. -/
theorem decoratedCycleEulerian_leadingCoeff {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (decoratedCycleEulerian q (n + 1)).leadingCoeff = q := by
  rw [decoratedCycleEulerian, leadingCoeff, natDegree_C_mul hq.ne',
    normalizedDecoratedCycleEulerian_natDegree, coeff_C_mul,
    (normalizedDecoratedCycleEulerian_top_and_above q n).1]
  ring

/-- Positive `q` gives positive coefficients exactly through degree `n` at
rank `n + 1`. -/
theorem decoratedCycleEulerian_coeff_pos_iff {q : ℝ} (hq : 0 < q) (n k : ℕ) :
    0 < (decoratedCycleEulerian q (n + 1)).coeff k ↔ k ≤ n := by
  rw [decoratedCycleEulerian, coeff_C_mul]
  constructor
  · intro hpos
    by_contra hk
    rw [(normalizedDecoratedCycleEulerian_top_and_above q n).2 k (by lia)] at hpos
    simp at hpos
  · intro hk
    exact mul_pos hq (normalizedDecoratedCycleEulerian_coeff_pos_of_le hq n k hk)

/-- Positive `q` gives nonnegative coefficients at every rank. -/
theorem decoratedCycleEulerian_hasNonnegCoeffs {q : ℝ} (hq : 0 < q) (n : ℕ) :
    HasNonnegCoeffs (decoratedCycleEulerian q n) := by
  rcases n with _ | n
  · intro k
    rw [decoratedCycleEulerian, coeff_one]
    split_ifs <;> norm_num
  · intro k
    simp only [decoratedCycleEulerian, coeff_C_mul]
    exact mul_nonneg hq.le (normalizedDecoratedCycleEulerian_hasNonnegCoeffs hq n k)

/-- Consecutive positive ranks are in proper position for positive `q`. -/
theorem decoratedCycleEulerian_prec {q : ℝ} (hq : 0 < q) (n : ℕ) :
    Prec (decoratedCycleEulerian q (n + 1))
      (decoratedCycleEulerian q (n + 2)) := by
  simpa only [decoratedCycleEulerian] using
    (normalizedDecoratedCycleEulerian_prec_and_noCommonRoot hq n).1.C_mul_left
      hq.ne' |>.C_mul_right hq.ne'

/-- Every positive-rank polynomial splits over the reals. -/
theorem decoratedCycleEulerian_splits {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (decoratedCycleEulerian q (n + 1)).Splits :=
  (decoratedCycleEulerian_prec hq n).1.2

/-- Consecutive positive ranks strictly interlace for positive `q`. -/
theorem decoratedCycleEulerian_interlaces {q : ℝ} (hq : 0 < q) (n : ℕ) :
    Interlaces (decoratedCycleEulerian q (n + 1))
      (decoratedCycleEulerian q (n + 2)) := by
  exact (decoratedCycleEulerian_prec hq n).toInterlaces (by
    rw [decoratedCycleEulerian_natDegree hq, decoratedCycleEulerian_natDegree hq])

/-- Consecutive positive ranks have no common real root. -/
theorem decoratedCycleEulerian_noCommonRoot {q : ℝ} (hq : 0 < q) (n : ℕ)
    (r : ℝ) (hr : (decoratedCycleEulerian q (n + 2)).IsRoot r) :
    ¬ (decoratedCycleEulerian q (n + 1)).IsRoot r := by
  simp only [decoratedCycleEulerian, Polynomial.IsRoot.def, eval_mul, eval_C] at hr ⊢
  exact fun hr0 => (normalizedDecoratedCycleEulerian_prec_and_noCommonRoot hq n).2 r
    (by exact (mul_eq_zero.mp hr).resolve_left hq.ne')
    ((mul_eq_zero.mp hr0).resolve_left hq.ne')

/-- Every real root at a positive rank is strictly negative. -/
theorem decoratedCycleEulerian_root_neg {q : ℝ} (hq : 0 < q) (n : ℕ) {r : ℝ}
    (hr : (decoratedCycleEulerian q (n + 1)).IsRoot r) : r < 0 := by
  rw [decoratedCycleEulerian, Polynomial.IsRoot.def, eval_mul, eval_C] at hr
  exact normalizedDecoratedCycleEulerian_root_neg hq n
    ((mul_eq_zero.mp hr).resolve_left hq.ne')

/-- Every positive-rank polynomial has simple real roots. -/
theorem decoratedCycleEulerian_hasSimpleRoots {q : ℝ} (hq : 0 < q) (n : ℕ) :
    HasSimpleRoots (decoratedCycleEulerian q (n + 1)) :=
  ((decoratedCycleEulerian_prec hq n).hasSimpleRoots_of_no_common_root fun r hr =>
    decoratedCycleEulerian_noCommonRoot hq n r hr.2 hr.1).1

/-- At `q = 1`, positive rank `n + 1` is exactly the deco Eulerian polynomial
of local rank `n`. -/
theorem decoratedCycleEulerian_one_eq_decoEulerian :
    ∀ n : ℕ, decoratedCycleEulerian 1 (n + 1) = decoEulerian n := by
  intro n
  simp only [decoratedCycleEulerian, map_one, one_mul]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [decoEulerian]
  | more n ih0 ih1 =>
      rw [normalizedDecoratedCycleEulerian_recurrence, decoEulerian_recurrence, ih0, ih1]
      simp

end RealRooted.Applications.OEIS
