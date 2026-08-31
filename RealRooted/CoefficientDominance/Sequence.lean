import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Geometric decay of log-concave sequences

Finite and infinite positive log-concave sequences are controlled by the
adjacent ratios at a chosen index.
-/

open Finset

namespace RealRooted.CoefficientDominance

/-- A finite sum of positive-exponent powers is bounded by the geometric tail. -/
theorem sum_pow_le {s : Finset ℕ} (hs : ∀ d ∈ s, 1 ≤ d) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    ∑ d ∈ s, r ^ d ≤ r / (1 - r) := by
  classical
  have hdenom : (0 : ℝ) < 1 - r := by linarith
  have hsubset : s ⊆ Finset.Ico 1 (s.sup id + 1) := by
    intro d hd
    rw [Finset.mem_Ico]
    exact ⟨hs d hd, Nat.lt_succ_of_le (Finset.le_sup (f := id) hd)⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun d _ _ => by positivity)) ?_
  have hupper : 1 ≤ s.sup id + 1 := by lia
  have hsplit : (1 : ℝ) + ∑ d ∈ Finset.Ico 1 (s.sup id + 1), r ^ d
      = ∑ d ∈ Finset.range (s.sup id + 1), r ^ d := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun d => r ^ d) (Nat.zero_le 1) hupper]
    simp
  have hgeometric : (∑ d ∈ Finset.range (s.sup id + 1), r ^ d) * (1 - r) ≤ 1 := by
    have hsum := geom_sum_mul r (s.sup id + 1)
    have hpower : (0 : ℝ) ≤ r ^ (s.sup id + 1) := by positivity
    nlinarith [hsum, hpower]
  rw [le_div_iff₀ hdenom]
  nlinarith [hsplit, hgeometric, hdenom]

/-- The sum of two geometric tails is less than one below ratio `1 / 3`. -/
theorem two_geom_lt_one {r : ℝ} (_hr_nonneg : 0 ≤ r) (hr_lt_third : r < 1 / 3) :
    2 * (r / (1 - r)) < 1 := by
  have hdenom : (0 : ℝ) < 1 - r := by linarith
  rw [mul_div_assoc'] at *
  rw [div_lt_one hdenom]
  linarith

/-- Adjacent ratios of a positive log-concave sequence are antitone. -/
theorem ratio_le {t : ℕ → ℝ} (hpositive : ∀ k, 0 < t k)
    (hlog_concave : ∀ k, t k * t (k + 2) ≤ (t (k + 1)) ^ 2) (j d : ℕ) :
    t (j + d + 1) * t j ≤ t (j + 1) * t (j + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hlocal := hlog_concave (j + d)
      have hterm : 0 < t (j + d) := hpositive _
      have hnext : 0 < t (j + d + 1) := hpositive _
      have hj : 0 < t j := hpositive j
      have hgoal : t (j + d + 1 + 1) * t j ≤ t (j + 1) * t (j + d + 1) := by
        nlinarith [ih, hlocal, hterm, hnext, hj]
      calc
        t (j + (d + 1) + 1) * t j = t (j + d + 1 + 1) * t j := by ring_nf
        _ ≤ t (j + 1) * t (j + d + 1) := hgoal
        _ = t (j + 1) * t (j + (d + 1)) := by ring_nf

/-- Upper-tail geometric decay for a positive log-concave sequence. -/
theorem decay_up {t : ℕ → ℝ} (hpositive : ∀ k, 0 < t k)
    (hlog_concave : ∀ k, t k * t (k + 2) ≤ (t (k + 1)) ^ 2) (j d : ℕ) :
    t (j + d) ≤ t j * (t (j + 1) / t j) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hj : 0 < t j := hpositive j
      have hratio := ratio_le hpositive hlog_concave j d
      have hstep : t (j + d + 1) ≤ t (j + d) * (t (j + 1) / t j) := by
        have hdivision : t (j + d + 1) ≤ t (j + 1) * t (j + d) / t j := by
          rw [le_div_iff₀ hj]
          exact hratio
        calc
          t (j + d + 1) ≤ t (j + 1) * t (j + d) / t j := hdivision
          _ = t (j + d) * (t (j + 1) / t j) := by ring
      have hratio_nonneg : (0 : ℝ) ≤ t (j + 1) / t j :=
        le_of_lt (div_pos (hpositive _) hj)
      calc
        t (j + (d + 1)) = t (j + d + 1) := by ring_nf
        _ ≤ t (j + d) * (t (j + 1) / t j) := hstep
        _ ≤ (t j * (t (j + 1) / t j) ^ d) * (t (j + 1) / t j) :=
            mul_le_mul_of_nonneg_right ih hratio_nonneg
        _ = t j * (t (j + 1) / t j) ^ (d + 1) := by ring

/-- Adjacent ratios are antitone inside a finite positive log-concave range. -/
theorem ratio_le_range {t : ℕ → ℝ} {N : ℕ} (hpositive : ∀ k, k < N → 0 < t k)
    (hlog_concave : ∀ k, k + 2 < N → t k * t (k + 2) ≤ (t (k + 1)) ^ 2) (j d : ℕ)
    (hindex : j + d + 1 < N) :
    t (j + d + 1) * t j ≤ t (j + 1) * t (j + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprevious : j + d + 1 < N := by lia
      have hinduction := ih (by lia)
      have hlocal := hlog_concave (j + d) (by lia)
      have hterm : 0 < t (j + d) := hpositive _ (by lia)
      have hnext : 0 < t (j + d + 1) := hpositive _ (by lia)
      have hj : 0 < t j := hpositive j (by lia)
      have hgoal : t (j + d + 1 + 1) * t j ≤ t (j + 1) * t (j + d + 1) := by
        nlinarith [hinduction, hlocal, hterm, hnext, hj]
      calc
        t (j + (d + 1) + 1) * t j = t (j + d + 1 + 1) * t j := by ring_nf
        _ ≤ t (j + 1) * t (j + d + 1) := hgoal
        _ = t (j + 1) * t (j + (d + 1)) := by ring_nf

/-- Upper-tail geometric decay inside a finite positive log-concave range. -/
theorem decay_up_range {t : ℕ → ℝ} {N : ℕ} (hpositive : ∀ k, k < N → 0 < t k)
    (hlog_concave : ∀ k, k + 2 < N → t k * t (k + 2) ≤ (t (k + 1)) ^ 2) (j d : ℕ)
    (hnext : j + 1 < N) (hindex : j + d < N) :
    t (j + d) ≤ t j * (t (j + 1) / t j) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hj : 0 < t j := hpositive j (by lia)
      have hinduction := ih (by lia)
      have hratio := ratio_le_range hpositive hlog_concave j d (by lia)
      have hstep : t (j + d + 1) ≤ t (j + d) * (t (j + 1) / t j) := by
        have hdivision : t (j + d + 1) ≤ t (j + 1) * t (j + d) / t j := by
          rw [le_div_iff₀ hj]
          exact hratio
        calc
          t (j + d + 1) ≤ t (j + 1) * t (j + d) / t j := hdivision
          _ = t (j + d) * (t (j + 1) / t j) := by ring
      have hratio_nonneg : (0 : ℝ) ≤ t (j + 1) / t j :=
        le_of_lt (div_pos (hpositive _ (by lia)) hj)
      calc
        t (j + (d + 1)) = t (j + d + 1) := by ring_nf
        _ ≤ t (j + d) * (t (j + 1) / t j) := hstep
        _ ≤ (t j * (t (j + 1) / t j) ^ d) * (t (j + 1) / t j) :=
            mul_le_mul_of_nonneg_right hinduction hratio_nonneg
        _ = t j * (t (j + 1) / t j) ^ (d + 1) := by ring

/-- Lower-tail geometric decay inside a finite positive log-concave range. -/
theorem decay_down_range {t : ℕ → ℝ} {N : ℕ} (hpositive : ∀ k, k < N → 0 < t k)
    (hlog_concave : ∀ k, k + 2 < N → t k * t (k + 2) ≤ (t (k + 1)) ^ 2) (j : ℕ)
    (hjN : j < N) (e : ℕ) (he : e ≤ j) :
    t (j - e) ≤ t j * (t (j - 1) / t j) ^ e := by
  revert he
  induction e with
  | zero => intro _; simp
  | succ e ih =>
      intro he
      have hinduction := ih (by lia)
      have hj : 0 < t j := hpositive j hjN
      have hrewrite_one : (j - e - 1) + e + 1 = j := by lia
      have hrewrite_two : (j - e - 1) + 1 = j - e := by lia
      have hrewrite_three : (j - e - 1) + e = j - 1 := by lia
      have hratio := ratio_le_range hpositive hlog_concave (j - e - 1) e (by lia)
      rw [hrewrite_one, hrewrite_two, hrewrite_three] at hratio
      have hsub : j - (e + 1) = j - e - 1 := by lia
      rw [hsub]
      have hstep : t (j - e - 1) ≤ t (j - e) * t (j - 1) / t j := by
        rw [le_div_iff₀ hj]
        linarith [hratio]
      have hratio_nonneg : (0 : ℝ) ≤ t (j - 1) / t j :=
        le_of_lt (div_pos (hpositive _ (by lia)) hj)
      calc
        t (j - e - 1) ≤ t (j - e) * t (j - 1) / t j := hstep
        _ = t (j - e) * (t (j - 1) / t j) := by ring
        _ ≤ (t j * (t (j - 1) / t j) ^ e) * (t (j - 1) / t j) :=
            mul_le_mul_of_nonneg_right hinduction hratio_nonneg
        _ = t j * (t (j - 1) / t j) ^ (e + 1) := by ring

end RealRooted.CoefficientDominance
