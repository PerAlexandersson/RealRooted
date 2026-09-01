import RealRooted.CoefficientDominance.Sequence
import RealRooted.Mathlib.Algebra.Polynomial.Dominance

/-!
# Coefficient dominance from log-concavity

Two adjacent small ratios force a coefficient term to dominate the rest of a
finite positive log-concave sequence, yielding a root-exclusion certificate.
-/

open Finset Polynomial

namespace RealRooted.CoefficientDominance

/-- Bound the upper tail of a finite positive log-concave sequence by its first
adjacent ratio. -/
theorem sum_hi_le {t : ℕ → ℝ} {N j : ℕ} (hpositive : ∀ k, k < N → 0 < t k)
    (hlog_concave : ∀ k, k + 2 < N → t k * t (k + 2) ≤ (t (k + 1)) ^ 2)
    (hnext : j + 1 < N) (hratio : t (j + 1) / t j < 1) :
    ∑ k ∈ (range N).filter (fun k => j < k), t k
      ≤ t j * (t (j + 1) / t j / (1 - t (j + 1) / t j)) := by
  classical
  have hj : 0 < t j := hpositive j (by lia)
  have hratio_nonneg : (0 : ℝ) ≤ t (j + 1) / t j :=
    le_of_lt (div_pos (hpositive _ hnext) hj)
  have hbound : ∀ k ∈ (range N).filter (fun k => j < k),
      t k ≤ t j * (t (j + 1) / t j) ^ (k - j) := by
    intro k hk
    rw [Finset.mem_filter, mem_range] at hk
    have hrewrite : k = j + (k - j) := by lia
    conv_lhs => rw [hrewrite]
    exact decay_up_range hpositive hlog_concave j (k - j) hnext (by lia)
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hj.le
  have hinjective : Set.InjOn (fun k => k - j) ((range N).filter (fun k => j < k)) := by
    intro a ha b hb heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_range] at ha hb
    simp only at heq
    lia
  rw [← Finset.sum_image (fun a ha b hb h => hinjective ha hb h)]
  refine sum_pow_le ?_ hratio_nonneg hratio
  intro d hd
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  rw [Finset.mem_filter] at hk
  lia

/-- Bound the lower tail of a finite positive log-concave sequence by its first
adjacent ratio. -/
theorem sum_lo_le {t : ℕ → ℝ} {N j : ℕ} (hpositive : ∀ k, k < N → 0 < t k)
    (hlog_concave : ∀ k, k + 2 < N → t k * t (k + 2) ≤ (t (k + 1)) ^ 2)
    (hjN : j < N) (hj : 1 ≤ j) (hratio : t (j - 1) / t j < 1) :
    ∑ k ∈ (range N).filter (fun k => k < j), t k
      ≤ t j * (t (j - 1) / t j / (1 - t (j - 1) / t j)) := by
  classical
  have hmiddle : 0 < t j := hpositive j hjN
  have hratio_nonneg : (0 : ℝ) ≤ t (j - 1) / t j :=
    le_of_lt (div_pos (hpositive _ (by lia)) hmiddle)
  have hbound : ∀ k ∈ (range N).filter (fun k => k < j),
      t k ≤ t j * (t (j - 1) / t j) ^ (j - k) := by
    intro k hk
    rw [Finset.mem_filter, mem_range] at hk
    have hrewrite : k = j - (j - k) := by lia
    conv_lhs => rw [hrewrite]
    exact decay_down_range hpositive hlog_concave j hjN (j - k) (by lia)
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hmiddle.le
  have hinjective : Set.InjOn (fun k => j - k) ((range N).filter (fun k => k < j)) := by
    intro a ha b hb heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_range] at ha hb
    simp only at heq
    lia
  rw [← Finset.sum_image (fun a ha b hb h => hinjective ha hb h)]
  refine sum_pow_le ?_ hratio_nonneg hratio
  intro d hd
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  rw [Finset.mem_filter] at hk
  lia

/-- If both adjacent ratios of a finite positive log-concave sequence are
below one third, its central term dominates all the others. -/
theorem sum_erase_lt {t : ℕ → ℝ} {N j : ℕ} (hpositive : ∀ k, k < N → 0 < t k)
    (hlog_concave : ∀ k, k + 2 < N → t k * t (k + 2) ≤ (t (k + 1)) ^ 2)
    (hj : 1 ≤ j) (hnext : j + 1 < N)
    (hupper : t (j + 1) / t j < 1 / 3) (hlower : t (j - 1) / t j < 1 / 3) :
    ∑ k ∈ (range N).erase j, t k < t j := by
  classical
  have hjN : j < N := by lia
  have hmiddle : 0 < t j := hpositive j hjN
  have hupper_nonneg : (0 : ℝ) ≤ t (j + 1) / t j :=
    le_of_lt (div_pos (hpositive _ hnext) hmiddle)
  have hlower_nonneg : (0 : ℝ) ≤ t (j - 1) / t j :=
    le_of_lt (div_pos (hpositive _ (by lia)) hmiddle)
  have hhi := sum_hi_le hpositive hlog_concave hnext (by linarith)
  have hlo := sum_lo_le hpositive hlog_concave hjN hj (by linarith)
  have hupper_tail := two_geom_lt_one hupper_nonneg hupper
  have hlower_tail := two_geom_lt_one hlower_nonneg hlower
  have hsplit : ∑ k ∈ (range N).erase j, t k
      = ∑ k ∈ (range N).filter (fun k => k < j), t k
        + ∑ k ∈ (range N).filter (fun k => j < k), t k := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, mem_range]
      constructor
      · rintro ⟨hne, hk⟩
        rcases Nat.lt_or_ge k j with hlt | hge
        · exact Or.inl ⟨hk, hlt⟩
        · exact Or.inr ⟨hk, by lia⟩
      · rintro (⟨hk, hlt⟩ | ⟨hk, hlt⟩) <;> exact ⟨by lia, hk⟩
    · refine Finset.disjoint_left.mpr (fun k hleft hright => ?_)
      rw [Finset.mem_filter] at hleft hright
      lia
  rw [hsplit]
  nlinarith [hhi, hlo, hupper_tail, hlower_tail, hmiddle]

/-- A polynomial with positive log-concave coefficients has no negative root at
a point whose two adjacent coefficient terms are each below one third of the
central term. -/
theorem eval_neg_ne_zero_of_dominant {p : ℝ[X]} {N : ℕ} (hdegree : p.natDegree = N)
    (hpositive : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    {s : ℝ} (hs : 0 < s) (j : ℕ) (hj : 1 ≤ j) (hnext : j + 1 ≤ N)
    (hupper : (p.coeff (j + 1) * s ^ (j + 1)) / (p.coeff j * s ^ j) < 1 / 3)
    (hlower : (p.coeff (j - 1) * s ^ (j - 1)) / (p.coeff j * s ^ j) < 1 / 3) :
    p.eval (-s) ≠ 0 := by
  classical
  set t : ℕ → ℝ := fun i => p.coeff i * s ^ i with ht
  have hpositive_t : ∀ i, i < N + 1 → 0 < t i := by
    intro i hi
    rw [ht]
    exact mul_pos (hpositive i (by lia)) (by positivity)
  have hlog_concave_t : ∀ i, i + 2 < N + 1 → t i * t (i + 2) ≤ (t (i + 1)) ^ 2 := by
    intro i hi
    have hlocal := hlog_concave (i + 1) (by lia) (by lia)
    have hsub : i + 1 - 1 = i := by lia
    rw [hsub] at hlocal
    have hsquare : (0 : ℝ) ≤ (s ^ (i + 1)) ^ 2 := by positivity
    calc
      t i * t (i + 2) = (p.coeff i * p.coeff (i + 2)) * (s ^ (i + 1)) ^ 2 := by
        rw [ht]
        simp only
        ring
      _ ≤ (p.coeff (i + 1)) ^ 2 * (s ^ (i + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right hlocal hsquare
      _ = (t (i + 1)) ^ 2 := by
        rw [ht]
        simp only
        ring
  have hdominates := sum_erase_lt hpositive_t hlog_concave_t hj (by lia) hupper hlower
  refine Polynomial.eval_neg_ne_zero_of_abs_coeff_term_dominates hs (j := j) (N := N + 1)
    (by rw [hdegree]; lia) (by lia) ?_
  have habs : ∀ i ∈ (range (N + 1)).erase j, |p.coeff i| * s ^ i = t i := by
    intro i hi
    have hindex : i < N + 1 := by
      have hmem := Finset.mem_of_mem_erase hi
      rw [mem_range] at hmem
      exact hmem
    rw [abs_of_pos (hpositive i (by lia))]
  rw [Finset.sum_congr rfl habs, abs_of_pos (hpositive j (by lia))]
  exact hdominates

end RealRooted.CoefficientDominance
