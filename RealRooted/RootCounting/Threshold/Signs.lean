import RealRooted.RootCounting.SignChanges
import RealRooted.RootCounting.Threshold.Basic

/-!
# Signed evaluations from coefficient dominance

Applications of dominant coefficients to a far-left evaluation, and a
splitness criterion expressed through signed evaluations at ordered points.
-/

namespace RealRooted.RootCounting

open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Positive coefficients make the leading term dominate sufficiently far left. -/
theorem sign_at_far_left {p : K[X]} (hpos : ∀ k, k ≤ p.natDegree → 0 < p.coeff k)
    (hd1 : 1 ≤ p.natDegree) {R : K} (hR : 1 ≤ R)
    (hbig : ∑ k ∈ Finset.range p.natDegree, p.coeff k < p.coeff p.natDegree * R) :
    0 < (-1 : K) ^ p.natDegree * p.eval (-R) := by
  classical
  have hR0 : (0 : K) < R := lt_of_lt_of_le one_pos hR
  have hcd : 0 < p.coeff p.natDegree := hpos p.natDegree (le_refl _)
  have herase : (Finset.range (p.natDegree + 1)).erase p.natDegree
      = Finset.range p.natDegree := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_range]
    lia
  have hRd : (0 : K) < R ^ p.natDegree := by positivity
  have hdom : ∑ k ∈ (Finset.range (p.natDegree + 1)).erase p.natDegree,
      |p.coeff k| * R ^ k < |p.coeff p.natDegree| * R ^ p.natDegree := by
    rw [herase, abs_of_pos hcd]
    have hstep : ∀ k ∈ Finset.range p.natDegree,
        |p.coeff k| * R ^ k ≤ p.coeff k * R ^ (p.natDegree - 1) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [abs_of_pos (hpos k (by lia))]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hpos k (by lia)))
      exact pow_le_pow_right₀ hR (by lia)
    refine lt_of_le_of_lt (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
    have hR1 : (0 : K) < R ^ (p.natDegree - 1) := by positivity
    have hpow : R ^ (p.natDegree - 1) * R = R ^ p.natDegree := by
      rw [← pow_succ]
      congr 1
      lia
    nlinarith [hbig, hR1, hpow, hcd]
  exact sign_of_dominant hR0 (Nat.lt_succ_self _) (Nat.lt_succ_self _) hcd hdom

/-- Consecutive signed evaluations at negative points yield a root between the
corresponding evaluation magnitudes. -/
theorem exists_isRoot_neg_between_of_signed_evals {p : ℝ[X]} {s₁ s₂ : ℝ}
    (h12 : s₁ < s₂) {j : ℕ}
    (h₁ : 0 < (-1 : ℝ) ^ j * p.eval (-s₁))
    (h₂ : 0 < (-1 : ℝ) ^ (j + 1) * p.eval (-s₂)) :
    ∃ x, s₁ < x ∧ x < s₂ ∧ p.IsRoot (-x) := by
  have hmul : p.eval (-s₂) * p.eval (-s₁) < 0 := by
    rcases neg_one_pow_eq_or ℝ j with hneg | hneg
    · rw [hneg] at h₁
      rw [pow_succ, hneg] at h₂
      nlinarith [h₁, h₂]
    · rw [hneg] at h₁
      rw [pow_succ, hneg] at h₂
      nlinarith [h₁, h₂]
  obtain ⟨c, hc1, hc2, hc0⟩ : ∃ c, -s₂ < c ∧ c < -s₁ ∧ p.IsRoot c :=
    exists_isRoot_between_of_eval_mul_neg (by linarith) hmul
  exact ⟨-c, by linarith, by linarith, by simpa using hc0⟩

/-- Alternating signed evaluations at `d + 1` ordered points imply splitness. -/
theorem splits_of_signs {q : ℝ[X]} {d : ℕ} (hd : q.natDegree = d)
    (x : Fin (d + 1) → ℝ) (hmono : StrictMono x) (σ : Fin (d + 1) → ℕ)
    (hsign : ∀ i, 0 < (-1 : ℝ) ^ (σ i) * q.eval (x i))
    (halt : ∀ i : Fin d, (-1 : ℝ) ^ (σ i.castSucc) = -((-1 : ℝ) ^ (σ i.succ))) :
    q.Splits := by
  have hq : q ≠ 0 := by
    intro hq
    subst q
    have h := hsign 0
    simp at h
  refine splits_of_strict_sign_changes_fin hq hd x (fun i j hij => hmono hij) (fun i => ?_)
  have h₁ := hsign i.castSucc
  have h₂ := hsign i.succ
  have hrel := halt i
  rcases neg_one_pow_eq_or ℝ (σ i.succ) with hB | hB
  · rw [hB] at h₂ hrel
    rw [hrel] at h₁
    nlinarith [h₁, h₂]
  · rw [hB] at h₂ hrel
    rw [hrel] at h₁
    nlinarith [h₁, h₂]

end RealRooted.RootCounting
