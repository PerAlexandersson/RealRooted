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

/-- Positive coefficients make the constant term dominate sufficiently near
the origin. -/
theorem sign_near_zero_of_pos_coeffs {p : K[X]}
    (hpos : ∀ k, k ≤ p.natDegree → 0 < p.coeff k)
    {s : K} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hlt : s * p.eval 1 < p.coeff 0) :
    0 < p.eval (-s) := by
  classical
  have hsum1 : p.eval 1 =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _)]
    simp
  have hbound :
      ∑ k ∈ (Finset.range (p.natDegree + 1)).erase 0,
          |p.coeff k| * s ^ k ≤ s * p.eval 1 := by
    rw [hsum1, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (g := fun k => s * p.coeff k) fun k hk => ?_) ?_
    · have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
      have hkdeg : k ≤ p.natDegree := by
        have hk' := Finset.mem_of_mem_erase hk
        rw [Finset.mem_range] at hk'
        lia
      rw [abs_of_pos (hpos k hkdeg)]
      have hpow : s ^ k ≤ s := by
        calc
          s ^ k = s * s ^ (k - 1) := by
            rw [← pow_succ']
            congr 1
            lia
          _ ≤ s * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hs0.le hs1) hs0.le
          _ = s := by ring
      nlinarith [hpow, hpos k hkdeg]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
      intro k hk _
      have hkdeg : k ≤ p.natDegree := by
        rw [Finset.mem_range] at hk
        lia
      exact le_of_lt (mul_pos hs0 (hpos k hkdeg))
  have hcoeff0 : 0 < p.coeff 0 := hpos 0 (Nat.zero_le _)
  have hdom :
      ∑ k ∈ (Finset.range (p.natDegree + 1)).erase 0,
          |p.coeff k| * s ^ k < |p.coeff 0| * s ^ 0 := by
    rw [abs_of_pos hcoeff0, pow_zero, mul_one]
    exact lt_of_le_of_lt hbound hlt
  simpa using sign_of_dominant hs0 (Nat.lt_succ_self _) (Nat.zero_lt_succ _)
    hcoeff0 hdom

/-- A convenient far-left sign criterion whose size hypothesis uses the
evaluation at one rather than an explicit coefficient sum. -/
theorem sign_at_far_left_of_eval_one_lt {p : K[X]}
    (hpos : ∀ k, k ≤ p.natDegree → 0 < p.coeff k)
    (hd1 : 1 ≤ p.natDegree) {R : K} (hR : 1 ≤ R)
    (hbig : p.eval 1 < p.coeff p.natDegree * R) :
    0 < (-1 : K) ^ p.natDegree * p.eval (-R) := by
  have heval1 : p.eval 1 =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _)]
    simp
  have hlc : 0 < p.coeff p.natDegree := hpos _ le_rfl
  have hsum :
      ∑ k ∈ Finset.range p.natDegree, p.coeff k <
        p.coeff p.natDegree * R := by
    rw [heval1, Finset.sum_range_succ] at hbig
    nlinarith
  exact sign_at_far_left hpos hd1 hR hsum

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

/-- Alternating signed evaluations on a family of intervals yield one root in
each interval. Values outside the index range `i < J` are intentionally left
unspecified. -/
theorem exists_isRoot_neg_family_of_signed_evals {p : ℝ[X]} {J d : ℕ}
    {lo hi : ℕ → ℝ}
    (hlosign : ∀ i, i < J →
      0 < (-1 : ℝ) ^ (i + d) * p.eval (-(lo i)))
    (hhisign : ∀ i, i < J →
      0 < (-1 : ℝ) ^ (i + d + 1) * p.eval (-(hi i)))
    (hloup : ∀ i, i < J → lo i < hi i) :
    ∃ x : ℕ → ℝ, ∀ i, i < J →
      lo i < x i ∧ x i < hi i ∧ p.IsRoot (-(x i)) := by
  classical
  have hroot : ∀ i : ℕ, ∃ x : ℝ, i < J →
      lo i < x ∧ x < hi i ∧ p.IsRoot (-x) := by
    intro i
    by_cases hiJ : i < J
    · obtain ⟨x, hxlo, hxhi, hxroot⟩ :=
        exists_isRoot_neg_between_of_signed_evals
          (hloup i hiJ) (hlosign i hiJ) (hhisign i hiJ)
      exact ⟨x, fun _ => ⟨hxlo, hxhi, hxroot⟩⟩
    · exact ⟨0, fun hiJ' => (hiJ hiJ').elim⟩
  choose x hx using hroot
  exact ⟨x, hx⟩

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
