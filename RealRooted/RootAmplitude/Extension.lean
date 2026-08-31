import RealRooted.RootAmplitude.Minimum

/-!
# Finite extension of root-amplitude sequences

An increasing convex sequence indexed by a finite range can be continued past
its last index by repeating its final gap. This lets global root-amplitude
criteria apply directly to finite root lists.
-/

namespace RealRooted.RootAmplitude

open Finset

noncomputable section

variable (g : ℕ → ℝ) (n : ℕ)

/-- The final gap of the finite part. -/
def lastGap : ℝ := g (n - 1) - g (n - 2)

/-- Continue `g` past `n - 1` by repeating its final gap. -/
def extend : ℕ → ℝ :=
  fun j => if j < n then g j else g (n - 1) + ((j - (n - 1) : ℕ) : ℝ) * lastGap g n

@[simp] theorem extend_of_lt {j : ℕ} (h : j < n) : extend g n j = g j := by
  simp [extend, h]

theorem extend_of_ge {j : ℕ} (h : n ≤ j) :
    extend g n j = g (n - 1) + ((j - (n - 1) : ℕ) : ℝ) * lastGap g n := by
  simp [extend, Nat.not_lt.mpr h]

/-- The extension's gap at `i`, for `i + 1 < n`, is the original gap. -/
theorem gap_extend_of_lt {i : ℕ} (h : i + 1 < n) :
    gap (extend g n) i = gap g i := by
  unfold gap
  rw [extend_of_lt g n h, extend_of_lt g n (by lia)]

/-- At and beyond `i = n - 1` every gap is the final gap. -/
theorem gap_extend_of_ge (hn : 2 ≤ n) {i : ℕ} (h : n - 1 ≤ i) :
    gap (extend g n) i = lastGap g n := by
  unfold gap
  rcases Nat.lt_or_ge i n with hi | hi
  · have hieq : i = n - 1 := by lia
    subst hieq
    rw [extend_of_ge g n (by lia : n ≤ n - 1 + 1),
      extend_of_lt g n (by lia : n - 1 < n)]
    have h1 : (n - 1 + 1 - (n - 1) : ℕ) = 1 := by lia
    rw [h1]
    push_cast
    ring
  · rw [extend_of_ge g n (by lia : n ≤ i + 1), extend_of_ge g n hi]
    have h1 : (i + 1 - (n - 1) : ℕ) = (i - (n - 1)) + 1 := by lia
    rw [h1]
    push_cast
    ring

/-- Convexity is preserved because the new gaps equal the final old gap. -/
theorem gap_mono_extend (hn : 2 ≤ n)
    (hconv : ∀ i, i + 2 < n → gap g i ≤ gap g (i + 1)) :
    ∀ i, gap (extend g n) i ≤ gap (extend g n) (i + 1) := by
  intro i
  rcases Nat.lt_or_ge (i + 2) n with h | h
  · rw [gap_extend_of_lt g n (by lia), gap_extend_of_lt g n (by lia)]
    exact hconv i h
  · rcases Nat.lt_or_ge (i + 1) n with h1 | h1
    · have hi : i = n - 2 := by lia
      subst hi
      rw [gap_extend_of_lt g n (by lia), gap_extend_of_ge g n hn (by lia)]
      unfold gap lastGap
      have : n - 2 + 1 = n - 1 := by lia
      rw [this]
    · rw [gap_extend_of_ge g n hn (by lia), gap_extend_of_ge g n hn (by lia)]

/-- The final gap is positive when the finite part increases. -/
theorem lastGap_pos (hn : 2 ≤ n) (hsm : ∀ i j, i < j → j < n → g i < g j) :
    0 < lastGap g n := by
  unfold lastGap
  have h := hsm (n - 2) (n - 1) (by lia) (by lia)
  linarith

/-- Strict monotonicity is preserved by the finite extension. -/
theorem strictMono_extend (hn : 2 ≤ n)
    (hsm : ∀ i j, i < j → j < n → g i < g j) : StrictMono (extend g n) := by
  refine strictMono_nat_of_lt_succ ?_
  intro j
  have hgap : 0 < gap (extend g n) j := by
    rcases Nat.lt_or_ge (j + 1) n with h | h
    · rw [gap_extend_of_lt g n h]
      unfold gap
      have h' := hsm j (j + 1) (by lia) h
      linarith
    · rw [gap_extend_of_ge g n hn (by lia)]
      exact lastGap_pos g n hn hsm
  unfold gap at hgap
  linarith

/-- Positivity is preserved by the finite extension. -/
theorem extend_pos (hn : 2 ≤ n) (hpos : ∀ i, i < n → 0 < g i)
    (hsm : ∀ i j, i < j → j < n → g i < g j) : ∀ j, 0 < extend g n j := by
  intro j
  rcases Nat.lt_or_ge j n with h | h
  · rw [extend_of_lt g n h]
    exact hpos j h
  · have h0 : 0 < g (n - 1) := hpos (n - 1) (by lia)
    have hL := lastGap_pos g n hn hsm
    have hcast : (0 : ℝ) ≤ ((j - (n - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [extend_of_ge g n h]
    nlinarith

/-- The amplitude is unchanged because it only reads indices below `n`. -/
theorem amp_extend {k : ℕ} (hk : k < n) :
    amp (extend g n) n k = amp g n k := by
  unfold amp
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjn : j < n := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  rw [extend_of_lt g n hk, extend_of_lt g n hjn]

/-- A reciprocal-distance-sum criterion on a finite increasing sequence makes
its smallest amplitude a lower bound for all of its amplitudes. -/
theorem amp_zero_le_of_finite_sum (hn : 2 ≤ n)
    (hpos : ∀ i, i < n → 0 < g i)
    (hsm : ∀ i j, i < j → j < n → g i < g j)
    (hsum : ∀ k, k + 1 < n →
      ∑ j ∈ Finset.Ico (k + 2) n, 1 / (g j - g (k + 1))
        ≤ 1 / g (k + 1) + ∑ j ∈ Finset.range k, 1 / (g (k + 1) - g j)) :
    ∀ k, k < n → amp g n 0 ≤ amp g n k := by
  intro k hk
  have hsum' : ∀ k' : ℕ, k' + 1 < n →
      ∑ j ∈ Finset.Ico (k' + 2) n, 1 / (extend g n j - extend g n (k' + 1))
        ≤ 1 / extend g n (k' + 1)
          + ∑ j ∈ Finset.range k', 1 / (extend g n (k' + 1) - extend g n j) := by
    intro k' hk'
    have hk1 : k' + 1 < n := hk'
    have e1 : ∑ j ∈ Finset.Ico (k' + 2) n, 1 / (extend g n j - extend g n (k' + 1))
        = ∑ j ∈ Finset.Ico (k' + 2) n, 1 / (g j - g (k' + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [extend_of_lt g n hj.2, extend_of_lt g n hk1]
    have e2 : ∑ j ∈ Finset.range k', 1 / (extend g n (k' + 1) - extend g n j)
        = ∑ j ∈ Finset.range k', 1 / (g (k' + 1) - g j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [Finset.mem_range] at hj
      rw [extend_of_lt g n hk1, extend_of_lt g n (by lia : j < n)]
    rw [e1, e2, extend_of_lt g n hk1]
    exact hsum k' hk'
  have h := amp_zero_le_of_sum (extend g n)
    (extend_pos g n hn hpos hsm) (strictMono_extend g n hn hsm) n hsum' k hk
  rwa [amp_extend g n (by lia : 0 < n), amp_extend g n hk] at h

end

end RealRooted.RootAmplitude
