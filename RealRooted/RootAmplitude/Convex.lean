import RealRooted.RootAmplitude.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
# Convex finite sequences and root amplitudes

Convexity supplies the distance pairing that proves monotonicity of finite
root-amplitude products.
-/

namespace RealRooted.RootAmplitude

open Finset

noncomputable section

variable (g : ℕ → ℝ)

/-- The consecutive-gap sequence. -/
def gap (i : ℕ) : ℝ :=
  g (i + 1) - g i

/-- Convexity on consecutive gaps makes the gap sequence monotone. -/
theorem monotone_gap (hconv : ∀ i, gap g i ≤ gap g (i + 1)) : Monotone (gap g) :=
  monotone_nat_of_le_succ hconv

/-- A finite block of consecutive gaps telescopes. -/
theorem sum_gap (a j : ℕ) :
    ∑ t ∈ range j, gap g (a + t) = g (a + j) - g a := by
  induction j with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, gap]
      have hrewrite : a + (m + 1) = a + m + 1 := by lia
      rw [hrewrite]
      ring

/-- Convexity dominates the distance below an index by the corresponding
distance above its successor. -/
theorem dist_below_le_dist_above (hconv : ∀ i, gap g i ≤ gap g (i + 1))
    {k j : ℕ} (hj : j ≤ k) :
    g k - g (k - j) ≤ g (k + 1 + j) - g (k + 1) := by
  have hmono := monotone_gap g hconv
  have hleft : ∑ t ∈ range j, gap g (k - j + t) = g k - g (k - j) := by
    rw [sum_gap]
    congr 2
    lia
  have hright : ∑ t ∈ range j, gap g (k + 1 + t) = g (k + 1 + j) - g (k + 1) := by
    rw [sum_gap]
  rw [← hleft, ← hright]
  refine Finset.sum_le_sum ?_
  intro t _
  exact hmono (by lia)

/-- Each positive-distance factor is at least one. -/
theorem one_le_one_add_div {D x : ℝ} (hD : 0 ≤ D) (hx : 0 < x) :
    1 ≤ 1 + D / x := by
  have hdivision : 0 ≤ D / x := div_nonneg hD (le_of_lt hx)
  linarith

/-- If positive denominator families admit an injective distance-decreasing
matching, their normalized-distance products are ordered in the same direction. -/
theorem prod_one_add_div_le_of_inj {ι κ : Type*}
    {D : ℝ} (hD : 0 ≤ D) (A : Finset κ) (B : Finset ι) (a : κ → ℝ) (b : ι → ℝ)
    (hb : ∀ y ∈ B, 0 < b y) (ha : ∀ x ∈ A, 0 < a x)
    (φ : κ → ι) (hmaps : ∀ x ∈ A, φ x ∈ B)
    (hinjective : ∀ x ∈ A, ∀ y ∈ A, φ x = φ y → x = y)
    (hdominates : ∀ x ∈ A, b (φ x) ≤ a x) :
    ∏ x ∈ A, (1 + D / a x) ≤ ∏ y ∈ B, (1 + D / b y) := by
  classical
  have hstep : ∏ x ∈ A, (1 + D / a x) ≤ ∏ x ∈ A, (1 + D / b (φ x)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro x hx
      have hone := one_le_one_add_div hD (ha x hx)
      linarith
    · intro x hx
      have hbx : 0 < b (φ x) := hb _ (hmaps x hx)
      have hax : 0 < a x := ha x hx
      have hdivision : D / a x ≤ D / b (φ x) := by
        apply div_le_div_of_nonneg_left hD hbx (hdominates x hx)
      linarith
  have himage : ∏ x ∈ A, (1 + D / b (φ x)) = ∏ y ∈ A.image φ, (1 + D / b y) :=
    (Finset.prod_image (f := fun y => 1 + D / b y) hinjective).symm
  have hsubset : A.image φ ⊆ B := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmaps x hx
  have hrest : ∏ y ∈ A.image φ, (1 + D / b y) ≤ ∏ y ∈ B, (1 + D / b y) := by
    have hone : (1 : ℝ) ≤ ∏ y ∈ B \ A.image φ, (1 + D / b y) := by
      calc
        (1 : ℝ) = ∏ _y ∈ B \ A.image φ, (1 : ℝ) := by simp
        _ ≤ ∏ y ∈ B \ A.image φ, (1 + D / b y) := by
            refine Finset.prod_le_prod (fun _ _ => zero_le_one) ?_
            intro y hy
            exact one_le_one_add_div hD (hb y (Finset.mem_sdiff.mp hy).1)
    have hnonnegative : (0 : ℝ) ≤ ∏ y ∈ A.image φ, (1 + D / b y) := by
      refine Finset.prod_nonneg ?_
      intro y hy
      have hone := one_le_one_add_div hD (hb y (hsubset hy))
      linarith
    rw [← Finset.prod_sdiff hsubset]
    nlinarith [hone, hnonnegative]
  rw [himage] at hstep
  exact le_trans hstep hrest

/-- Amplitude monotonicity from convexity when there are enough lower indices
to pair every upper index. -/
theorem amp_le_amp_of_convex (hpos : ∀ i, 0 < g i) (hsm : StrictMono g)
    (hconv : ∀ i, gap g i ≤ gap g (i + 1))
    (n k : ℕ) (hk1 : k + 1 < n) (hcount : n ≤ 2 * k + 2) :
    amp g n k ≤ amp g n (k + 1) := by
  classical
  refine amp_le_amp_of_core g hpos hsm n k hk1 ?_
  have hDpos : (0 : ℝ) ≤ g (k + 1) - g k :=
    le_of_lt (sub_pos.mpr (hsm (Nat.lt_succ_self k)))
  have hb : ∀ y ∈ range k, 0 < g k - g y := by
    intro y hy
    exact sub_pos.mpr (hsm (Finset.mem_range.mp hy))
  have ha : ∀ x ∈ Ico (k + 2) n, 0 < g x - g (k + 1) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact sub_pos.mpr (hsm (by lia : k + 1 < x))
  have hmain : ∏ j ∈ Ico (k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
      ≤ ∏ j ∈ range k, (1 + (g (k + 1) - g k) / (g k - g j)) := by
    refine prod_one_add_div_le_of_inj hDpos (Ico (k + 2) n) (range k)
      (fun j => g j - g (k + 1)) (fun j => g k - g j) hb ha
      (fun j => 2 * k + 1 - j) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range]
      lia
    · intro x hx y hy hxy
      rw [Finset.mem_Ico] at hx hy
      lia
    · intro x hx
      rw [Finset.mem_Ico] at hx
      obtain ⟨t, hxt, htk⟩ : ∃ t, x = k + 1 + t ∧ t ≤ k :=
        ⟨x - k - 1, by lia, by lia⟩
      subst hxt
      have hindex : 2 * k + 1 - (k + 1 + t) = k - t := by lia
      rw [hindex]
      exact dist_below_le_dist_above g hconv htk
  have hRbelow_positive :
      (0 : ℝ) < ∏ j ∈ range k, (1 + (g (k + 1) - g k) / (g k - g j)) := by
    refine Finset.prod_pos ?_
    intro j hj
    have hone := one_le_one_add_div hDpos (hb j hj)
    linarith
  have hone : (1 : ℝ) ≤ 1 + (g (k + 1) - g k) / g k :=
    one_le_one_add_div hDpos (hpos k)
  nlinarith [hmain, hRbelow_positive, hone]

/-- Amplitude monotonicity from convexity with an explicit bound for the
unpaired upper tail. -/
theorem amp_le_amp_of_convex_tail (hpos : ∀ i, 0 < g i) (hsm : StrictMono g)
    (hconv : ∀ i, gap g i ≤ gap g (i + 1))
    (n k : ℕ) (hk1 : k + 1 < n)
    (htail : ∏ j ∈ Ico (2 * k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
      ≤ 1 + (g (k + 1) - g k) / g k) :
    amp g n k ≤ amp g n (k + 1) := by
  classical
  rcases le_or_gt n (2 * k + 2) with hle | hgt
  · exact amp_le_amp_of_convex g hpos hsm hconv n k hk1 hle
  refine amp_le_amp_of_core g hpos hsm n k hk1 ?_
  have hDpos : (0 : ℝ) ≤ g (k + 1) - g k :=
    le_of_lt (sub_pos.mpr (hsm (Nat.lt_succ_self k)))
  have hb : ∀ y ∈ range k, 0 < g k - g y := by
    intro y hy
    exact sub_pos.mpr (hsm (Finset.mem_range.mp hy))
  have ha : ∀ x ∈ Ico (k + 2) n, 0 < g x - g (k + 1) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact sub_pos.mpr (hsm (by lia : k + 1 < x))
  have hsplit : ∏ j ∈ Ico (k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
      = (∏ j ∈ Ico (k + 2) (2 * k + 2),
          (1 + (g (k + 1) - g k) / (g j - g (k + 1))))
        * ∏ j ∈ Ico (2 * k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1))) :=
    (prod_Ico_consecutive _ (by lia) (by lia)).symm
  have hpair : ∏ j ∈ Ico (k + 2) (2 * k + 2),
      (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
      ≤ ∏ j ∈ range k, (1 + (g (k + 1) - g k) / (g k - g j)) := by
    refine prod_one_add_div_le_of_inj hDpos (Ico (k + 2) (2 * k + 2)) (range k)
      (fun j => g j - g (k + 1)) (fun j => g k - g j) hb
      (fun x hx => ha x (by rw [Finset.mem_Ico] at hx ⊢; lia))
      (fun j => 2 * k + 1 - j) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range]
      lia
    · intro x hx y hy hxy
      rw [Finset.mem_Ico] at hx hy
      lia
    · intro x hx
      rw [Finset.mem_Ico] at hx
      obtain ⟨t, hxt, htk⟩ : ∃ t, x = k + 1 + t ∧ t ≤ k :=
        ⟨x - k - 1, by lia, by lia⟩
      subst hxt
      have hindex : 2 * k + 1 - (k + 1 + t) = k - t := by lia
      rw [hindex]
      exact dist_below_le_dist_above g hconv htk
  have hpaired_nonnegative : (0 : ℝ) ≤ ∏ j ∈ Ico (k + 2) (2 * k + 2),
      (1 + (g (k + 1) - g k) / (g j - g (k + 1))) := by
    refine Finset.prod_nonneg ?_
    intro j hj
    have hone := one_le_one_add_div hDpos (ha j (by rw [Finset.mem_Ico] at hj ⊢; lia))
    linarith
  have htail_nonnegative : (0 : ℝ) ≤ ∏ j ∈ Ico (2 * k + 2) n,
      (1 + (g (k + 1) - g k) / (g j - g (k + 1))) := by
    refine Finset.prod_nonneg ?_
    intro j hj
    have hone := one_le_one_add_div hDpos (ha j (by rw [Finset.mem_Ico] at hj ⊢; lia))
    linarith
  have horigin_nonnegative : (0 : ℝ) ≤ 1 + (g (k + 1) - g k) / g k := by
    have hone := one_le_one_add_div hDpos (hpos k)
    linarith
  rw [hsplit]
  calc
    (∏ j ∈ Ico (k + 2) (2 * k + 2), (1 + (g (k + 1) - g k) / (g j - g (k + 1))))
        * ∏ j ∈ Ico (2 * k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
      ≤ (∏ j ∈ range k, (1 + (g (k + 1) - g k) / (g k - g j)))
        * (1 + (g (k + 1) - g k) / g k) := by
        exact mul_le_mul hpair htail htail_nonnegative
          (Finset.prod_nonneg (fun j hj => by
            have hone := one_le_one_add_div hDpos (hb j hj)
            linarith))
    _ = (1 + (g (k + 1) - g k) / g k)
        * ∏ j ∈ range k, (1 + (g (k + 1) - g k) / (g k - g j)) := by ring

end

end RealRooted.RootAmplitude
