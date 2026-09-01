import RealRooted.RootAmplitude.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Minimum root-amplitude bounds

Two routes propagate a lower bound at the smallest finite-sequence amplitude:
one through convexity and one through reciprocal-distance sums.
-/

namespace RealRooted.RootAmplitude

open Finset

noncomputable section

variable (g : ℕ → ℝ)

/-- For a positive strictly increasing convex sequence, every amplitude is at
least the amplitude at its smallest index, under the supplied tail estimates. -/
theorem amp_zero_le (hpos : ∀ i, 0 < g i) (hsm : StrictMono g)
    (hconv : ∀ i, gap g i ≤ gap g (i + 1)) (n : ℕ)
    (htail : ∀ k, k + 1 < n →
      ∏ j ∈ Ico (2 * k + 2) n, (1 + (g (k + 1) - g k) / (g j - g (k + 1)))
        ≤ 1 + (g (k + 1) - g k) / g k) :
    ∀ k, k < n → amp g n 0 ≤ amp g n k := by
  intro k
  induction k with
  | zero => intro _; exact le_refl _
  | succ m ih =>
      intro hm
      exact le_trans (ih (by lia))
        (amp_le_amp_of_convex_tail g hpos hsm hconv n m (by lia) (htail m (by lia)))

/-- `exp (z / (1 + z)) ≤ 1 + z` for nonnegative `z`. -/
theorem exp_div_le_one_add {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (z / (1 + z)) ≤ 1 + z := by
  have hdenom : (0 : ℝ) < 1 + z := by linarith
  have hexp : (0 : ℝ) < Real.exp (z / (1 + z)) := Real.exp_pos _
  have hbound := Real.add_one_le_exp (-(z / (1 + z)))
  rw [show -(z / (1 + z)) + 1 = (1 + z)⁻¹ by field_simp; ring, Real.exp_neg] at hbound
  exact (inv_le_inv₀ hdenom hexp).mp hbound

/-- A reciprocal-distance-sum criterion implies one step of amplitude
monotonicity, without a convexity hypothesis. -/
theorem amp_le_amp_of_sum (hpos : ∀ i, 0 < g i) (hsm : StrictMono g)
    (n k : ℕ) (hk1 : k + 1 < n)
    (hsum : ∑ j ∈ Ico (k + 2) n, 1 / (g j - g (k + 1))
      ≤ 1 / g (k + 1) + ∑ j ∈ range k, 1 / (g (k + 1) - g j)) :
    amp g n k ≤ amp g n (k + 1) := by
  classical
  refine amp_le_amp_of_core g hpos hsm n k hk1 ?_
  have hgk : 0 < g k := hpos k
  have hgk1 : 0 < g (k + 1) := hpos (k + 1)
  set D : ℝ := g (k + 1) - g k with hD
  have hDpos : (0 : ℝ) ≤ D := le_of_lt (sub_pos.mpr (hsm (Nat.lt_succ_self k)))
  have hcurrent : g (k + 1) = g k + D := by
    rw [hD]
    ring
  have hb : ∀ j ∈ range k, 0 < g k - g j := fun y hy =>
    sub_pos.mpr (hsm (Finset.mem_range.mp hy))
  have ha : ∀ j ∈ Ico (k + 2) n, 0 < g j - g (k + 1) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact sub_pos.mpr (hsm (by lia : k + 1 < x))
  have hupper : ∏ j ∈ Ico (k + 2) n, (1 + D / (g j - g (k + 1)))
      ≤ Real.exp (∑ j ∈ Ico (k + 2) n, D / (g j - g (k + 1))) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod ?_ ?_
    · intro j hj
      have hdivision := div_nonneg hDpos (le_of_lt (ha j hj))
      linarith
    · intro j _
      linarith [Real.add_one_le_exp (D / (g j - g (k + 1)))]
  have horigin : Real.exp (D / g (k + 1)) ≤ 1 + D / g k := by
    have hrewrite : D / g (k + 1) = (D / g k) / (1 + D / g k) := by
      rw [hcurrent]
      field_simp
    rw [hrewrite]
    exact exp_div_le_one_add (div_nonneg hDpos (le_of_lt hgk))
  have hlower : Real.exp (∑ j ∈ range k, D / (g (k + 1) - g j))
      ≤ ∏ j ∈ range k, (1 + D / (g k - g j)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod ?_ ?_
    · intro j _
      exact le_of_lt (Real.exp_pos _)
    · intro j hj
      have hbelow := hb j hj
      have hrewrite : D / (g (k + 1) - g j)
          = (D / (g k - g j)) / (1 + D / (g k - g j)) := by
        rw [show g (k + 1) - g j = (g k - g j) + D by rw [hcurrent]; ring]
        field_simp
      rw [hrewrite]
      exact exp_div_le_one_add (div_nonneg hDpos (le_of_lt hbelow))
  have hmiddle : (∑ j ∈ Ico (k + 2) n, D / (g j - g (k + 1)))
      ≤ D / g (k + 1) + ∑ j ∈ range k, D / (g (k + 1) - g j) := by
    have hleft : (∑ j ∈ Ico (k + 2) n, D / (g j - g (k + 1)))
        = D * ∑ j ∈ Ico (k + 2) n, 1 / (g j - g (k + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_one_div])
    have hright : (∑ j ∈ range k, D / (g (k + 1) - g j))
        = D * ∑ j ∈ range k, 1 / (g (k + 1) - g j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_one_div])
    rw [hleft, hright, show D / g (k + 1) = D * (1 / g (k + 1)) by rw [mul_one_div]]
    nlinarith [hsum, hDpos]
  have hexp : Real.exp (∑ j ∈ Ico (k + 2) n, D / (g j - g (k + 1)))
      ≤ Real.exp (D / g (k + 1)) * Real.exp (∑ j ∈ range k, D / (g (k + 1) - g j)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hmiddle
  have horigin_positive : (0 : ℝ) < Real.exp (D / g (k + 1)) := Real.exp_pos _
  have hproduct_nonnegative : (0 : ℝ) ≤ ∏ j ∈ range k, (1 + D / (g k - g j)) := by
    refine Finset.prod_nonneg ?_
    intro j hj
    have hdivision := div_nonneg hDpos (le_of_lt (hb j hj))
    linarith
  calc
    ∏ j ∈ Ico (k + 2) n, (1 + D / (g j - g (k + 1)))
      ≤ Real.exp (∑ j ∈ Ico (k + 2) n, D / (g j - g (k + 1))) := hupper
    _ ≤ Real.exp (D / g (k + 1)) * Real.exp (∑ j ∈ range k, D / (g (k + 1) - g j)) :=
      hexp
    _ ≤ (1 + D / g k) * ∏ j ∈ range k, (1 + D / (g k - g j)) := by
        exact mul_le_mul horigin hlower (le_of_lt (Real.exp_pos _))
          (by
            have hbound := exp_div_le_one_add (div_nonneg hDpos (le_of_lt hgk))
            linarith [horigin, horigin_positive])

/-- A reciprocal-distance-sum criterion at every index makes the smallest
amplitude a lower bound for all finite-sequence amplitudes. -/
theorem amp_zero_le_of_sum (hpos : ∀ i, 0 < g i) (hsm : StrictMono g) (n : ℕ)
    (hsum : ∀ k, k + 1 < n →
      ∑ j ∈ Ico (k + 2) n, 1 / (g j - g (k + 1))
        ≤ 1 / g (k + 1) + ∑ j ∈ range k, 1 / (g (k + 1) - g j)) :
    ∀ k, k < n → amp g n 0 ≤ amp g n k := by
  intro k
  induction k with
  | zero => intro _; exact le_refl _
  | succ m ih =>
      intro hm
      exact le_trans (ih (by lia))
        (amp_le_amp_of_sum g hpos hsm n m (by lia) (hsum m (by lia)))

end

end RealRooted.RootAmplitude
