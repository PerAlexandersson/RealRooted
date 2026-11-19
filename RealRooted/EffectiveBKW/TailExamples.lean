module

public import RealRooted.EffectiveBKW.Tail
public import RealRooted.EffectiveBKW.QuadraticInverse
import Mathlib.Tactic.NormNum

/-!
# Effective BKW tail regressions

The recommended Phase 0 path-cube certificate has `q = 17/20`, `e = 2`, and cutoff 59.
The exact values below are copied from `certificate_wide.json`, not rounded approximations.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.TailExamples

/-- Numerator weights of the recommended Phase 0 certificate. -/
noncomputable def pilotWeights : List ℝ := [1, 8 / 5, 3 / 5, 1 / 2]

/-- The exact pilot tail immediately before the cutoff. -/
theorem pilot_tail_58 :
    tail (17 / 20) pilotWeights 2 58 =
      7447021886507917545941771384239348772718079502573696809268327732720269913269 /
        64851834634135142400000000000000000000000000000000000000000000000000000000000 := by
  rw [tail_two_eq (by norm_num) (by norm_num)]
  norm_num [pilotWeights, Finset.sum_range_succ, List.getD]

/-- The exact pilot tail at the cutoff. -/
theorem pilot_tail_59 :
    tail (17 / 20) pilotWeights 2 59 =
      1028294309410338232276414711571432496946441809535427128153278001170256834040491 /
        10376293541461622784000000000000000000000000000000000000000000000000000000000000 := by
  rw [tail_two_eq (by norm_num) (by norm_num)]
  norm_num [pilotWeights, Finset.sum_range_succ, List.getD]

/-- The cutoff crosses the amplitude threshold between rows 58 and 59. -/
theorem pilot_cutoff :
    (1 / 10 : ℝ) ≤ tail (17 / 20) pilotWeights 2 58 ∧
      tail (17 / 20) pilotWeights 2 59 < 1 / 10 := by
  rw [pilot_tail_58, pilot_tail_59]
  norm_num

/-- The cutoff inequality propagates to every subsequent row. -/
theorem pilot_tail_lt {n : ℕ} (hn : 59 ≤ n) :
    tail (17 / 20) pilotWeights 2 n < 1 / 10 := by
  apply tail_lt_of_le (by norm_num) (by norm_num) pilotWeights _ 2 pilot_cutoff.2 hn
  intro j
  rcases j with _ | _ | _ | _ | j <;> norm_num [pilotWeights, List.getD]

/-- A constant cofactor has no tail after the numerator has been included. -/
example : tail (1 / 2) [1] 0 0 = 0 := by
  rw [tail_eq_closedForm (by norm_num) (by norm_num)]
  norm_num [majorantCoeff, Finset.sum_range_succ, List.getD]

/-- Natural subtraction keeps all terms when a numerator index exceeds the cutoff. -/
example : tail (1 / 2) [1, 0, 0, 2] 0 0 = 2 := by
  rw [tail_eq_closedForm (by norm_num) (by norm_num)]
  norm_num [majorantCoeff, Finset.sum_range_succ, List.getD]

/-- The first nontrivial inverse coefficient agrees with the quadratic recurrence. -/
example (a b : ℝ) : PowerSeries.coeff 2 (quadraticInverse a b) = 4 * a ^ 2 - b := by
  rw [coeff_quadraticInverse_add_two a b 0]
  simp
  ring

/-- The pilot tail simplifies to a single arithmetic-geometric expression. -/
theorem pilot_tail_succ (s : ℕ) :
    tail (17 / 20) pilotWeights 2 (s + 1) =
      (17 / 20 : ℝ) ^ s * (66723 * (s : ℝ) + 556765) / 3600 := by
  rw [tail_two_eq (by norm_num) (by norm_num)]
  have h₁ : s + 1 + 2 - 1 = s + 2 := by lia
  have h₂ : s + 1 + 2 - 2 = s + 1 := by lia
  have h₃ : s + 1 + 2 - 3 = s := by lia
  norm_num [pilotWeights, Finset.sum_range_succ, List.getD, h₁, h₂, h₃]
  simp only [pow_add, pow_one]
  ring

/-- A kernel-only arithmetic benchmark for 100 denominator-cleared pilot tail inequalities. -/
example : (List.range 100).all (fun k ↦ decide
    (17 ^ (k + 58) * (66723 * (k + 58) + 556765) < 360 * 20 ^ (k + 58))) = true := by
  decide +kernel

end RealRooted.EffectiveBKW.TailExamples
