import RealRooted.ThresholdMatrix

open Polynomial

noncomputable section

namespace RealRooted

/-- A zero-aware nonnegative interlacing triple projects to an interlacing
pair consisting of its last entry and the last entry after one digit step. -/
theorem interl_last_digit_step_of_triple
    (a b c : ℝ[X])
    (hseq : IsInterlacingSeq0Nonneg [a, b, c])
    (hreal : ∀ f ∈ [a, b, c], f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    Interl c (X * a + X * b + (1 + X) * c) := by
  have hpair := interl_zipWith_sum_pair_of_2x2_weak
    (n := 3) (row₁ := [0, 0, 1]) (row₂ := [X, X, 1 + X])
    (fs := [a, b, c])
    (by simp) (by simp)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact hasNonnegCoeffs_zero
      · exact hasNonnegCoeffs_zero
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_X
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_X
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one_add_X)
    (by
      intro j₁ j₂ hj
      fin_cases j₁ <;> fin_cases j₂ <;> norm_num at hj <;>
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, List.get_eq_getElem, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          List.getElem_cons_zero, Fin.mk_one, Nat.one_mod, List.getElem_cons_succ,
          Fin.reduceFinMk, Nat.mod_succ] at ⊢
      · intro s t hs ht
        simpa using interl_X_X
      · intro s t hs ht
        simpa using interl_X_X
      · intro s t hs ht
        simp only [mul_one, mul_zero, zero_add]
        rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
          C (s + 1) * X + C (t + 1) by grind]
        exact interl_affine_X (by positivity) (by positivity)
      · intro s t hs ht
        simpa using interl_X_X
      · intro s t hs ht
        simp only [mul_one, mul_zero, zero_add]
        rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
          C (s + 1) * X + C (t + 1) by grind]
        exact interl_affine_X (by positivity) (by positivity)
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
          C (s + 1) * X + C (t + 1) by grind]
        exact interl_affine_self (by positivity))
    (by simp) hseq hreal
  simpa [add_assoc] using hpair

/-- A zero-aware nonnegative interlacing triple projects to an interlacing
pair consisting of its sum and the sum after one digit step. -/
theorem interl_sum_digit_step_of_triple
    (a b c : ℝ[X])
    (hseq : IsInterlacingSeq0Nonneg [a, b, c])
    (hreal : ∀ f ∈ [a, b, c], f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    Interl (a + b + c)
      (((1 + 3 * X) * a + (2 + 2 * X) * b) + (3 + X) * c) := by
  have hpair := interl_zipWith_sum_pair_of_2x2_weak
    (n := 3) (row₁ := [1, 1, 1])
    (row₂ := [1 + 3 * X, 2 + 2 * X, 3 + X])
    (fs := [a, b, c])
    (by simp) (by simp)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
      · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simpa [map_ofNat, add_comm] using
          (hasNonnegCoeffs_affine_linear (a := 3) (b := 1) (by norm_num) (by norm_num))
      · simpa [map_ofNat, add_comm] using
          (hasNonnegCoeffs_affine_linear (a := 2) (b := 2) (by norm_num) (by norm_num))
      · simpa [map_ofNat, add_comm] using
          (hasNonnegCoeffs_affine_linear (a := 1) (b := 3) (by norm_num) (by norm_num)))
    (by
      intro j₁ j₂ hj
      fin_cases j₁ <;> fin_cases j₂ <;> norm_num at hj <;>
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, List.get_eq_getElem, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          List.getElem_cons_zero, Fin.mk_one, Nat.one_mod, List.getElem_cons_succ,
          Fin.reduceFinMk, Nat.mod_succ] at ⊢
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (1 + 3 * X) : ℝ[X]) =
          C (s + 3) * X + C (t + 1) by norm_num [map_ofNat]; ring]
        exact interl_affine_self (by positivity)
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (2 + 2 * X) : ℝ[X]) =
          C (s + 2) * X + C (t + 2) by norm_num [map_ofNat]; ring]
        rw [show (C s * X + C t + (1 + 3 * X) : ℝ[X]) =
          C (s + 3) * X + C (t + 1) by norm_num [map_ofNat]; ring]
        exact interl_affine_linear_affine_linear_of_cross
          (by positivity) (by positivity) (by nlinarith)
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (3 + X) : ℝ[X]) =
          C (s + 1) * X + C (t + 3) by norm_num [map_ofNat]; ring]
        rw [show (C s * X + C t + (1 + 3 * X) : ℝ[X]) =
          C (s + 3) * X + C (t + 1) by norm_num [map_ofNat]; ring]
        exact interl_affine_linear_affine_linear_of_cross
          (by positivity) (by positivity) (by nlinarith)
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (2 + 2 * X) : ℝ[X]) =
          C (s + 2) * X + C (t + 2) by norm_num [map_ofNat]; ring]
        exact interl_affine_self (by positivity)
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (3 + X) : ℝ[X]) =
          C (s + 1) * X + C (t + 3) by norm_num [map_ofNat]; ring]
        rw [show (C s * X + C t + (2 + 2 * X) : ℝ[X]) =
          C (s + 2) * X + C (t + 2) by norm_num [map_ofNat]; ring]
        exact interl_affine_linear_affine_linear_of_cross
          (by positivity) (by positivity) (by nlinarith)
      · intro s t hs ht
        simp only [mul_one]
        rw [show (C s * X + C t + (3 + X) : ℝ[X]) =
          C (s + 1) * X + C (t + 3) by norm_num [map_ofNat]; ring]
        exact interl_affine_self (by positivity))
    (by simp) hseq hreal
  simpa [add_assoc] using hpair

end RealRooted
