import RealRooted.JacobiDeformation.JacobiMomentCompletion

/-!
# Coefficient transport for normalized Jacobi moments

The first lemma is the denominator-cleared generalized-binomial identity used
to normalize the coefficient of `X ^ i` in a shifted Jacobi polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Clearing the endpoint normalization denominator in a shifted-Jacobi
coefficient. -/
theorem choose_mul_risingFactorial_eq_choose_mul_fallingFactorial
    {c : ℝ} (hc : 0 < c) {i j : ℕ} (hij : i ≤ j) :
    Ring.choose ((j : ℝ) + c - 1) (j - i) * risingFactorial c i =
      Ring.choose ((j : ℝ) + c - 1) j * fallingFactorial (j : ℝ) i := by
  let x : ℝ := (j : ℝ) + c - 1
  have hchoose := Ring.choose_smul_choose (R := ℝ) x (n := j) (k := j - i)
    (Nat.sub_le j i)
  have hsub : j - (j - i) = i := by lia
  have harg : x - (j - i : ℕ) = c + i - 1 := by
    dsimp [x]
    rw [Nat.cast_sub hij]
    ring
  rw [hsub, harg] at hchoose
  have hnat : (j.choose (j - i) : ℝ) * (i.factorial : ℝ) =
      fallingFactorial (j : ℝ) i := by
    rw [Nat.choose_symm hij, Nat.cast_choose_eq_descPochhammer_div]
    field_simp [Nat.factorial_ne_zero]
  have hring : Ring.choose (c + i - 1) i * (i.factorial : ℝ) =
      risingFactorial c i := by
    rw [Ring.choose_eq_smul, smul_eq_mul]
    change (i.factorial : ℝ)⁻¹ *
        (descPochhammer ℤ i).smeval (c + i - 1) * (i.factorial : ℝ) =
      risingFactorial c i
    field_simp [Nat.factorial_ne_zero]
    rw [show (descPochhammer ℤ i).smeval (c + i - 1) =
        (descPochhammer ℝ i).eval (c + i - 1) by simp]
    rw [descPochhammer_eval_eq_ascPochhammer]
    congr 2
    push_cast
    ring
  rw [← hring, ← hnat]
  nlinarith [hchoose]

end RealRooted.JacobiDeformation
