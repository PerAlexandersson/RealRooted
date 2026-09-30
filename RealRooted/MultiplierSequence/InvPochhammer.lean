import RealRooted.Laguerre.Roots
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# The multiplier sequences `1 / (α)_k` and `1 / k!`

For real `α > 0`, the reciprocal rising factorials `γ_k = 1 / (α)_k` form a
PF multiplier sequence.  After clearing the denominator `(α)_n`, the Jensen
polynomial of `γ` is the sign-reversed generalized Laguerre polynomial

```text
(α)_n * sum_k choose(n,k) x^k / (α)_k = sum_k choose(n,k) (α+k)_{n-k} x^k
                                      = generalizedLaguerre n (α - 1),
```

which is PF for `α - 1 ≥ -1`.  The case `α = 1` is `γ_k = 1 / k!`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Jensen polynomial of `k ↦ 1 / (α)_k`, scaled by `(α)_n`, is the
sign-reversed generalized Laguerre polynomial with parameter `α - 1`. -/
theorem C_mul_jensenPolynomial_inv_ascPochhammer {α : ℝ} (hα : 0 < α) (n : ℕ) :
    C ((ascPochhammer ℝ n).eval α) *
        jensenPolynomial n (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) =
      generalizedLaguerre n (α - 1) := by
  ext j
  rw [coeff_C_mul, jensenPolynomial, generalizedLaguerre, finsetSum_coeff,
    finsetSum_coeff]
  simp only [coeff_monomial, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (fun h => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using h)]
      simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (fun h => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using h)]
      simp)]
  by_cases hj : j ≤ n
  · have hsplit := congrArg (eval α) (ascPochhammer_mul ℝ j (n - j))
    rw [Nat.add_sub_cancel' hj, eval_mul, eval_comp, eval_add, eval_X,
      eval_natCast] at hsplit
    have hpos : (ascPochhammer ℝ j).eval α ≠ 0 := (ascPochhammer_pos j α hα).ne'
    simp only [↓reduceIte]
    rw [← hsplit, show α - 1 + (j : ℝ) + 1 = α + j by ring]
    field_simp
  · have hlt : n < j := Nat.lt_of_not_ge hj
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- **The reciprocal rising factorials `1 / (α)_k`, for `α > 0`, form a PF
multiplier sequence.** -/
theorem isPFMultiplierSequence_inv_ascPochhammer {α : ℝ} (hα : 0 < α) :
    IsPFMultiplierSequence (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) := by
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  intro n
  have hpos : 0 < (ascPochhammer ℝ n).eval α := ascPochhammer_pos n α hα
  have hα1 : -1 ≤ α - 1 := by linarith
  have heq : jensenPolynomial n (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) =
      C ((ascPochhammer ℝ n).eval α)⁻¹ * generalizedLaguerre n (α - 1) := by
    rw [← C_mul_jensenPolynomial_inv_ascPochhammer hα n, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ hpos.ne', C_1, one_mul]
  rw [heq]
  exact IsPFPolynomial.of_realRooted_nonneg
    (nonnegCoeffs_C_mul (inv_pos.mpr hpos).le
      (generalizedLaguerre_hasNonnegCoeffs n hα1))
    ((generalizedLaguerre_splits n hα1).C_mul _)

/-- **The reciprocal factorials `1 / k!` form a PF multiplier sequence.** -/
theorem isPFMultiplierSequence_inv_factorial :
    IsPFMultiplierSequence (fun k => ((k.factorial : ℝ))⁻¹) := by
  simpa [ascPochhammer_eval_one] using
    isPFMultiplierSequence_inv_ascPochhammer (α := 1) one_pos

/-- The reciprocal factorials form a multiplier sequence. -/
theorem isMultiplierSequence_inv_factorial :
    IsMultiplierSequence (fun k => ((k.factorial : ℝ))⁻¹) :=
  (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
    isPFMultiplierSequence_inv_factorial).1

end RealRooted
