import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Laguerre's theorem on multiplier sequences

If `φ` is a real polynomial whose zeros are all real and nonpositive, then
`k ↦ φ(k)` is a multiplier sequence.  It is a PF multiplier sequence when, in
addition, the leading coefficient of `φ` is nonnegative.

The basic case is the shifted Euler diagonal `k ↦ k + r` with real `r ≥ 0`.
Its Jensen polynomials factor as

```text
sum_k choose(n,k) (k + r) x^k = r (1 + x)^n + n x (1 + x)^(n-1)
                              = (1 + x)^(n-1) ((n + r) x + r),
```

so they are PF, and the Jensen criterion applies.  The general polynomial
case follows by factoring `φ = c ∏ (X - ρ_i)`, with every `ρ_i ≤ 0`, and using
closure of multiplier sequences under products.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The diagonal operator of `k ↦ k + r` is the positive Euler pencil
`p ↦ X p' + r p`. -/
theorem diagonalOperator_natCast_add (r : ℝ) (p : ℝ[X]) :
    diagonalOperator (fun k => (k : ℝ) + r) p = X * derivative p + C r * p := by
  rw [eulerOperator_eq_diagonalOperator_natCast]
  ext k
  simp only [coeff_diagonalOperator, coeff_add, coeff_C_mul]
  ring

/-- **The shifted Euler diagonal `k ↦ k + r`, for real `r ≥ 0`, is a PF
multiplier sequence.** -/
theorem isPFMultiplierSequence_natCast_add {r : ℝ} (hr : 0 ≤ r) :
    IsPFMultiplierSequence (fun k => (k : ℝ) + r) := by
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  intro n
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  have hnn : HasNonnegCoeffs (diagonalOperator (fun k => (k : ℝ) + r) ((X + 1) ^ n)) := by
    intro k
    rw [coeff_diagonalOperator]
    have hcoeff : 0 ≤ ((X + 1 : ℝ[X]) ^ n).coeff k := by
      rw [add_pow, finsetSum_coeff]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [one_pow, mul_one, ← Nat.cast_comm, ← C_eq_natCast, coeff_C_mul, coeff_X_pow]
      split_ifs <;> positivity
    positivity
  refine IsPFPolynomial.of_realRooted_nonneg hnn ?_
  rw [diagonalOperator_natCast_add]
  rcases n with _ | m
  · simp [Splits.C r]
  · have hfac : X * derivative ((X + 1 : ℝ[X]) ^ (m + 1)) + C r * (X + 1) ^ (m + 1) =
        (X + C 1) ^ m * (C ((m : ℝ) + 1 + r) * X + C r) := by
      rw [← C_1, derivative_X_add_C_pow]
      simp only [Nat.add_sub_cancel, map_add, map_one, map_natCast]
      push_cast
      ring
    rw [hfac]
    exact ((Splits.X_add_C 1).pow m).mul (Splits.of_natDegree_le_one (natDegree_linear_le))

private theorem isPFMultiplierSequence_prod_sub_of_nonpos :
    ∀ (s : Multiset ℝ), (∀ a ∈ s, a ≤ 0) →
      IsPFMultiplierSequence (fun k => (s.map (fun a => (k : ℝ) - a)).prod) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      intro _
      simpa using isPFMultiplierSequence_one_sequence
  | cons a s ih =>
      intro hs
      have ha : 0 ≤ -a := by linarith [hs a (Multiset.mem_cons_self a s)]
      have hs' := ih fun b hb => hs b (Multiset.mem_cons_of_mem hb)
      simpa [Multiset.map_cons, Multiset.prod_cons, sub_eq_add_neg] using
        (isPFMultiplierSequence_natCast_add ha).mul hs'

private theorem eval_natCast_eq_leadingCoeff_mul_prod {φ : ℝ[X]} (hφ : φ.Splits) (k : ℕ) :
    φ.eval (k : ℝ) = φ.leadingCoeff * (φ.roots.map (fun a => (k : ℝ) - a)).prod := by
  conv_lhs => rw [hφ.eq_prod_roots]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun a _ => ?_
  simp

/-- **Laguerre's theorem, PF form.**  If `φ` splits with only nonpositive
roots and a nonnegative leading coefficient, then `k ↦ φ(k)` is a PF
multiplier sequence. -/
theorem isPFMultiplierSequence_eval_of_roots_nonpos {φ : ℝ[X]} (hφ : φ.Splits)
    (hroots : ∀ r ∈ φ.roots, r ≤ 0) (hlead : 0 ≤ φ.leadingCoeff) :
    IsPFMultiplierSequence (fun k => φ.eval (k : ℝ)) := by
  simpa [eval_natCast_eq_leadingCoeff_mul_prod hφ] using
    (isPFMultiplierSequence_prod_sub_of_nonpos φ.roots hroots).const_mul hlead

/-- **Laguerre's theorem.**  If `φ` splits with only nonpositive roots, then
`k ↦ φ(k)` is a multiplier sequence. -/
theorem isMultiplierSequence_eval_of_roots_nonpos {φ : ℝ[X]} (hφ : φ.Splits)
    (hroots : ∀ r ∈ φ.roots, r ≤ 0) :
    IsMultiplierSequence (fun k => φ.eval (k : ℝ)) := by
  have h := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
    (isPFMultiplierSequence_prod_sub_of_nonpos φ.roots hroots)).1
  simpa [eval_natCast_eq_leadingCoeff_mul_prod hφ] using h.const_mul φ.leadingCoeff

end RealRooted
