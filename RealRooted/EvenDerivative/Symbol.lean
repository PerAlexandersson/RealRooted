module

public import RealRooted.EvenDerivative.Basic
public import RealRooted.Hermite.Poulain

/-!
# The test polynomial as a constant-coefficient differential operator

For a coefficient sequence with finite support `c k = 0` for `k > M`, the test polynomial is
`p_N = h(D) uᴺ` with the signed symbol `h(w) = ∑_{k ≤ M} (-1)ᵏ cₖ w^{2k} = C(-w²)`, where
`C(t) = ∑ cₖ tᵏ`.  By the Hermite--Poulain theorem `p_N` is real-rooted for every `N` as soon as
the symbol `h` is real-rooted, which is the polynomial case of the all-degree criterion.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

variable {c : ℕ → ℝ} {M : ℕ}

/-- The signed symbol `h(w) = ∑_{k ≤ M} (-1)ᵏ cₖ w^{2k}` of the test polynomials,
so that `p_N = h(D) uᴺ`. -/
def evenDerivativeSymbol (c : ℕ → ℝ) (M : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (M + 1), C ((-1) ^ k * c k) * X ^ (2 * k)

private theorem applyAsDifferentialOperator_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (g : ℝ[X]) : HermitePoulain.applyAsDifferentialOperator (∑ i ∈ s, f i) g =
      ∑ i ∈ s, HermitePoulain.applyAsDifferentialOperator (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HermitePoulain.applyAsDifferentialOperator]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, HermitePoulain.applyAsDifferentialOperator_add, ih,
      Finset.sum_insert hi]

/-- The extended sum for the test polynomial: terms with `2k > N` vanish. -/
private theorem evenDerivativeTest_eq_sum_range {N B : ℕ} (hB : N / 2 < B) :
    evenDerivativeTest c N = ∑ k ∈ Finset.range B,
      C ((-1) ^ k * c k * (N.descFactorial (2 * k) : ℝ)) * X ^ (N - 2 * k) := by
  refine Finset.sum_subset (Finset.range_mono (by lia)) fun k hk hk' => ?_
  simp only [Finset.mem_range, not_lt] at hk hk'
  simp [Nat.descFactorial_eq_zero_iff_lt.2 (show N < 2 * k by lia)]

/-- For a finitely supported coefficient sequence, the test polynomial is the constant-coefficient
differential operator with the signed symbol applied to `uᴺ`. -/
theorem evenDerivativeTest_eq_applyAsDifferentialOperator (hM : ∀ k, M < k → c k = 0) (N : ℕ) :
    evenDerivativeTest c N =
      HermitePoulain.applyAsDifferentialOperator (evenDerivativeSymbol c M) (X ^ N) := by
  rw [evenDerivativeSymbol, applyAsDifferentialOperator_sum,
    evenDerivativeTest_eq_sum_range (B := N / 2 + M + 1) (by lia)]
  have h1 : ∀ k ∈ Finset.range (M + 1), HermitePoulain.applyAsDifferentialOperator
      (C ((-1) ^ k * c k) * X ^ (2 * k)) (X ^ N) =
      C ((-1) ^ k * c k * (N.descFactorial (2 * k) : ℝ)) * X ^ (N - 2 * k) := by
    intro k _
    rw [C_mul_X_pow_eq_monomial, HermitePoulain.applyAsDifferentialOperator_monomial,
      iterate_derivative_X_pow_eq_smul, smul_eq_C_mul]
    simp only [C_mul]
    ring
  rw [Finset.sum_congr rfl h1]
  symm
  refine Finset.sum_subset (Finset.range_mono (by lia)) fun k hk hk' => ?_
  simp only [Finset.mem_range, not_lt] at hk hk'
  simp [hM k (by lia)]

/-- **Polynomial case of the all-degree criterion.**  If `c` has finite support and the signed
symbol `∑ₖ (-1)ᵏ cₖ w^{2k}` is real-rooted, then every test polynomial `p_N` is real-rooted
(Hermite--Poulain). -/
theorem splits_evenDerivativeTest_of_splits_symbol (hc0 : c 0 = 1) (hM : ∀ k, M < k → c k = 0)
    (hs : (evenDerivativeSymbol c M).Splits) (N : ℕ) : (evenDerivativeTest c N).Splits := by
  have hsymm : evenDerivativeSymbol c M ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 0) h
    simp only [evenDerivativeSymbol, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (by simp)] at this
    simp [hc0] at this
  rcases HermitePoulain.applyAsDifferentialOperator_eq_zero_or_splits (f := evenDerivativeSymbol c
    M)
    (g := X ^ N) ⟨hsymm, hs⟩ ⟨pow_ne_zero N X_ne_zero, by simp⟩ with h | h
  · exact absurd ((evenDerivativeTest_eq_applyAsDifferentialOperator hM N).trans h)
      (evenDerivativeTest_ne_zero hc0 N)
  · rwa [← evenDerivativeTest_eq_applyAsDifferentialOperator hM N] at h

end RealRooted
