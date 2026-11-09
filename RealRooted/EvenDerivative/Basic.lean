module

public import RealRooted.Basic.Coefficients
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.PFPolynomial
import RealRooted.ClassicalHurwitzMatrix.Stability.HermiteBiehler
import RealRooted.Derivative.Algebra

/-!
# Even-derivative operators and their monomial tests

For a coefficient sequence `c` we study the operator
`T_c f = ∑ₖ cₖ xᵏ f^{(2k)}`, multiplication by `xᵏ` being applied after differentiation, and its
degree-`N` test polynomial `p_N(z) = ∑_{k ≤ N/2} (-1)ᵏ cₖ (N)_{2k} z^{N-2k}`.

This file contains the elementary algebra: the image of a monomial, the relation
`T_c(uᴺ)(-z²) = (-1)ᴺ zᴺ p_N(z)` (folding), the degree and leading coefficient of `T_c f`
for `c 0 = 1`, nonnegativity of coefficients, and the lower-degree caps
`p_N^{(N-n)} = (N)_{N-n} p_n`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The even-derivative operator `T_c f = ∑ₖ cₖ xᵏ f^{(2k)}`.  The sum is cut off at
`natDegree f / 2`, beyond which `f^{(2k)} = 0`. -/
def evenDerivativeOperator (c : ℕ → ℝ) (f : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (f.natDegree / 2 + 1), C (c k) * X ^ k * derivative^[2 * k] f

/-- The degree-`N` test polynomial `p_N(z) = ∑_{k ≤ N/2} (-1)ᵏ cₖ (N)_{2k} z^{N-2k}` of the
even-derivative operator with coefficients `c`. -/
def evenDerivativeTest (c : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N / 2 + 1),
    C ((-1) ^ k * c k * (N.descFactorial (2 * k) : ℝ)) * X ^ (N - 2 * k)

variable {c : ℕ → ℝ}

/-- The cutoff in `evenDerivativeOperator` may be replaced by any larger bound. -/
theorem evenDerivativeOperator_eq_sum_range {f : ℝ[X]} {m : ℕ} (hm : f.natDegree / 2 < m) :
    evenDerivativeOperator c f =
      ∑ k ∈ Finset.range m, C (c k) * X ^ k * derivative^[2 * k] f := by
  refine Finset.sum_subset (Finset.range_mono (by lia)) fun k hk hk' => ?_
  simp only [Finset.mem_range, not_lt] at hk hk'
  simp [iterate_derivative_eq_zero (show f.natDegree < 2 * k by lia)]

@[simp] theorem evenDerivativeOperator_zero : evenDerivativeOperator c 0 = 0 := by
  simp [evenDerivativeOperator]

/-- `T_c` commutes with multiplication by a nonzero constant. -/
theorem evenDerivativeOperator_C_mul {a : ℝ} (ha : a ≠ 0) (f : ℝ[X]) :
    evenDerivativeOperator c (C a * f) = C a * evenDerivativeOperator c f := by
  rw [evenDerivativeOperator, evenDerivativeOperator, natDegree_C_mul ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_C_mul]
  ring

/-- `T_c` as a real-linear map on polynomials. -/
def evenDerivativeLinearMap (c : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := evenDerivativeOperator c
  map_add' f g := by
    have hm : (f + g).natDegree / 2 < f.natDegree + g.natDegree + 1 := by
      have := natDegree_add_le f g
      lia
    rw [evenDerivativeOperator_eq_sum_range hm, evenDerivativeOperator_eq_sum_range
      (f := f) (m := f.natDegree + g.natDegree + 1) (by lia),
      evenDerivativeOperator_eq_sum_range (f := g) (m := f.natDegree + g.natDegree + 1) (by lia),
      ← Finset.sum_add_distrib]
    have hder : ∀ k, derivative^[k] (f + g) = derivative^[k] f + derivative^[k] g := fun k =>
      iterate_map_add (derivative (R := ℝ)).toAddMonoidHom k f g
    simp [hder, mul_add]
  map_smul' a f := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · simpa [Polynomial.smul_eq_C_mul] using evenDerivativeOperator_C_mul (c := c) ha f

@[simp] theorem evenDerivativeLinearMap_apply (c : ℕ → ℝ) (f : ℝ[X]) :
    evenDerivativeLinearMap c f = evenDerivativeOperator c f := rfl

/-- The image of a monomial: `T_c uᴺ = ∑ₖ cₖ (N)_{2k} u^{N-k}`. -/
theorem evenDerivativeOperator_X_pow (N : ℕ) :
    evenDerivativeOperator c (X ^ N) =
      ∑ k ∈ Finset.range (N / 2 + 1), C (c k * (N.descFactorial (2 * k) : ℝ)) * X ^ (N - k) := by
  rw [evenDerivativeOperator, natDegree_X_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : 2 * k ≤ N := by simp only [Finset.mem_range] at hk; lia
  rw [iterate_derivative_X_pow_eq_smul, smul_eq_C_mul, C_mul]
  have : (X : ℝ[X]) ^ k * X ^ (N - 2 * k) = X ^ (N - k) := by
    rw [← pow_add]; congr 1; lia
  rw [← this]
  ring

private theorem sum_comp' {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (q : ℝ[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  simp

/-- **Folding.** `T_c(uᴺ)(-z²) = (-1)ᴺ zᴺ p_N(z)`. -/
theorem evenDerivativeOperator_X_pow_comp (N : ℕ) :
    (evenDerivativeOperator c (X ^ N)).comp (-(X ^ 2)) =
      C ((-1) ^ N) * X ^ N * evenDerivativeTest c N := by
  rw [evenDerivativeOperator_X_pow, evenDerivativeTest, sum_comp', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : 2 * k ≤ N := by simp only [Finset.mem_range] at hk; lia
  have h1 : (-1 : ℝ) ^ (N - k) = (-1) ^ N * (-1) ^ k := by
    have : (-1 : ℝ) ^ N = (-1) ^ (N - k) * (-1) ^ k := by
      rw [← pow_add]; congr 1; lia
    rw [this]; ring_nf; simp [mul_comm k 2]
  have h2 : (X : ℝ[X]) ^ N * X ^ (N - 2 * k) = X ^ (2 * (N - k)) := by
    rw [← pow_add]; congr 1; lia
  have h3 : ((-(X ^ 2)) : ℝ[X]) ^ (N - k) = C ((-1) ^ (N - k)) * X ^ (2 * (N - k)) := by
    rw [show (-(X ^ 2) : ℝ[X]) = C (-1) * X ^ 2 by simp, mul_pow, ← C_pow, ← pow_mul]
  simp only [mul_comp, C_comp, pow_comp, X_comp, h3, h1]
  rw [← h2]
  simp only [C_mul]
  ring

/-- The summand `k = 0` is `c 0 • f`; the remaining summands of `T_c f` have smaller degree. -/
private theorem evenDerivativeOperator_sub_natDegree_le (c : ℕ → ℝ) (f : ℝ[X]) :
    (evenDerivativeOperator c f - C (c 0) * f).natDegree ≤ f.natDegree - 1 := by
  rw [evenDerivativeOperator, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, Nat.mul_zero, Function.iterate_zero, id_eq, add_sub_cancel_right]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : 2 * (k + 1) ≤ f.natDegree := by simp only [Finset.mem_range] at hk; lia
  calc (C (c (k + 1)) * X ^ (k + 1) * derivative^[2 * (k + 1)] f).natDegree
      ≤ (X ^ (k + 1) * derivative^[2 * (k + 1)] f).natDegree := by
        rw [mul_assoc]; exact natDegree_C_mul_le _ _
    _ ≤ (k + 1) + (f.natDegree - 2 * (k + 1)) :=
        (natDegree_mul_le (p := X ^ (k + 1))).trans
          (by rw [natDegree_X_pow]; exact add_le_add le_rfl (natDegree_iterate_derivative _ _))
    _ ≤ f.natDegree - 1 := by lia

private theorem degree_evenDerivativeOperator_sub_lt (hc : c 0 = 1) {f : ℝ[X]} (hf : f ≠ 0) :
    (evenDerivativeOperator c f - f).degree < f.degree := by
  have hle := evenDerivativeOperator_sub_natDegree_le c f
  rw [hc, C_1, one_mul] at hle
  by_cases hn : f.natDegree = 0
  · have h0 : evenDerivativeOperator c f - f = 0 := by
      rw [evenDerivativeOperator, hn]; simp [hc]
    rw [h0, degree_zero]
    exact bot_lt_iff_ne_bot.2 (by simpa using hf)
  · exact degree_lt_degree (by lia)

/-- For `c 0 = 1` the operator `T_c` preserves the degree. -/
theorem natDegree_evenDerivativeOperator (hc : c 0 = 1) (f : ℝ[X]) :
    (evenDerivativeOperator c f).natDegree = f.natDegree := by
  by_cases hf : f = 0
  · simp [hf]
  have := natDegree_add_eq_left_of_degree_lt (degree_evenDerivativeOperator_sub_lt hc hf)
  simpa using this

/-- For `c 0 = 1` the operator `T_c` preserves the leading coefficient. -/
theorem leadingCoeff_evenDerivativeOperator (hc : c 0 = 1) (f : ℝ[X]) :
    (evenDerivativeOperator c f).leadingCoeff = f.leadingCoeff := by
  by_cases hf : f = 0
  · simp [hf]
  have := leadingCoeff_add_of_degree_lt' (degree_evenDerivativeOperator_sub_lt hc hf)
  simpa using this

/-- For `c 0 = 1` the operator `T_c` is injective on nonzero polynomials. -/
theorem evenDerivativeOperator_ne_zero (hc : c 0 = 1) {f : ℝ[X]} (hf : f ≠ 0) :
    evenDerivativeOperator c f ≠ 0 := fun h => by
  have := leadingCoeff_evenDerivativeOperator hc f
  rw [h, leadingCoeff_zero] at this
  exact hf (leadingCoeff_eq_zero.1 this.symm)

/-- Nonnegative coefficients `c` give nonnegative coefficients of `T_c f`. -/
theorem HasNonnegCoeffs.evenDerivativeOperator (hc : ∀ k, 0 ≤ c k) {f : ℝ[X]}
    (hf : HasNonnegCoeffs f) : HasNonnegCoeffs (evenDerivativeOperator c f) :=
  hasNonnegCoeffs_finsetSum _ _ fun k _ =>
    (hasNonnegCoeffs_C (hc k)).mul (hasNonnegCoeffs_X.pow k) |>.mul (hf.iterate_derivative _)

/-- For `c 0 = 1` the test polynomial `p_N` is nonzero. -/
theorem evenDerivativeTest_ne_zero (hc : c 0 = 1) (N : ℕ) : evenDerivativeTest c N ≠ 0 := by
  intro h
  have h1 := evenDerivativeOperator_X_pow_comp (c := c) N
  rw [h, mul_zero] at h1
  refine (comp_neg_X_sq_ne_zero (evenDerivativeOperator_ne_zero hc (pow_ne_zero N X_ne_zero))) h1

/-- The lower-degree caps: `p_N^{(N-n)} = (N)_{N-n} p_n` for `n ≤ N`. -/
theorem iterate_derivative_evenDerivativeTest {n N : ℕ} (hn : n ≤ N) :
    derivative^[N - n] (evenDerivativeTest c N) =
      C (N.descFactorial (N - n) : ℝ) * evenDerivativeTest c n := by
  rw [evenDerivativeTest, evenDerivativeTest, iterate_derivative_sum, Finset.mul_sum]
  have hsub : Finset.range (n / 2 + 1) ⊆ Finset.range (N / 2 + 1) :=
    Finset.range_mono (by lia)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 2 * k ≤ n := by simp only [Finset.mem_range] at hk; lia
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul, smul_eq_C_mul,
      show N - 2 * k - (N - n) = n - 2 * k by lia]
    have hfac := Nat.descFactorial_mul_descFactorial (n := N) (k := N - n) (m := N - n + 2 * k)
      (by lia)
    have hfac2 := Nat.descFactorial_mul_descFactorial (n := N) (k := 2 * k) (m := N - n + 2 * k)
      (by lia)
    rw [show N - n + 2 * k - (N - n) = 2 * k by lia,
      show N - (N - n) = n by lia] at hfac
    rw [show N - n + 2 * k - 2 * k = N - n by lia] at hfac2
    have hR : (n.descFactorial (2 * k) : ℝ) * N.descFactorial (N - n) =
        (N - 2 * k).descFactorial (N - n) * N.descFactorial (2 * k) := by
      exact_mod_cast hfac.trans hfac2.symm
    simp only [← C_mul, ← mul_assoc]
    congr 2
    linear_combination (-((-1) ^ k * c k)) * hR
  · intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk hk'
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul,
      (Nat.descFactorial_eq_zero_iff_lt (n := N - 2 * k) (k := N - n)).2 (by lia)]
    simp

end RealRooted
