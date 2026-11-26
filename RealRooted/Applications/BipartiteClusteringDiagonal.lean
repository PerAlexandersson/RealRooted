module

public import RealRooted.Applications.BipartiteClustering
import RealRooted.ExponentialRows.SubstitutionRows
import Mathlib.Tactic

/-!
# The diagonal exponential formula for bipartite clustering

At edge cap two the bivariate labelled-set exponential is
`exp(x + y + t x y (1 + (x + y)/2))`. After fixing the number `k` of
pieces, its remaining factor depends only on `x + y`. Extracting the
balanced diagonal therefore gives a binomial coefficient times a single
power-series coefficient. We use this coefficient formula as the definition
of the packing rows, without formalizing finite graph enumeration.

We identify these rows with the determinant-based polynomials in
`BipartiteClustering`. Consequently the diagonal exponential rows have exact
degree, simple negative roots, and genuinely strict consecutive interlacing.

Source: unpublished recurrence and exponential formula in RealRooted #2646,
https://github.com/PerAlexandersson/RealRooted/issues/2646.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted.BipartiteClustering

private theorem coeff_affine_insertion {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (n k : ℕ) :
    (ExponentialRows.insertionRow (ExponentialRows.affineBlockWeights A B) n).coeff k =
      (n.factorial : ℝ) * (k.factorial : ℝ)⁻¹ *
        PowerSeries.coeff n (((PowerSeries.exp ℝ).subst A) * B ^ k) := by
  rw [ExponentialRows.insertionRow_eq_factorialCoeff,
    ExponentialRows.insertionSeries_affineBlockWeights hA hB,
    ExponentialRows.factorialCoeff, coeff_C_mul, PowerSeries.coeff_mul,
    finsetSum_coeff, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_map, coeff_C_mul]
  have he (j : ℕ) :
      (PowerSeries.coeff j (ExponentialRows.exponentialKernel B)).coeff k =
        (k.factorial : ℝ)⁻¹ * PowerSeries.coeff j (B ^ k) := by
    have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
    have hh := ExponentialRows.coeff_exponentialKernelRow hB j k
    simp only [ExponentialRows.exponentialKernelRow,
      ExponentialRows.factorialCoeff, coeff_C_mul] at hh
    apply (mul_left_cancel₀ hjfac)
    simpa only [mul_assoc] using hh
  simp only [he, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

private theorem row_coeff (n k : ℕ) (hk : k ≤ n) :
    (row n).coeff k = (n.factorial : ℝ) * (k.factorial : ℝ)⁻¹ *
      PowerSeries.coeff (n - k) (PowerSeries.exp ℝ *
        ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ (2 * k)) := by
  have he : row n = ExponentialRows.insertionRow
      (ExponentialRows.affineBlockWeights PowerSeries.X
        (blockPolynomial : PowerSeries ℝ)) n := by
    rw [ExponentialRows.insertionRow_affineBlockWeights_eq_exponential
      (by simp) (by simp [blockPolynomial])]
    simpa only [PowerSeries.map_X] using row_eq_exponential n
  rw [he, coeff_affine_insertion (by simp) (by simp [blockPolynomial])]
  congr 1
  rw [PowerSeries.X_subst, blockPolynomial_eq]
  simp only [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_pow, mul_pow, ← pow_mul]
  rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', ite_eq_left hk]

private theorem coeff_linear_pow (c : ℝ) (k l : ℕ) :
    PowerSeries.coeff l (((1 + C c * X : ℝ[X]) : PowerSeries ℝ) ^ k) =
      (k.choose l : ℝ) * c ^ l := by
  rw [← Polynomial.coe_pow, Polynomial.coeff_coe]
  have he : (1 + C c * X : ℝ[X]) ^ k = ((1 + X) ^ k).comp (C c * X) := by
    simp only [pow_comp, add_comp, one_comp, X_comp]
  rw [he, comp_C_mul_X_coeff, coeff_one_add_X_pow]

private theorem factorial_coeff_exp_mul_linear (c : ℝ) (m k : ℕ) :
    (m.factorial : ℝ) * PowerSeries.coeff m (PowerSeries.exp ℝ *
      ((1 + C c * X : ℝ[X]) : PowerSeries ℝ) ^ k) =
      ∑ l ∈ range (m + 1), (k.choose l : ℝ) * (m.descFactorial l : ℝ) * c ^ l := by
  rw [mul_comm (PowerSeries.exp ℝ), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro l hl
  rw [coeff_linear_pow, PowerSeries.coeff_exp]
  have hf : ((m - l).factorial : ℝ) ≠ 0 := by positivity
  have hh : ((m - l).factorial : ℝ) * (m.descFactorial l : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial (by have := mem_range.mp hl; lia)
  norm_num only [map_div₀, map_natCast, map_one]
  rw [← hh]
  field_simp

private theorem factorial_coeff_exp_mul_linear_symm (c : ℝ) (m k : ℕ) :
    (m.factorial : ℝ) * PowerSeries.coeff m (PowerSeries.exp ℝ *
      ((1 + C c * X : ℝ[X]) : PowerSeries ℝ) ^ k) =
    (k.factorial : ℝ) * PowerSeries.coeff k (PowerSeries.exp ℝ *
      ((1 + C c * X : ℝ[X]) : PowerSeries ℝ) ^ m) := by
  rw [factorial_coeff_exp_mul_linear, factorial_coeff_exp_mul_linear]
  have he (a b : ℕ) (ha : a ≤ m + k) :
      (∑ l ∈ range (a + 1), (b.choose l : ℝ) * (a.descFactorial l : ℝ) * c ^ l) =
        ∑ l ∈ range (m + k + 1), (b.choose l : ℝ) *
          (a.descFactorial l : ℝ) * c ^ l := by
    apply sum_subset (by intro l hl; simp only [mem_range] at hl ⊢; lia)
    intro l _ hl
    have hlt : a < l := by simp only [mem_range] at hl; lia
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero, mul_zero, zero_mul]
  rw [he m k (by lia), he k m (by lia)]
  apply sum_congr rfl
  intro l _
  simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  ring

private abbrev indexPair (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private abbrev sumVariables : MvPowerSeries (Fin 2) ℝ :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1

private theorem indexPair_eq_iff (a b c d : ℕ) :
    indexPair a b = indexPair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrArg (fun e => e 0) h
    have h1 := congrArg (fun e => e 1) h
    simpa [indexPair] using And.intro h0 h1
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem coeff_sumVariables_pow (a b m : ℕ) :
    MvPowerSeries.coeff (indexPair a b) (sumVariables ^ m) =
      if m = a + b then (m.choose a : ℝ) else 0 := by
  rw [sumVariables, add_pow, map_sum]
  have hc (r : ℕ) : (r : MvPowerSeries (Fin 2) ℝ) = MvPowerSeries.C (r : ℝ) := by simp
  simp only [hc, MvPowerSeries.coeff_mul_C, MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial, mul_one, MvPowerSeries.coeff_monomial,
    indexPair_eq_iff]
  by_cases hm : m = a + b
  · subst m
    rw [ite_eq_left rfl, sum_eq_single a]
    · simp
    · intro j _ hj
      simp only [Ne.symm hj, false_and, ite_false, zero_mul]
    · intro h
      exact (h (mem_range.mpr (by lia))).elim
  · rw [ite_eq_right hm]
    apply sum_eq_zero
    intro j hj
    have hn : ¬ (a = j ∧ b = m - j) := by
      intro ⟨ha, hb⟩
      have := mem_range.mp hj
      apply hm
      lia
    simp only [hn, ite_false, zero_mul]

private theorem coeff_subst_sumVariables (f : PowerSeries ℝ) (a b : ℕ) :
    MvPowerSeries.coeff (indexPair a b) (f.subst sumVariables) =
      (a + b).choose a * PowerSeries.coeff (a + b) f := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.add
    (PowerSeries.HasSubst.X 0) (PowerSeries.HasSubst.X 1))]
  simp only [coeff_sumVariables_pow, smul_eq_mul]
  rw [finsum_eq_single _ (a + b)]
  · simp only [ite_true]
    ring
  · intro j hj
    simp only [hj, ite_false, mul_zero]

private theorem indexPair_le_iff (a b c d : ℕ) :
    indexPair a b ≤ indexPair c d ↔ a ≤ c ∧ b ≤ d := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simpa [indexPair] using And.intro h0 h1
  · rintro ⟨ha, hb⟩ i
    fin_cases i <;> simpa [indexPair]

private theorem indexPair_sub (n k : ℕ) :
    indexPair n n - indexPair k k = indexPair (n - k) (n - k) := by
  ext i
  fin_cases i <;> simp [indexPair]

private theorem coeff_shifted_subst (f : PowerSeries ℝ) (n k : ℕ) :
    MvPowerSeries.coeff (indexPair n n)
      (MvPowerSeries.X 0 ^ k * MvPowerSeries.X 1 ^ k * f.subst sumVariables) =
        if k ≤ n then ((2 * (n - k)).choose (n - k) : ℝ) *
          PowerSeries.coeff (2 * (n - k)) f else 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial, one_mul,
    MvPowerSeries.coeff_monomial_mul]
  simp only [indexPair_le_iff, and_self, one_mul]
  split_ifs with hk
  · rw [indexPair_sub, coeff_subst_sumVariables]
    congr 2 <;> lia
  · rfl

private theorem coeff_bivariate_kernel (n k : ℕ) :
    MvPowerSeries.coeff (indexPair n n)
      (((PowerSeries.exp ℝ).subst sumVariables) *
        (MvPowerSeries.X 0 * MvPowerSeries.X 1 *
          (1 + MvPowerSeries.C (1 / 2 : ℝ) * sumVariables)) ^ k) =
        if k ≤ n then ((2 * (n - k)).choose (n - k) : ℝ) *
          PowerSeries.coeff (2 * (n - k)) (PowerSeries.exp ℝ *
            ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ k) else 0 := by
  have hs : PowerSeries.HasSubst sumVariables :=
    (PowerSeries.HasSubst.X 0).add (PowerSeries.HasSubst.X 1)
  have h1 : (1 : PowerSeries ℝ).subst sumVariables = 1 := by
    rw [show (1 : PowerSeries ℝ) = PowerSeries.C 1 by simp,
      PowerSeries.subst_C, map_one]
  have hq : (((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ)).subst sumVariables =
      1 + MvPowerSeries.C (1 / 2 : ℝ) * sumVariables := by
    simp [Polynomial.coe_add, Polynomial.coe_mul, PowerSeries.subst_add hs,
      PowerSeries.subst_mul hs, PowerSeries.subst_X hs, h1]
  have he : ((PowerSeries.exp ℝ).subst sumVariables) *
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 *
        (1 + MvPowerSeries.C (1 / 2 : ℝ) * sumVariables)) ^ k =
        MvPowerSeries.X 0 ^ k * MvPowerSeries.X 1 ^ k *
          (PowerSeries.exp ℝ *
            ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ k).subst
              sumVariables := by
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, hq, mul_pow, mul_pow]
    ring
  rw [he, coeff_shifted_subst]

/-- Balanced diagonal coefficients of `exp(x+y+txy(1+(x+y)/2))`.
For `k` pieces, the factor left after removing `(xy)^k` depends on `x+y`,
so its `(n-k,n-k)` coefficient is `choose (2(n-k)) (n-k)` times its
coefficient of degree `2(n-k)`. The two vertex-label factorials are included. -/
@[expose] def diagonalPolynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C ((n.factorial : ℝ) ^ 2 * (k.factorial : ℝ)⁻¹ *
    ((2 * (n - k)).choose (n - k) : ℝ) *
      PowerSeries.coeff (2 * (n - k)) (PowerSeries.exp ℝ *
        ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ k)) * X ^ k

private theorem natDegree_diagonalPolynomial_le (n : ℕ) :
    (diagonalPolynomial n).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hj; lia)

private theorem coeff_diagonalPolynomial (n k : ℕ) (hk : k ≤ n) :
    (diagonalPolynomial n).coeff k =
      (n.factorial : ℝ) ^ 2 * (k.factorial : ℝ)⁻¹ *
        ((2 * (n - k)).choose (n - k) : ℝ) *
          PowerSeries.coeff (2 * (n - k)) (PowerSeries.exp ℝ *
            ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ k) := by
  rw [diagonalPolynomial, finsetSum_coeff, sum_eq_single k]
  · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
  · intro j _ hj
    simp only [coeff_C_mul_X_pow, Ne.symm hj, ite_false]
  · intro hh
    exact (hh (mem_range.mpr (by lia))).elim

/-- The balanced diagonal exponential rows are exactly the existing algebraic
clustering candidates. This discharges their exponential-formula identification. -/
theorem diagonalPolynomial_eq_polynomial (n : ℕ) : diagonalPolynomial n = polynomial n := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_diagonalPolynomial n k hk, polynomial, coeff_C_mul,
      Polynomial.coeff_reverse, compressedRow_natDegree, Polynomial.revAt_le hk,
      compressedRow, coeff_diagonalOperator, row_coeff n (n - k) (by lia),
      Nat.sub_sub_self hk]
    have hr : ((n - k).factorial : ℝ) ≠ 0 := by positivity
    have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hs := factorial_coeff_exp_mul_linear_symm (1 / 2 : ℝ) k (2 * (n - k))
    have hc : ((2 * (n - k)).choose (n - k) : ℝ) *
        ((n - k).factorial : ℝ) * ((n - k).factorial : ℝ) =
          ((2 * (n - k)).factorial : ℝ) := by
      have hh := Nat.choose_mul_factorial_mul_factorial (n := 2 * (n - k))
        (k := n - k) (by lia)
      have hhsub : 2 * (n - k) - (n - k) = n - k := by lia
      rw [hhsub] at hh
      exact_mod_cast hh
    have he : PowerSeries.coeff k (PowerSeries.exp ℝ *
        ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ (2 * (n - k))) =
          ((2 * (n - k)).factorial : ℝ) / (k.factorial : ℝ) *
            PowerSeries.coeff (2 * (n - k)) (PowerSeries.exp ℝ *
              ((1 + C (1 / 2 : ℝ) * X : ℝ[X]) : PowerSeries ℝ) ^ k) := by
      apply (mul_left_cancel₀ hkf)
      field_simp
      exact hs
    rw [he, ← hc]
    field_simp
  · have hdeg := natDegree_diagonalPolynomial_le n
    rw [coeff_eq_zero_of_natDegree_lt (by lia),
      coeff_eq_zero_of_natDegree_lt (by rw [polynomial_natDegree]; lia)]

/-- The edge-cap-two bivariate EGF, viewed as a series in the piece variable:
`exp(x+y) exp(txy(1+(x+y)/2))`. The two inner variables label the vertex parts. -/
@[expose] def bivariateSeries : PowerSeries (MvPowerSeries (Fin 2) ℝ) :=
  PowerSeries.C ((PowerSeries.exp ℝ).subst
    (MvPowerSeries.X 0 + MvPowerSeries.X 1)) *
      PowerSeries.rescale (MvPowerSeries.X 0 * MvPowerSeries.X 1 *
        (1 + MvPowerSeries.C (1 / 2 : ℝ) * (MvPowerSeries.X 0 + MvPowerSeries.X 1)))
        (PowerSeries.exp (MvPowerSeries (Fin 2) ℝ))

/-- The diagonal polynomials are the literal normalized bivariate EGF coefficients,
including the vanishing coefficients above degree `n`. -/
theorem coeff_bivariateSeries_diagonal (n k : ℕ) :
    (n.factorial : ℝ) ^ 2 *
      MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 n)
        (PowerSeries.coeff k bivariateSeries) = (diagonalPolynomial n).coeff k := by
  have he : algebraMap ℚ (MvPowerSeries (Fin 2) ℝ) (1 / (k.factorial : ℚ)) =
      MvPowerSeries.C ((k.factorial : ℝ)⁻¹) := by
    rw [IsScalarTower.algebraMap_apply ℚ ℝ (MvPowerSeries (Fin 2) ℝ)]
    congr 1
    norm_num
  rw [bivariateSeries, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, he, ← mul_assoc, MvPowerSeries.coeff_mul_C,
    coeff_bivariate_kernel]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, coeff_diagonalPolynomial n k hk]
    ring
  · rw [ite_eq_right hk, zero_mul, mul_zero]
    have hdeg := natDegree_diagonalPolynomial_le n
    exact (coeff_eq_zero_of_natDegree_lt (by lia)).symm

/-- Balanced bipartite edge-cap-two exponential rows have degree `n`. -/
theorem diagonalPolynomial_natDegree (n : ℕ) : (diagonalPolynomial n).natDegree = n := by
  rw [diagonalPolynomial_eq_polynomial, polynomial_natDegree]

/-- Balanced bipartite edge-cap-two exponential rows have simple negative zeros
and strictly interlace consecutively; disjointness supplies strict inequalities. -/
theorem diagonalPolynomial_roots (n : ℕ) :
    Interlaces (diagonalPolynomial n) (diagonalPolynomial (n + 1)) ∧
      HasSimpleRoots (diagonalPolynomial n) ∧ HasSimpleRoots (diagonalPolynomial (n + 1)) ∧
      (∀ x, ¬ ((diagonalPolynomial n).IsRoot x ∧
        (diagonalPolynomial (n + 1)).IsRoot x)) ∧
      (∀ x ∈ (diagonalPolynomial n).roots, x < 0) ∧
      ∀ x ∈ (diagonalPolynomial (n + 1)).roots, x < 0 := by
  simpa only [diagonalPolynomial_eq_polynomial] using polynomial_roots n

/-- The empty packing has weight one in every diagonal exponential row. -/
@[simp] theorem diagonalPolynomial_coeff_zero (n : ℕ) :
    (diagonalPolynomial n).coeff 0 = 1 := by
  rw [diagonalPolynomial_eq_polynomial, polynomial, coeff_C_mul,
    Polynomial.coeff_reverse, compressedRow_natDegree, Polynomial.revAt_le (by lia),
    Nat.sub_zero, compressedRow, coeff_diagonalOperator, row_coeff n n le_rfl,
    Nat.sub_self]
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  simp [hfac]

/-- The top coefficient counts perfect matchings: it is `n!`. -/
theorem diagonalPolynomial_leadingCoeff (n : ℕ) :
    (diagonalPolynomial n).leadingCoeff = (n.factorial : ℝ) := by
  rw [Polynomial.leadingCoeff, diagonalPolynomial_natDegree,
    diagonalPolynomial_eq_polynomial, polynomial, coeff_C_mul,
    Polynomial.coeff_reverse, compressedRow_natDegree, Polynomial.revAt_le le_rfl,
    Nat.sub_self, compressedRow, coeff_diagonalOperator, row_coeff_zero]
  simp

end RealRooted.BipartiteClustering
