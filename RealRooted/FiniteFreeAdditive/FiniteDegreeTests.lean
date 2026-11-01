module

public import RealRooted.Hermite.PoulainInterlacing
public import RealRooted.PFPolynomial
public import RealRooted.FiniteFreeAdditive
import RealRooted.FiniteFreeAdditive.Preservation

/-!
# Finite-degree tests for constant-coefficient differential operators

This file proves the scalar degree-capped test for constant-coefficient
differential operators and the first ordered-pair recurrence consequence.
-/

@[expose] public section

open Polynomial BigOperators

noncomputable section

namespace RealRooted

open HermitePoulain

/-- The degree-`N` monomial test for the constant-coefficient symbol `h`. -/
def finiteDifferentialTest (N : ℕ) (h : ℝ[X]) : ℝ[X] :=
  applyAsDifferentialOperator h (X ^ N)

/-- A constant-coefficient differential symbol preserves the polynomial PF
cone through degree `N`. -/
def PreservesPFUpTo (N : ℕ) (h : ℝ[X]) : Prop :=
  ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree ≤ N →
    IsPFPolynomial (applyAsDifferentialOperator h p)

/-- Two constant-coefficient differential symbols give ordered PF images
through degree `N`. -/
def PreservesOrderedPFUpTo (N : ℕ) (h k : ℝ[X]) : Prop :=
  ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree ≤ N →
    IsPFPolynomial (applyAsDifferentialOperator h p) ∧
      IsPFPolynomial (applyAsDifferentialOperator k p) ∧
        Interl (applyAsDifferentialOperator h p)
          (applyAsDifferentialOperator k p)

private theorem coeff_finiteDifferentialTest_of_le
    (N : ℕ) (h : ℝ[X]) {j : ℕ} (hj : j ≤ N) :
    (finiteDifferentialTest N h).coeff (N - j) =
      (N.descFactorial j : ℝ) * h.coeff j := by
  rw [finiteDifferentialTest, applyAsDifferentialOperator,
    Polynomial.finsetSum_coeff]
  by_cases hh : j ≤ h.natDegree
  · rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
      simp only [nsmul_eq_mul]
      rw [Nat.sub_add_cancel hj]
      simp
      ring
    · intro k hk hkj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
      simp only [nsmul_eq_mul]
      simp [coeff_X_pow, show N - j + k ≠ N by lia]
    · intro hjnot
      exact (hjnot (by simpa using Nat.lt_succ_of_le hh)).elim
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hh), mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
    simp only [nsmul_eq_mul]
    by_cases hkj : k = j
    · subst k
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hh)]
      simp
    · simp [coeff_X_pow, show N - j + k ≠ N by lia]

private theorem natDegree_finiteDifferentialTest_le (N : ℕ) (h : ℝ[X]) :
    (finiteDifferentialTest N h).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [finiteDifferentialTest, applyAsDifferentialOperator,
    Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
  simp only [nsmul_eq_mul]
  simp [coeff_X_pow, show j + k ≠ N by lia]

private theorem finiteDifferentialTest_coeff_nonneg
    {N : ℕ} {h : ℝ[X]} (hF : IsPFPolynomial (finiteDifferentialTest N h))
    {j : ℕ} (hj : j ≤ N) :
    0 ≤ h.coeff j := by
  have hcoeff := hF.hasNonnegCoeffs (N - j)
  rw [coeff_finiteDifferentialTest_of_le N h hj] at hcoeff
  have hfall : 0 < (N.descFactorial j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hj
  nlinarith

/-- If the finite differential test polynomial is PF, the operator sends nonnegative inputs to
polynomials with nonnegative coefficients. -/
theorem applyAsDifferentialOperator_hasNonnegCoeffs_of_test
    {N : ℕ} {h p : ℝ[X]}
    (hF : IsPFPolynomial (finiteDifferentialTest N h))
    (hp : HasNonnegCoeffs p) (hpdeg : p.natDegree ≤ N) :
    HasNonnegCoeffs (applyAsDifferentialOperator h p) := by
  rw [applyAsDifferentialOperator_eq_sum_range_right]
  apply hasNonnegCoeffs_finsetSum
  intro j hj
  have hjle : j ≤ N := by
    have := Finset.mem_range.mp hj
    lia
  exact (hasNonnegCoeffs_C (finiteDifferentialTest_coeff_nonneg hF hjle)).mul
    (hp.iterate_derivative j)

/-- The cap image realizes the differential action as finite-free additive
convolution in the common ambient degree. -/
theorem finiteFreeAdditiveConvolution_finiteDifferentialTest
    (N : ℕ) (h p : ℝ[X]) (hpdeg : p.natDegree ≤ N) :
    finiteFreeAdditiveConvolution N (finiteDifferentialTest N h) p =
      applyAsDifferentialOperator h p := by
  ext j
  by_cases hj : j ≤ N
  · rw [coeff_finiteFreeAdditiveConvolution_of_le N _ _ hj]
    unfold finiteFreeAdditiveConvolutionCoeff
    rw [applyAsDifferentialOperator_eq_sum_range_right,
      Polynomial.finsetSum_coeff]
    have hterm : ∀ i ∈ Finset.range (N - j + 1),
        finiteFreeAdditiveConvolutionGamma N i (N - j - i) *
              (finiteDifferentialTest N h).coeff (N - i) *
            p.coeff (N - (N - j - i)) =
          h.coeff i * (j + i).descFactorial i * p.coeff (j + i) := by
      intro i hi
      have hi' : i ≤ N - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hiN : i ≤ N := hi'.trans (Nat.sub_le N j)
      rw [coeff_finiteDifferentialTest_of_le N h hiN,
        finiteFreeAdditiveConvolutionGamma_eq_descFactorial_ratio N i
          (N - j - i) (by lia)]
      have hfallN : (N.descFactorial i : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr hiN)
      have hfallRest : (N.descFactorial (N - j - i) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt
          (Nat.descFactorial_pos.mpr (by lia : N - j - i ≤ N))
      have hsum : i + (N - j - i) = N - j := by lia
      have hsub : N - (N - j - i) = j + i := by lia
      have hlen : N - j - (N - j - i) = i := by lia
      have hfactor := Nat.descFactorial_mul_descFactorial
        (k := N - j - i) (m := N - j) (n := N) (by lia)
      rw [hsub, hlen] at hfactor
      have hfactorR :
          ((j + i).descFactorial i : ℝ) * N.descFactorial (N - j - i) =
            N.descFactorial (N - j) := by
        exact_mod_cast hfactor
      rw [hsum, hsub]
      field_simp
      rw [← hfactorR]
      ring
    rw [Finset.sum_congr rfl hterm]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
    simp only [nsmul_eq_mul]
    simp only [mul_assoc]
    let f : ℕ → ℝ := fun i ↦
      h.coeff i * ((j + i).descFactorial i * p.coeff (j + i))
    change (Finset.range (N - j + 1)).sum f =
      (Finset.range (p.natDegree + 1)).sum f
    rcases le_total (p.natDegree + 1) (N - j + 1) with hle | hle
    · symm
      apply Finset.sum_subset (Finset.range_mono hle)
      intro i hiBig hiSmall
      have hip : p.natDegree < j + i := by
        simp only [Finset.mem_range, not_lt] at hiBig hiSmall
        lia
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hip]
    · apply Finset.sum_subset (Finset.range_mono hle)
      intro i hiBig hiSmall
      have hip : p.natDegree < j + i := by
        simp only [Finset.mem_range, not_lt] at hiBig hiSmall
        lia
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hip]
  · have hj' : N < j := Nat.lt_of_not_ge hj
    rw [coeff_finiteFreeAdditiveConvolution_of_gt N _ _ hj']
    rw [applyAsDifferentialOperator_eq_sum_range_right,
      Polynomial.finsetSum_coeff]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
    simp only [nsmul_eq_mul]
    have hpzero : p.coeff (j + k) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
    rw [hpzero]
    simp

/-- A constant-coefficient differential operator preserves PF polynomials
through degree `N` exactly when its image of `X ^ N` is PF. -/
theorem preservesPFUpTo_iff_finiteDifferentialTest
    (N : ℕ) (h : ℝ[X]) :
    PreservesPFUpTo N h ↔ IsPFPolynomial (finiteDifferentialTest N h) := by
  constructor
  · intro hpres
    exact hpres (isPFPolynomial_X_pow N) (by simp)
  · intro hF p hp hpdeg
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    · exact applyAsDifferentialOperator_hasNonnegCoeffs_of_test
        hF hp.hasNonnegCoeffs hpdeg
    · rw [← finiteFreeAdditiveConvolution_finiteDifferentialTest N h p hpdeg]
      exact Or.inr <| splits_finiteFreeAdditiveConvolution N
        (hF.eq_zero_or_splits.elim (fun hz ↦ hz ▸ Splits.zero) id)
        (hp.eq_zero_or_splits.elim (fun hz ↦ hz ▸ Splits.zero) id)
        (natDegree_finiteDifferentialTest_le N h) hpdeg

/-- Ordered preservation through degree `N` forces the two monomial-test
images to be PF and ordered. -/
theorem finiteDifferentialTest_ordered_of_preservesOrderedPFUpTo
    {N : ℕ} {h k : ℝ[X]} (hpres : PreservesOrderedPFUpTo N h k) :
    IsPFPolynomial (finiteDifferentialTest N h) ∧
      IsPFPolynomial (finiteDifferentialTest N k) ∧
        Interl (finiteDifferentialTest N h) (finiteDifferentialTest N k) := by
  exact hpres (isPFPolynomial_X_pow N) (by simp)

/-- An ordered PF pair remains ordered after adjoining `X` to its left
member and adding a nonnegative multiple of its right member. -/
theorem interl_X_mul_add_C_mul {f g : ℝ[X]} (hf : IsPFPolynomial f)
    (hg : IsPFPolynomial g) (hfg : Interl f g) {a : ℝ} (ha : 0 ≤ a) :
    Interl f (X * f + C a * g) := by
  have hX : Interl f (X * f) :=
    interl_mul_X_of_interl hf.interl_self hf.hasNonnegCoeffs hf.hasNonnegCoeffs
  simpa using interl_nonneg_combo_right_of_common_left_of_nonneg hX hfg
    hf.X_mul.hasNonnegCoeffs hg.hasNonnegCoeffs zero_le_one ha

/-- Adjoining `X` to the left member of an ordered PF pair and adding a
nonnegative multiple of its right member remains in the PF cone. -/
theorem isPFPolynomial_X_mul_add_C_mul {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hfg : Interl f g)
    {a : ℝ} (ha : 0 ≤ a) : IsPFPolynomial (X * f + C a * g) := by
  have hinterl := interl_X_mul_add_C_mul hf hg hfg ha
  have hnn : HasNonnegCoeffs (X * f + C a * g) :=
    hf.X_mul.hasNonnegCoeffs.add (hasNonnegCoeffs_C_mul ha hg.hasNonnegCoeffs)
  by_cases hf0 : f = 0
  · rw [hf0, mul_zero, zero_add]
    rcases hg.eq_zero_or_splits with hg0 | hgs
    · simpa [hg0] using IsPFPolynomial.zero
    · exact IsPFPolynomial.of_realRooted_nonneg
        (hasNonnegCoeffs_C_mul ha hg.hasNonnegCoeffs)
        ((Polynomial.Splits.C a).mul hgs)
  rcases hinterl with hleft0 | hright0 | hstrict
  · exact False.elim (hf0 hleft0)
  · simpa [hright0] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg hnn hstrict.2.1.2

/-- Recurrence form of the ordered-pair step for two differential symbols. -/
theorem differentialRecurrence_pf_and_interl {h k p : ℝ[X]}
    (hh : IsPFPolynomial (applyAsDifferentialOperator h p))
    (hk : IsPFPolynomial (applyAsDifferentialOperator k p))
    (horder : Interl (applyAsDifferentialOperator h p)
      (applyAsDifferentialOperator k p)) {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial
        (X * applyAsDifferentialOperator h p +
          C a * applyAsDifferentialOperator k p) ∧
      Interl (applyAsDifferentialOperator h p)
        (X * applyAsDifferentialOperator h p +
          C a * applyAsDifferentialOperator k p) := by
  exact ⟨isPFPolynomial_X_mul_add_C_mul hh hk horder ha,
    interl_X_mul_add_C_mul hh hk horder ha⟩

end RealRooted
