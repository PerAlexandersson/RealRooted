import RealRooted.NarayanaTransformation.Rectangular.LowDegree

/-!
# Narayana rectangular convolution coefficient transport.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Factorial form of the generalized Narayana coefficient `N_m(n,k)`.

From `N_m(n,k) = C(n,k) * C(n+m,k) / C(m+k,k)` one gets, for `k ≤ n`,
the paper's Eq. (1.2) form. -/
theorem narayanaTransformCoeff_eq_factorial (m n k : ℕ) (hk : k ≤ n) :
    narayanaTransformCoeff m n k =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
          (Nat.factorial m : ℝ)) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ) *
          (Nat.factorial (m + k) : ℝ) *
          (Nat.factorial (n + m - k) : ℝ)) := by
  have hk2 : k ≤ n + m := hk.trans (Nat.le_add_right n m)
  have h3 : k ≤ m + k := Nat.le_add_left k m
  have e1 : (m + k) - k = m := by lia
  unfold narayanaTransformCoeff
  rw [Nat.cast_choose ℝ hk, Nat.cast_choose ℝ hk2, Nat.cast_choose ℝ h3, e1]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp

/-- Complementary-index symmetry of the generalized Narayana coefficients. -/
theorem narayanaTransformCoeff_symm (m n k : ℕ) (hk : k ≤ n) :
    narayanaTransformCoeff m n k = narayanaTransformCoeff m n (n - k) := by
  rw [narayanaTransformCoeff_eq_factorial m n k hk,
      narayanaTransformCoeff_eq_factorial m n (n - k) (Nat.sub_le n k)]
  have h1 : n - (n - k) = k := by lia
  have h2 : m + (n - k) = n + m - k := by lia
  have h3 : n + m - (n - k) = m + k := by lia
  rw [h1, h2, h3]
  ring

/-- Reversed-index coefficient of the generalized Narayana polynomial. -/
theorem coeff_narayanaPolynomial_sub (m n i : ℕ) (hi : i ≤ n) :
    (narayanaPolynomial m n).coeff (n - i) = narayanaTransformCoeff m n i := by
  rw [coeff_narayanaPolynomial_of_le (Nat.sub_le n i)]
  exact (narayanaTransformCoeff_symm m n i hi).symm

/-- The key coefficient identity from Section 2 of Mao--Wang.  For `i+j ≤ n`,
the rectangular convolution coefficient `γ_{i,j}^{(n,m)}` transports the
generalized Narayana coefficient `N_m(n,j)` to `N_m(n-i,j)`. -/
theorem rectangularConvolutionGamma_mul_narayanaTransformCoeff
    (m n i j : ℕ) (h : i + j ≤ n) :
    rectangularConvolutionGamma m n i j * narayanaTransformCoeff m n j =
      narayanaTransformCoeff m (n - i) j := by
  have hj : j ≤ n := by lia
  have hji : j ≤ n - i := by lia
  have ea : (n - i) + m = n + m - i := by lia
  rw [narayanaTransformCoeff_eq_factorial m n j hj,
      narayanaTransformCoeff_eq_factorial m (n - i) j hji, ea]
  unfold rectangularConvolutionGamma
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp

/-- Symmetric companion of
`rectangularConvolutionGamma_mul_narayanaTransformCoeff`. -/
theorem rectangularConvolutionGamma_mul_narayanaTransformCoeff_left
    (m n i j : ℕ) (h : i + j ≤ n) :
    rectangularConvolutionGamma m n i j * narayanaTransformCoeff m n i =
      narayanaTransformCoeff m (n - j) i := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_mul_narayanaTransformCoeff m n j i (by lia)

/-- Rectangular convolution of two generalized Narayana polynomials, expanded
as the finite coefficient sum before the final Vandermonde evaluation. -/
theorem rectangularConvolutionCoeff_narayanaPolynomial_of_le
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        rectangularConvolutionGamma m n i (k - i) *
          narayanaTransformCoeff m n i *
          narayanaTransformCoeff m n (k - i) := by
  unfold rectangularConvolutionCoeff
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hi_n : i ≤ n := hik.trans hk
  have hki_n : k - i ≤ n := (Nat.sub_le k i).trans hk
  rw [coeff_narayanaPolynomial_sub m n i hi_n,
    coeff_narayanaPolynomial_sub m n (k - i) hki_n]

/-- The same convolution sum after transporting one Narayana factor with the
rectangular convolution coefficient.  The remaining closed-form step is a
Vandermonde/Chu summation. -/
theorem rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (k - i) := by
  rw [rectangularConvolutionCoeff_narayanaPolynomial_of_le m n k hk]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsum : i + (k - i) ≤ n := by
    rw [Nat.add_sub_of_le hik]
    exact hk
  rw [← rectangularConvolutionGamma_mul_narayanaTransformCoeff m n i (k - i) hsum]
  ring

/-- Vandermonde variant used in the Mao--Wang Section 2 coefficient bridge.
Summing the shifted product of binomials over `Finset.range (k + 1)` collapses
to a single binomial coefficient. -/
theorem sum_choose_mul_choose_shift (m k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        Nat.choose k i * Nat.choose (2 * m + k) (m + i) =
      Nat.choose (2 * m + 2 * k) (m + k) := by
  have h1 : Nat.choose (2 * m + 2 * k) (m + k) =
      ∑ i ∈ Finset.range (m + k + 1),
        Nat.choose k i * Nat.choose (2 * m + k) (m + k - i) := by
    rw [show 2 * m + 2 * k = k + (2 * m + k) by ring, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      fun i j => Nat.choose k i * Nat.choose (2 * m + k) j]
  rw [h1, ← Finset.sum_subset (Finset.range_mono (by lia : k + 1 ≤ m + k + 1))]
  · rw [← Finset.sum_flip]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hx),
        Nat.add_sub_assoc (Finset.mem_range_succ_iff.mp hx)]
  · intro x _ hx
    have hx' : k < x :=
      Nat.lt_of_succ_le (Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx))
    rw [Nat.choose_eq_zero_of_lt hx']
    ring

/-- Reciprocal-factorial form of the Chu--Vandermonde summation appearing in
the Mao--Wang Section 2 coefficient bridge. -/
theorem sum_factorial_recip_eq (m k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ)) =
      (Nat.factorial (2 * m + 2 * k) : ℝ) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (m + k) : ℝ) ^ 2 *
          (Nat.factorial (2 * m + k) : ℝ)) := by
  have h_binom : (∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ))) =
      ∑ i ∈ Finset.range (k + 1),
        ((Nat.choose k i : ℝ) * (Nat.choose (2 * m + k) (m + i) : ℝ)) /
          ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hmi : m + i ≤ 2 * m + k := by lia
    rw [Nat.cast_choose ℝ hik, Nat.cast_choose ℝ hmi]
    field_simp
    rw [show 2 * m + k - (m + i) = m + k - i by lia]
  convert h_binom using 1
  convert congr_arg
      (fun x : ℕ =>
        (x : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)))
      (sum_choose_mul_choose_shift m k) using 1
  · rw [sum_choose_mul_choose_shift, Nat.cast_choose]
    · rw [show 2 * m + 2 * k - (m + k) = m + k by
        rw [Nat.sub_eq_of_eq_add]
        ring]
      ring
    · lia
  · convert congr_arg
        (fun x : ℕ =>
          (x : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)))
        (sum_choose_mul_choose_shift m k) using 1
    norm_num [Finset.sum_div]

/-- Short name for the transported Narayana rectangular-convolution coefficient
sum used in the Mao--Wang Section 2 bridge. -/
theorem rectangularConvolutionCoeff_narayana_eq_sum
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (k - i) :=
  rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport m n k hk

/-- Each summand of the Chu--Vandermonde sum factors as a constant independent
of `i` times a reciprocal-factorial term. -/
theorem narayana_product_term_eq (m n k i : ℕ) (hk : k ≤ n) (hi : i ≤ k) :
    narayanaTransformCoeff m n i * narayanaTransformCoeff m (n - i) (k - i) =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
          (Nat.factorial m : ℝ) ^ 2 /
            ((Nat.factorial (n - k) : ℝ) *
              (Nat.factorial (n + m - k) : ℝ))) *
        ((1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ))) := by
  have h_geometric :
      narayanaTransformCoeff m n i * narayanaTransformCoeff m (n - i) (k - i) =
        ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
            (Nat.factorial m : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (n - i) : ℝ) *
            (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (n + m - i) : ℝ))) *
        ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n + m - i) : ℝ) *
            (Nat.factorial m : ℝ) /
          ((Nat.factorial (k - i) : ℝ) * (Nat.factorial (n - k) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ) *
            (Nat.factorial (n + m - k) : ℝ))) := by
    convert congr_arg₂ (· * ·)
      (narayanaTransformCoeff_eq_factorial m n i (hi.trans hk))
      (narayanaTransformCoeff_eq_factorial m (n - i) (k - i) (by lia)) using 2
    rw [show n + m - i = n - i + m by lia,
      show n - i - (k - i) = n - k by lia,
      show m + (k - i) = m + k - i by lia,
      show n - i + m - (k - i) = n + m - k by lia]
  rw [h_geometric]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp [f0]

/-- Mao--Wang Section 2 coefficient bridge: closed form for the rectangular
convolution coefficient of a generalized Narayana polynomial with itself. -/
theorem coeff_rectangularConvolution_narayana (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      narayanaTransformCoeff m n k *
        ((Nat.factorial m : ℝ) * (Nat.factorial (2 * m + 2 * k) : ℝ) /
          ((Nat.factorial (2 * m + k) : ℝ) *
            (Nat.factorial (m + k) : ℝ))) := by
  convert rectangularConvolutionCoeff_narayana_eq_sum m n k hk using 1
  rw [Finset.sum_congr rfl
    fun i hi => narayana_product_term_eq m n k i hk
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [← Finset.mul_sum _ _ _, sum_factorial_recip_eq]
  rw [narayanaTransformCoeff_eq_factorial m n k hk]
  ring

/-- Coefficients of the rectangular additive convolution of two generalized
Narayana polynomials, reduced to the transported convolution sum. -/
theorem coeff_rectangularAdditiveConvolution_narayanaPolynomial_of_le
    (m n j : ℕ) (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n (narayanaPolynomial m n)
        (narayanaPolynomial m n)).coeff j =
      ∑ i ∈ Finset.range (n - j + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (n - j - i) := by
  rw [coeff_rectangularAdditiveConvolution_of_le m n (narayanaPolynomial m n)
      (narayanaPolynomial m n) hj,
    rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport m n (n - j)
      (Nat.sub_le n j)]

/-- Rectangular-convolution coefficient after applying the degree-`n` sign flip
to an arbitrary input and to `N_{n,m}`. -/
theorem coeff_rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_of_le
    (m n j : ℕ) (p : ℝ[X]) (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n (degreeSignFlip n p)
        (degreeSignFlip n (narayanaPolynomial m n))).coeff j =
      (-1 : ℝ) ^ (n - j) *
        ∑ i ∈ Finset.range (n - j + 1),
          p.coeff (n - i) * narayanaTransformCoeff m (n - i) j := by
  rw [coeff_rectangularAdditiveConvolution_of_le m n (degreeSignFlip n p)
    (degreeSignFlip n (narayanaPolynomial m n)) hj]
  unfold rectangularConvolutionCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hki_n : n - j - i ≤ n := by lia
  have hsum : i + (n - j - i) ≤ n := by
    rw [Nat.add_sub_of_le hik]
    exact Nat.sub_le n j
  have hsign :
      (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - j - i) = (-1 : ℝ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hik]
  have hgamma :
      rectangularConvolutionGamma m n i (n - j - i) *
          narayanaTransformCoeff m n (n - j - i) =
        narayanaTransformCoeff m (n - i) j := by
    rw [rectangularConvolutionGamma_mul_narayanaTransformCoeff m n i
      (n - j - i) hsum]
    have hsym := narayanaTransformCoeff_symm m (n - i) (n - j - i) (by lia)
    rwa [show n - i - (n - j - i) = j by lia] at hsym
  rw [coeff_degreeSignFlip_of_le p (by lia : n - i ≤ n),
    coeff_degreeSignFlip_of_le (narayanaPolynomial m n)
      (by lia : n - (n - j - i) ≤ n)]
  rw [show n - (n - i) = i by lia,
    show n - (n - (n - j - i)) = n - j - i by lia]
  rw [coeff_narayanaPolynomial_sub m n (n - j - i) hki_n]
  calc
    rectangularConvolutionGamma m n i (n - j - i) *
          ((-1 : ℝ) ^ i * p.coeff (n - i)) *
        ((-1 : ℝ) ^ (n - j - i) * narayanaTransformCoeff m n (n - j - i)) =
        ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - j - i)) *
          p.coeff (n - i) *
            (rectangularConvolutionGamma m n i (n - j - i) *
              narayanaTransformCoeff m n (n - j - i)) := by
      ring
    _ = (-1 : ℝ) ^ (n - j) *
        (p.coeff (n - i) * narayanaTransformCoeff m (n - i) j) := by
      rw [hsign, hgamma]
      ring

/-- Mao--Wang's coefficient comparison: rectangular convolution of the
degree-`n` sign flips of `p` and `N_{n,m}` is the degree-`n` sign flip of the
Narayana transform of `p`. -/
theorem rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_eq
    (m n : ℕ) (p : ℝ[X]) (hpdeg : p.natDegree ≤ n) :
    rectangularAdditiveConvolution m n (degreeSignFlip n p)
        (degreeSignFlip n (narayanaPolynomial m n)) =
      degreeSignFlip n (narayanaTransform m p) := by
  ext j
  by_cases hj : j ≤ n
  · rw [coeff_rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_of_le
      m n j p hj]
    rw [coeff_degreeSignFlip_narayanaTransform_of_le m n p hj,
      narayanaTransform_coeff_sum_reflect m n j p hpdeg hj]
  · have hjlt : n < j := Nat.lt_of_not_ge hj
    rw [coeff_rectangularAdditiveConvolution_of_gt m n (degreeSignFlip n p)
        (degreeSignFlip n (narayanaPolynomial m n)) hjlt,
      coeff_degreeSignFlip_of_lt (narayanaTransform m p) hjlt]


end RealRooted
