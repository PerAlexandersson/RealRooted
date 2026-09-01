import RealRooted.NarayanaTransformation.Rising

/-!
# Generalized Narayana coefficient and transform data.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Coefficient `N_m(n,k)` of the generalized Narayana polynomial. -/
def narayanaTransformCoeff (m n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (Nat.choose (n + m) k : ℝ) /
    (Nat.choose (m + k) k : ℝ)

theorem narayanaTransformCoeff_nonneg (m n k : ℕ) :
    0 ≤ narayanaTransformCoeff m n k := by
  unfold narayanaTransformCoeff
  positivity

theorem narayanaTransformCoeff_eq_zero_of_lt {m n k : ℕ} (h : n < k) :
    narayanaTransformCoeff m n k = 0 := by
  simp [narayanaTransformCoeff, Nat.choose_eq_zero_of_lt h]

@[simp] theorem narayanaTransformCoeff_zero_right (m n : ℕ) :
    narayanaTransformCoeff m n 0 = 1 := by
  simp [narayanaTransformCoeff]

@[simp] theorem narayanaTransformCoeff_zero_left (m k : ℕ) :
    narayanaTransformCoeff m 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, narayanaTransformCoeff]
  · have hchoose : Nat.choose 0 k = 0 := by
      cases k with
      | zero => contradiction
      | succ k => simp
    simp [hk, narayanaTransformCoeff, hchoose]

/-- The `m = 1` Narayana coefficient is the adjacent binomial determinant
appearing in the reflection-principle count. -/
theorem choose_sq_sub_choose_pred_mul_choose_succ_eq_narayanaTransformCoeff_one
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n) :
    (Nat.choose n k : ℝ) ^ 2 -
        (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) =
      narayanaTransformCoeff 1 n k := by
  rw [Nat.cast_choose_sq_sub_choose_pred_mul_choose_succ_eq hkpos hkn]
  unfold narayanaTransformCoeff
  rw [show Nat.choose (1 + k) k = k + 1 by
    simp [add_comm, Nat.choose_succ_self_right]]
  norm_num [Nat.cast_add]

/-- The same adjacent determinant vanishes outside the subset range. -/
theorem choose_sq_sub_choose_pred_mul_choose_succ_eq_narayanaTransformCoeff_one_of_lt
    {n k : ℕ} (h : n < k) :
    (Nat.choose n k : ℝ) ^ 2 -
        (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) =
      narayanaTransformCoeff 1 n k := by
  have hchoose : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt h
  have hchoose_succ : Nat.choose n (k + 1) = 0 :=
    Nat.choose_eq_zero_of_lt (by lia)
  simp [narayanaTransformCoeff, hchoose, hchoose_succ]

/-- Generalized Narayana polynomial `N_{n,m}` from Mao--Wang, Eq. (1.2). -/
def narayanaPolynomial (m n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (narayanaTransformCoeff m n k) * X ^ k

@[simp] theorem coeff_narayanaPolynomial_of_le {m n k : ℕ} (hk : k ≤ n) :
    (narayanaPolynomial m n).coeff k = narayanaTransformCoeff m n k := by
  simp [narayanaPolynomial, hk]

@[simp] theorem coeff_narayanaPolynomial_of_lt {m n k : ℕ} (hk : n < k) :
    (narayanaPolynomial m n).coeff k = 0 := by
  simp [narayanaPolynomial, hk.not_ge]

theorem hasNonnegCoeffs_narayanaPolynomial (m n : ℕ) :
    HasNonnegCoeffs (narayanaPolynomial m n) := by
  intro k
  by_cases hk : k ≤ n
  · simp [coeff_narayanaPolynomial_of_le hk, narayanaTransformCoeff_nonneg]
  · have hk' : n < k := Nat.lt_of_not_ge hk
    simp [coeff_narayanaPolynomial_of_lt hk']

theorem natDegree_narayanaPolynomial_le (m n : ℕ) :
    (narayanaPolynomial m n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_narayanaPolynomial_of_lt hk

/-- A symmetric form of Vandermonde's identity. -/
theorem sum_range_choose_mul_choose_same (m k : ℕ) (hk : k ≤ m) :
    ∑ r ∈ Finset.range (k + 1),
        Nat.choose k r * Nat.choose (m - k) r = Nat.choose m k := by
  have h := Nat.add_choose_eq (m - k) k k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    show (m - k) + k = m by lia] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r ≤ k := by simpa using hr
  simp only
  rw [Nat.choose_symm hrk]
  ring

/-- The termwise multinomial identity behind the gamma expansion of the
binomial-square Narayana polynomial. -/
theorem choose_gamma_term (m k r : ℕ) (hk : k ≤ m) (hr : r ≤ k) :
    Nat.choose m r * Nat.choose (m - r) r * Nat.choose (m - 2 * r) (k - r) =
      Nat.choose m k * Nat.choose k r * Nat.choose (m - k) r := by
  have hA := Nat.choose_mul (n := m - r) (k := k) (s := r) hr
  have hB := Nat.choose_mul (n := m - r) (k := k) (s := k - r) (Nat.sub_le k r)
  have hC := Nat.choose_mul (n := m) (k := k) (s := r) hr
  rw [show m - r - r = m - 2 * r by lia] at hA
  rw [show m - r - (k - r) = m - k by lia,
    show k - (k - r) = r by lia, Nat.choose_symm hr] at hB
  calc
    Nat.choose m r * Nat.choose (m - r) r * Nat.choose (m - 2 * r) (k - r) =
        Nat.choose m r *
          (Nat.choose (m - r) r * Nat.choose (m - 2 * r) (k - r)) := by ring
    _ = Nat.choose m r * (Nat.choose (m - r) k * Nat.choose k r) := by rw [hA]
    _ = Nat.choose m r *
        (Nat.choose (m - r) (k - r) * Nat.choose (m - k) r) := by rw [hB]
    _ = (Nat.choose m r * Nat.choose (m - r) (k - r)) *
        Nat.choose (m - k) r := by ring
    _ = (Nat.choose m k * Nat.choose k r) * Nat.choose (m - k) r := by rw [hC]
    _ = Nat.choose m k * Nat.choose k r * Nat.choose (m - k) r := by ring

/-- Summing the gamma-basis coefficients recovers a squared binomial
coefficient. -/
theorem sum_range_choose_gamma (m k : ℕ) (hk : k ≤ m) :
    ∑ r ∈ Finset.range (k + 1),
        Nat.choose m r * Nat.choose (m - r) r * Nat.choose (m - 2 * r) (k - r) =
      (Nat.choose m k) ^ 2 := by
  calc
    ∑ r ∈ Finset.range (k + 1),
        Nat.choose m r * Nat.choose (m - r) r * Nat.choose (m - 2 * r) (k - r) =
        ∑ r ∈ Finset.range (k + 1),
          Nat.choose m k * Nat.choose k r * Nat.choose (m - k) r := by
            apply Finset.sum_congr rfl
            intro r hr
            exact choose_gamma_term m k r hk (by simpa using hr)
    _ = Nat.choose m k *
        (∑ r ∈ Finset.range (k + 1),
          Nat.choose k r * Nat.choose (m - k) r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = (Nat.choose m k) ^ 2 := by rw [sum_range_choose_mul_choose_same m k hk, pow_two]

/-- Gamma coefficients of the binomial-square Narayana polynomial
`narayanaPolynomial 0 n`. -/
def narayanaZeroGammaPolynomial (n : ℕ) : ℝ[X] :=
  ∑ r ∈ Finset.range (n / 2 + 1),
    Polynomial.monomial r ((Nat.choose n r * Nat.choose (n - r) r : ℕ) : ℝ)

@[simp] theorem coeff_narayanaZeroGammaPolynomial_of_le {n r : ℕ}
    (hr : r ≤ n / 2) :
    (narayanaZeroGammaPolynomial n).coeff r =
      ((Nat.choose n r * Nat.choose (n - r) r : ℕ) : ℝ) := by
  rw [narayanaZeroGammaPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hbr
    rw [Polynomial.coeff_monomial]
    simp [hbr]
  · intro hnot
    exact (hnot (by simpa using hr)).elim

@[simp] theorem coeff_narayanaZeroGammaPolynomial_of_lt {n r : ℕ}
    (hr : n / 2 < r) : (narayanaZeroGammaPolynomial n).coeff r = 0 := by
  rw [narayanaZeroGammaPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  have hbr : b ≠ r := by
    have hb_le : b ≤ n / 2 := by simpa using hb
    lia
  rw [Polynomial.coeff_monomial]
  simp [hbr]

theorem natDegree_narayanaZeroGammaPolynomial_le (n : ℕ) :
    (narayanaZeroGammaPolynomial n).natDegree ≤ n / 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro r hr
  exact coeff_narayanaZeroGammaPolynomial_of_lt hr

theorem coeff_gammaBasisTerm (d i k : ℕ) :
    (gammaBasisTerm d i).coeff k =
      if i ≤ k then (Nat.choose (d - 2 * i) (k - i) : ℝ) else 0 := by
  rw [gammaBasisTerm, Polynomial.coeff_X_pow_mul']
  split_ifs with hik
  · rw [Polynomial.coeff_X_add_one_pow]
  · rfl

/-- The binomial-square Narayana polynomial has the classical gamma expansion
with coefficients `choose n i * choose (n - i) i`. -/
theorem gammaTransform_narayanaZeroGammaPolynomial (n : ℕ) :
    gammaTransform n (narayanaZeroGammaPolynomial n) = narayanaPolynomial 0 n := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_narayanaPolynomial_of_le hk]
    have hcoeff :
        (gammaTransform n (narayanaZeroGammaPolynomial n)).coeff k =
          ∑ i ∈ Finset.range (n / 2 + 1),
            if i ≤ k then
              ((Nat.choose n i * Nat.choose (n - i) i *
                Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ)
            else 0 := by
      rw [gammaTransform, Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ n / 2 := by simpa using hi
      rw [Polynomial.coeff_C_mul, coeff_gammaBasisTerm,
        coeff_narayanaZeroGammaPolynomial_of_le hi_le]
      split_ifs
      · norm_num [Nat.cast_mul]
      · simp
    rw [hcoeff]
    by_cases hkh : k ≤ n / 2
    · have hsub : Finset.range (k + 1) ⊆ Finset.range (n / 2 + 1) :=
        Finset.range_mono (by lia)
      calc
        ∑ i ∈ Finset.range (n / 2 + 1),
            (if i ≤ k then
              ((Nat.choose n i * Nat.choose (n - i) i *
                Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ)
            else 0) =
            ∑ i ∈ Finset.range (k + 1),
              if i ≤ k then
                ((Nat.choose n i * Nat.choose (n - i) i *
                  Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ)
              else 0 := by
                symm
                apply Finset.sum_subset hsub
                intro i hi hni
                have hki : k < i := by simpa using hni
                simp [hki.not_ge]
        _ = ∑ i ∈ Finset.range (k + 1),
              ((Nat.choose n i * Nat.choose (n - i) i *
                Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hik : i ≤ k := by simpa using hi
              simp [hik]
        _ = ((Nat.choose n k) ^ 2 : ℕ) := by exact_mod_cast sum_range_choose_gamma n k hk
        _ = narayanaTransformCoeff 0 n k := by simp [narayanaTransformCoeff, pow_two]
    · have hhalf : n / 2 < k := Nat.lt_of_not_ge hkh
      have hsub : Finset.range (n / 2 + 1) ⊆ Finset.range (k + 1) :=
        Finset.range_mono (by lia)
      calc
        ∑ i ∈ Finset.range (n / 2 + 1),
            (if i ≤ k then
              ((Nat.choose n i * Nat.choose (n - i) i *
                Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ)
            else 0) =
            ∑ i ∈ Finset.range (n / 2 + 1),
              ((Nat.choose n i * Nat.choose (n - i) i *
                Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hik : i ≤ k := by
                have hi_le : i ≤ n / 2 := by simpa using hi
                lia
              simp [hik]
        _ = ∑ i ∈ Finset.range (k + 1),
              ((Nat.choose n i * Nat.choose (n - i) i *
                Nat.choose (n - 2 * i) (k - i) : ℕ) : ℝ) := by
              apply Finset.sum_subset hsub
              intro i hi hni
              have hhalf_i : n / 2 < i := by simpa using hni
              have hchoose : Nat.choose (n - i) i = 0 := by
                apply Nat.choose_eq_zero_of_lt
                lia
              simp [hchoose]
        _ = ((Nat.choose n k) ^ 2 : ℕ) := by exact_mod_cast sum_range_choose_gamma n k hk
        _ = narayanaTransformCoeff 0 n k := by simp [narayanaTransformCoeff, pow_two]
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [coeff_narayanaPolynomial_of_lt hnk]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt
      (natDegree_gammaTransform_le n (narayanaZeroGammaPolynomial n)) hnk

/-- The Narayana basis transform `X ^ k ↦ N_{k,m}`. -/
def narayanaTransform (m : ℕ) : ℝ[X] → ℝ[X] :=
  basisTransform (narayanaPolynomial m)

@[simp] theorem narayanaTransform_X_pow (m n : ℕ) :
    narayanaTransform m (X ^ n) = narayanaPolynomial m n :=
  basisTransform_X_pow (narayanaPolynomial m) n

@[simp] theorem narayanaTransform_monomial (m n : ℕ) (a : ℝ) :
    narayanaTransform m (Polynomial.monomial n a) = C a * narayanaPolynomial m n := by
  rw [narayanaTransform, basisTransform_monomial]

theorem coeff_narayanaTransform (m : ℕ) (p : ℝ[X]) (j : ℕ) :
    (narayanaTransform m p).coeff j =
      p.sum fun k a => a * (narayanaPolynomial m k).coeff j :=
  coeff_basisTransform (narayanaPolynomial m) p j

@[simp] theorem coeff_narayanaTransform_monomial (m n j : ℕ) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j =
      a * (narayanaPolynomial m n).coeff j := by
  simp [narayanaTransform_monomial]

@[simp] theorem coeff_narayanaTransform_monomial_of_le
    {m n j : ℕ} (hj : j ≤ n) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j =
      a * narayanaTransformCoeff m n j := by
  simp [hj]

@[simp] theorem coeff_narayanaTransform_monomial_of_lt
    {m n j : ℕ} (hj : n < j) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j = 0 := by
  simp [hj]

theorem HasNonnegCoeffs.narayanaTransform {m : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (narayanaTransform m p) :=
  hp.basisTransform (hasNonnegCoeffs_narayanaPolynomial m)

theorem coeff_degreeSignFlip_narayanaTransform_of_le
    (m n : ℕ) (p : ℝ[X]) {j : ℕ} (hj : j ≤ n) :
    (degreeSignFlip n (narayanaTransform m p)).coeff j =
      (-1 : ℝ) ^ (n - j) *
        p.sum fun k a => a * (narayanaPolynomial m k).coeff j := by
  rw [coeff_degreeSignFlip_of_le (narayanaTransform m p) hj, coeff_narayanaTransform]

theorem natDegree_narayanaTransform_le (m : ℕ) (p : ℝ[X]) :
    (narayanaTransform m p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_narayanaTransform, Polynomial.sum_def]
  apply Finset.sum_eq_zero
  intro k hk
  have hkdeg : k ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
  rw [coeff_narayanaPolynomial_of_lt (lt_of_le_of_lt hkdeg hj), mul_zero]

theorem narayanaTransform_coeff_sum_reflect
    (m n j : ℕ) (p : ℝ[X]) (hpdeg : p.natDegree ≤ n) (hj : j ≤ n) :
    p.sum (fun k a => a * (narayanaPolynomial m k).coeff j) =
      ∑ i ∈ Finset.range (n - j + 1),
        p.coeff (n - i) * narayanaTransformCoeff m (n - i) j := by
  let f : ℕ → ℝ := fun k => p.coeff k * (narayanaPolynomial m k).coeff j
  have hsum_range :
      p.sum (fun k a => a * (narayanaPolynomial m k).coeff j) =
        ∑ k ∈ Finset.range (n + 1), f k := by
    rw [Polynomial.sum_over_range]
    · exact Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hpdeg)) (by
        intro k hk_big hk_small
        have hkgt : p.natDegree < k := by
          have hnot : ¬ k < p.natDegree + 1 := by simpa [Finset.mem_range] using hk_small
          exact Nat.lt_of_not_ge (by
            intro hk_le
            exact hnot (Nat.lt_succ_iff.mpr hk_le))
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hkgt])
    · intro k
      simp
  have hlow : ∑ k ∈ Finset.range j, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    simp [f, coeff_narayanaPolynomial_of_lt hkj]
  have htail :
      ∑ k ∈ Finset.range (n + 1), f k =
        ∑ k ∈ Finset.Ico j (n + 1), f k := by
    have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_succ_of_le hj)
    rw [hlow, zero_add] at hsplit
    exact hsplit.symm
  rw [hsum_range, htail, Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - j = n - j + 1 := by lia
  rw [hlen]
  rw [← Finset.sum_range_reflect
    (fun i => p.coeff (j + i) * (narayanaPolynomial m (j + i)).coeff j)
    (n - j + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hindex : j + (n - j + 1 - 1 - i) = n - i := by lia
  rw [hindex]
  have hj_le : j ≤ n - i := by lia
  rw [coeff_narayanaPolynomial_of_le hj_le]

/-- Dominici--Johnston--Jordaan root-location input for the generalized
Narayana polynomials, paper Lemma 2.5. -/
abbrev narayanaPolynomialRootLocationStatement : Prop :=
  ∀ m n : ℕ, IsPFPolynomial (narayanaPolynomial m n)

/-- Mao--Wang Theorem 1.1 in zero-aware PF-polynomial form. -/
abbrev narayanaTransformPreservesPFStatement : Prop :=
  ∀ (m : ℕ) {p : ℝ[X]},
    IsPFPolynomial p → IsPFPolynomial (narayanaTransform m p)

/-- Mao--Wang Theorem 1.1 in the paper-facing nonpositive-root form. -/
abbrev narayanaTransformPreservesNonposRootsStatement : Prop :=
  ∀ (m : ℕ) {p : ℝ[X]},
    HasNonnegCoeffs p → p.Splits →
      HasOnlyNonposRoots (narayanaTransform m p)

@[simp] theorem rectangularConvolutionCoeff_zero (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 0 f g 0 = f.coeff 0 * g.coeff 0 := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma]
  have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp [hm]
  simp

@[simp] theorem rectangularConvolutionCoeff_one_zero (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 1 f g 0 = f.coeff 1 * g.coeff 1 := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma]
  have hm : ((Nat.factorial (1 + m) : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp [hm]
  simp

@[simp] theorem rectangularConvolutionCoeff_one_one (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 1 f g 1 =
      f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1 := by
  unfold rectangularConvolutionCoeff rectangularConvolutionGamma
  simp [Finset.sum_range_succ]
  have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
  have hm1 : ((Nat.factorial (1 + m) : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp [hm, hm1]


end RealRooted
