import RealRooted.NarayanaTransformation.Gamma

/-!
# Narayana transformation final endpoints.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Generalized Narayana polynomials split over the reals. -/
theorem splits_narayanaPolynomial (m n : ℕ) :
    (narayanaPolynomial m n).Splits := by
  rcases n with _ | n
  · simp
  · exact (prec_narayanaPolynomial_succ m n).1.2

/-- The gamma polynomial of the binomial-square Narayana polynomial is itself
real-rooted, with all roots nonpositive. -/
theorem narayanaZeroGammaPolynomial_realRooted (n : ℕ) :
    (narayanaZeroGammaPolynomial n ≠ 0 ∧ (narayanaZeroGammaPolynomial n).Splits) ∧
      HasRootsNonpos (narayanaZeroGammaPolynomial n) := by
  apply isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    (natDegree_narayanaZeroGammaPolynomial_le n)
  · rw [gammaTransform_narayanaZeroGammaPolynomial]
    exact narayanaPolynomial_ne_zero 0 n
  · rw [gammaTransform_narayanaZeroGammaPolynomial]
    exact splits_narayanaPolynomial 0 n
  · rw [gammaTransform_narayanaZeroGammaPolynomial]
    intro r hr
    exact narayanaPolynomial_root_nonpos
      ((Polynomial.mem_roots (narayanaPolynomial_ne_zero 0 n)).mp hr)

theorem splits_narayanaZeroGammaPolynomial (n : ℕ) :
    (narayanaZeroGammaPolynomial n).Splits :=
  (narayanaZeroGammaPolynomial_realRooted n).1.2

/-- Consecutive gamma polynomials of the binomial-square Narayana family are
in proper position. -/
theorem prec_narayanaZeroGammaPolynomial_succ (n : ℕ) :
    Prec (narayanaZeroGammaPolynomial n)
      (narayanaZeroGammaPolynomial (n + 1)) := by
  cases n with
  | zero =>
      simpa [narayanaZeroGammaPolynomial] using
        (prec_refl (by simp) (by simp) : Prec (1 : ℝ[X]) 1)
  | succ n =>
      rw [← prec_gammaTransform_succ_iff
        (natDegree_narayanaZeroGammaPolynomial_le (n + 1))
        (natDegree_narayanaZeroGammaPolynomial_le (n + 2))]
      · rw [gammaTransform_narayanaZeroGammaPolynomial,
          gammaTransform_narayanaZeroGammaPolynomial]
        exact prec_narayanaPolynomial_succ 0 n
      · intro k
        by_cases hk : k ≤ (n + 1) / 2
        · rw [coeff_narayanaZeroGammaPolynomial_of_le hk]
          positivity
        · rw [coeff_narayanaZeroGammaPolynomial_of_lt (by lia)]
      · intro k
        by_cases hk : k ≤ (n + 2) / 2
        · rw [coeff_narayanaZeroGammaPolynomial_of_le hk]
          positivity
        · rw [coeff_narayanaZeroGammaPolynomial_of_lt (by lia)]
      · rw [coeff_narayanaZeroGammaPolynomial_of_le (by lia)]
        norm_num
      · rw [coeff_narayanaZeroGammaPolynomial_of_le (by lia)]
        norm_num

/-- The generalized Narayana polynomials are PF polynomials. -/
theorem narayanaPolynomialRootLocation :
    narayanaPolynomialRootLocationStatement :=
  fun m n =>
    IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_narayanaPolynomial m n)
      (splits_narayanaPolynomial m n)

/-- The Narayana transform preserves PF polynomials, reduced to the
Gribinski--Marcus rectangular additive convolution theorem. -/
theorem narayanaTransformPreservesPF :
    narayanaTransformPreservesPFStatement := by
  intro m p hp
  refine IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    hp.hasNonnegCoeffs.narayanaTransform ?_
  by_cases hp0 : p = 0
  · left
    simp [hp0, narayanaTransform]
  · right
    set n := p.natDegree with hn
    have hpdeg : p.natDegree ≤ n := by rw [hn]
    have hqdeg : (narayanaTransform m p).natDegree ≤ n := by
      simpa [hn] using natDegree_narayanaTransform_le m p
    have hpcoeff : p.coeff n ≠ 0 := by
      rw [hn, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hfdeg : (degreeSignFlip n p).natDegree = n :=
      natDegree_degreeSignFlip_eq_of_coeff_ne_zero hpcoeff
    have hflead : 0 < (degreeSignFlip n p).leadingCoeff := by
      rw [leadingCoeff_degreeSignFlip_of_coeff_ne_zero hpcoeff, hn,
        Polynomial.coeff_natDegree]
      exact hp.hasNonnegCoeffs.pos_leadingCoeff hp0
    have hNdeg : (narayanaPolynomial m n).natDegree ≤ n := by rw [natDegree_narayanaPolynomial]
    have hNcoeff : (narayanaPolynomial m n).coeff n ≠ 0 := by simp
    have hgdeg : (degreeSignFlip n (narayanaPolynomial m n)).natDegree = n :=
      natDegree_degreeSignFlip_eq_of_coeff_ne_zero hNcoeff
    have hglead : 0 < (degreeSignFlip n (narayanaPolynomial m n)).leadingCoeff := by
      rw [leadingCoeff_degreeSignFlip_of_coeff_ne_zero hNcoeff,
        coeff_narayanaPolynomial_of_le le_rfl]
      simp
    have hfroots : HasOnlyNonnegRoots (degreeSignFlip n p) :=
      hp.hasOnlyNonposRoots.degreeSignFlip_hasOnlyNonnegRoots hpdeg
    have hgroots : HasOnlyNonnegRoots (degreeSignFlip n (narayanaPolynomial m n)) :=
      (narayanaPolynomialRootLocation m n).hasOnlyNonposRoots
        |>.degreeSignFlip_hasOnlyNonnegRoots hNdeg
    have hconv :
        HasOnlyNonnegRoots
          (rectangularAdditiveConvolution m n (degreeSignFlip n p)
            (degreeSignFlip n (narayanaPolynomial m n))) :=
      rectangularAdditiveConvolutionPreservesNonnegRoots
        (m := m) (n := n)
        (f := degreeSignFlip n p)
        (g := degreeSignFlip n (narayanaPolynomial m n))
        hfdeg hgdeg hflead hglead hfroots hgroots
    have hconv_eq :
        rectangularAdditiveConvolution m n (degreeSignFlip n p)
            (degreeSignFlip n (narayanaPolynomial m n)) =
          degreeSignFlip n (narayanaTransform m p) :=
      rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_eq m n p hpdeg
    have hsign : HasOnlyNonnegRoots (degreeSignFlip n (narayanaTransform m p)) := by
      simpa [hconv_eq] using hconv
    have hsign_splits : (degreeSignFlip n (narayanaTransform m p)).Splits := by
      rcases hsign with hzero | ⟨hsplits, _⟩
      · simp [hzero]
      · exact hsplits
    exact splits_of_degreeSignFlip_splits hqdeg hsign_splits

/-- Paper-facing nonpositive-root form of the Narayana transform theorem. -/
theorem narayanaTransformPreservesNonposRoots :
    narayanaTransformPreservesNonposRootsStatement := by
  intro m p hpnn hpsplits
  exact (narayanaTransformPreservesPF m
    (IsPFPolynomial.of_realRooted_nonneg hpnn hpsplits)).hasOnlyNonposRoots

end RealRooted
