import RealRooted.NarayanaTransformation.Coefficients

/-!
# Low-degree rectangular additive convolution.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

private theorem rectangularConvolutionGamma_two_zero_zero (m : ℕ) :
    rectangularConvolutionGamma m 2 0 0 = 1 := by
  unfold rectangularConvolutionGamma
  norm_num
  exact (Nat.factorial_pos (2 + m)).ne'

private theorem rectangularConvolutionGamma_two_zero_one (m : ℕ) :
    rectangularConvolutionGamma m 2 0 1 = 1 := by
  unfold rectangularConvolutionGamma
  norm_num
  exact ⟨(Nat.factorial_pos (2 + m)).ne', (Nat.factorial_pos (1 + m)).ne'⟩

private theorem rectangularConvolutionGamma_two_one_zero (m : ℕ) :
    rectangularConvolutionGamma m 2 1 0 = 1 := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_two_zero_one m

private theorem rectangularConvolutionGamma_two_zero_two (m : ℕ) :
    rectangularConvolutionGamma m 2 0 2 = 1 := by
  unfold rectangularConvolutionGamma
  norm_num
  exact ⟨(Nat.factorial_pos (2 + m)).ne', (Nat.factorial_pos m).ne'⟩

private theorem rectangularConvolutionGamma_two_two_zero (m : ℕ) :
    rectangularConvolutionGamma m 2 2 0 = 1 := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_two_zero_two m

private theorem rectangularConvolutionGamma_two_one_one (m : ℕ) :
    rectangularConvolutionGamma m 2 1 1 = ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) := by
  unfold rectangularConvolutionGamma
  norm_num
  rw [show 2 + m = m + 2 by lia, show 1 + m = m + 1 by lia]
  rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  norm_num
  have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hm, hm2]
  ring

private theorem rectangularConvolutionCoeff_two_zero (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 2 f g 0 = f.coeff 2 * g.coeff 2 := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma_two_zero_zero]

private theorem rectangularConvolutionCoeff_two_one (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 2 f g 1 =
      f.coeff 2 * g.coeff 1 + f.coeff 1 * g.coeff 2 := by
  unfold rectangularConvolutionCoeff
  simp [Finset.sum_range_succ, rectangularConvolutionGamma_two_zero_one,
    rectangularConvolutionGamma_two_one_zero]

private theorem rectangularConvolutionCoeff_two_two (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 2 f g 2 =
      f.coeff 2 * g.coeff 0 +
        (((m : ℝ) + 1) / (2 * ((m : ℝ) + 2))) * (f.coeff 1 * g.coeff 1) +
          f.coeff 0 * g.coeff 2 := by
  unfold rectangularConvolutionCoeff
  simp [Finset.sum_range_succ, rectangularConvolutionGamma_two_zero_two,
    rectangularConvolutionGamma_two_one_one, rectangularConvolutionGamma_two_two_zero]
  ring

theorem rectangularAdditiveConvolution_zero_right (m : ℕ) (f g : ℝ[X]) :
    rectangularAdditiveConvolution m 0 f g = C (f.coeff 0 * g.coeff 0) := by
  ext j
  rcases j with _ | j
  · simp [rectangularAdditiveConvolution, rectangularConvolutionCoeff,
      rectangularConvolutionGamma]
    have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
    field_simp [hm]
    simp
  · rw [coeff_rectangularAdditiveConvolution_of_gt m 0 f g (by simp), Polynomial.coeff_C]
    simp

theorem rectangularAdditiveConvolution_one (m : ℕ) (f g : ℝ[X]) :
    rectangularAdditiveConvolution m 1 f g =
      C (f.coeff 1 * g.coeff 1) * X +
        C (f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1) := by
  ext j
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 1 f g (by norm_num : 0 ≤ 1)]
    simp
  · rcases j with _ | j
    · rw [coeff_rectangularAdditiveConvolution_of_le m 1 f g le_rfl]
      simp
    · rw [coeff_rectangularAdditiveConvolution_of_gt m 1 f g (by lia)]
      simp

theorem rectangularAdditiveConvolution_two (m : ℕ) (f g : ℝ[X]) :
    rectangularAdditiveConvolution m 2 f g =
      C (f.coeff 2 * g.coeff 2) * X ^ 2 +
        C (f.coeff 2 * g.coeff 1 + f.coeff 1 * g.coeff 2) * X +
          C (f.coeff 2 * g.coeff 0 +
            (((m : ℝ) + 1) / (2 * ((m : ℝ) + 2))) * (f.coeff 1 * g.coeff 1) +
              f.coeff 0 * g.coeff 2) := by
  ext j
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 2 f g (by norm_num : 0 ≤ 2),
      rectangularConvolutionCoeff_two_two]
    simp
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 2 f g (by norm_num : 1 ≤ 2),
      rectangularConvolutionCoeff_two_one]
    simp only [map_mul, map_add, zero_add, coeff_add, coeff_mul_X, mul_coeff_zero,
      coeff_C_zero, coeff_mul_C, coeff_C_succ, zero_mul, coeff_C_mul, mul_zero,
      add_zero, right_eq_add]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 2 f g le_rfl,
      rectangularConvolutionCoeff_two_zero]
    simp only [map_mul, map_add, zero_add, Nat.reduceAdd, coeff_add, coeff_mul_X,
      coeff_mul_C, coeff_C_succ, zero_mul, add_zero, coeff_C_mul, mul_zero]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  · rw [coeff_rectangularAdditiveConvolution_of_gt m 2 f g (by lia)]
    simp

/-- Degree-zero base case of the Gribinski--Marcus rectangular convolution
preservation theorem. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_zero {m : ℕ} {f g : ℝ[X]}
    (_hfdeg : f.natDegree = 0) (_hgdeg : g.natDegree = 0)
    (_hflead : 0 < f.leadingCoeff) (_hglead : 0 < g.leadingCoeff)
    (_hfroots : HasOnlyNonnegRoots f) (_hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m 0 f g) := by
  rw [rectangularAdditiveConvolution_zero_right]
  right
  refine ⟨by simp, ?_⟩
  intro r hr
  have hroots : (C (f.coeff 0 * g.coeff 0) : ℝ[X]).roots = 0 := Polynomial.roots_C _
  have hroot0 : r ∈ (0 : Multiset ℝ) := hroots ▸ hr
  cases hroot0

/-- Degree-one base case of the Gribinski--Marcus rectangular convolution
preservation theorem. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_one {m : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 1)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m 1 f g) := by
  rw [rectangularAdditiveConvolution_one]
  have hf1pos : 0 < f.coeff 1 := by simpa [Polynomial.leadingCoeff, hfdeg] using hflead
  have hg1pos : 0 < g.coeff 1 := by simpa [Polynomial.leadingCoeff, hgdeg] using hglead
  have hf0nonpos : f.coeff 0 ≤ 0 :=
    hfroots.coeff_zero_nonpos_of_natDegree_eq_one hfdeg hflead
  have hg0nonpos : g.coeff 0 ≤ 0 :=
    hgroots.coeff_zero_nonpos_of_natDegree_eq_one hgdeg hglead
  apply hasOnlyNonnegRoots_C_mul_X_add_C_of_pos_nonpos
  · exact mul_pos hf1pos hg1pos
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hf1pos.le hg0nonpos)
      (mul_nonpos_of_nonpos_of_nonneg hf0nonpos hg1pos.le)

private theorem quadratic_data_of_hasOnlyNonnegRoots {p : ℝ[X]}
    (hpdeg : p.natDegree = 2) (hplead : 0 < p.leadingCoeff)
    (hproots : HasOnlyNonnegRoots p) :
    0 < p.coeff 2 ∧ p.coeff 1 ≤ 0 ∧ 0 ≤ p.coeff 0 ∧ p.Splits ∧
      4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 := by
  have h2pos : 0 < p.coeff 2 := by simpa [Polynomial.leadingCoeff, hpdeg] using hplead
  have hfliproots : HasOnlyNonposRoots (degreeSignFlip 2 p) :=
    hproots.degreeSignFlip_hasOnlyNonposRoots (by rw [hpdeg])
  have hp0 : p ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hplead.ne'
  rcases hproots with hpzero | ⟨hpsplits, _hroots⟩
  · exact (hp0 hpzero).elim
  have hflip0 : degreeSignFlip 2 p ≠ 0 := by
    intro hzero
    have hcoeff : (degreeSignFlip 2 p).coeff 2 = 0 := by simp [hzero]
    rw [coeff_degreeSignFlip_of_le p le_rfl] at hcoeff
    norm_num at hcoeff
    exact h2pos.ne' hcoeff
  rcases hfliproots with hflipzero | ⟨hflipsplits, hflip_roots⟩
  · exact (hflip0 hflipzero).elim
  have hfliplead : HasPosLeadingCoeff (degreeSignFlip 2 p) := by
    rw [HasPosLeadingCoeff, leadingCoeff_degreeSignFlip_of_coeff_ne_zero h2pos.ne']
    exact h2pos
  have hflipnn : HasNonnegCoeffs (degreeSignFlip 2 p) :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hflipsplits).mpr
      ⟨hfliplead, hflip_roots⟩).1
  have h0 : 0 ≤ p.coeff 0 := by
    have hcoeff := hflipnn 0
    rw [coeff_degreeSignFlip_of_le p (by norm_num : 0 ≤ 2)] at hcoeff
    simpa using hcoeff
  have h1 : p.coeff 1 ≤ 0 := by
    have hcoeff := hflipnn 1
    rw [coeff_degreeSignFlip_of_le p (by norm_num : 1 ≤ 2)] at hcoeff
    norm_num at hcoeff
    linarith
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hquad_splits : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X +
      C (p.coeff 0) : ℝ[X]).Splits := by
    simpa [← hpform] using hpsplits
  have hdisc : 4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 :=
    (quadraticPoly_splits_iff_le h2pos).mp hquad_splits
  exact ⟨h2pos, h1, h0, hpsplits, hdisc⟩

/-- Degree-two base case of the Gribinski--Marcus rectangular convolution
preservation theorem. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_two
    {m : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 2)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m 2 f g) := by
  rcases quadratic_data_of_hasOnlyNonnegRoots hfdeg hflead hfroots with
    ⟨hf2pos, hf1nonpos, hf0nonneg, _hfsplits, hfdisc⟩
  rcases quadratic_data_of_hasOnlyNonnegRoots hgdeg hglead hgroots with
    ⟨hg2pos, hg1nonpos, hg0nonneg, _hgsplits, hgdisc⟩
  let γ : ℝ := ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2))
  let A : ℝ := f.coeff 2 * g.coeff 2
  let B : ℝ := f.coeff 2 * g.coeff 1 + f.coeff 1 * g.coeff 2
  let D : ℝ := f.coeff 2 * g.coeff 0 + γ * (f.coeff 1 * g.coeff 1) +
    f.coeff 0 * g.coeff 2
  let q := rectangularAdditiveConvolution m 2 f g
  have hqform : q = C A * X ^ 2 + C B * X + C D := by
    dsimp [q, A, B, D, γ]
    exact rectangularAdditiveConvolution_two m f g
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hf2pos hg2pos
  have hBnonpos : B ≤ 0 := by
    dsimp [B]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hf2pos.le hg1nonpos)
      (mul_nonpos_of_nonpos_of_nonneg hf1nonpos hg2pos.le)
  have hγnonneg : 0 ≤ γ := by
    dsimp [γ]
    positivity
  have hγle : γ ≤ (1 : ℝ) / 2 := by
    dsimp [γ]
    have hden : 0 < 2 * ((m : ℝ) + 2) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (add_nonneg (mul_nonneg hf2pos.le hg0nonneg)
        (mul_nonneg hγnonneg (mul_nonneg_of_nonpos_of_nonpos hf1nonpos hg1nonpos)))
      (mul_nonneg hf0nonneg hg2pos.le)
  have hfg11_nonneg : 0 ≤ f.coeff 1 * g.coeff 1 :=
    mul_nonneg_of_nonpos_of_nonpos hf1nonpos hg1nonpos
  have hcross_nonneg : 0 ≤ f.coeff 2 * g.coeff 2 * (f.coeff 1 * g.coeff 1) :=
    mul_nonneg (mul_nonneg hf2pos.le hg2pos.le) hfg11_nonneg
  have hfdisc_scaled : 4 * f.coeff 2 * f.coeff 0 * g.coeff 2 ^ 2 ≤
      f.coeff 1 ^ 2 * g.coeff 2 ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hfdisc (sq_nonneg (g.coeff 2))
    nlinarith
  have hgdisc_scaled : 4 * g.coeff 2 * g.coeff 0 * f.coeff 2 ^ 2 ≤
      g.coeff 1 ^ 2 * f.coeff 2 ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hgdisc (sq_nonneg (f.coeff 2))
    nlinarith
  have hcross_scaled : 4 * γ * (f.coeff 2 * g.coeff 2 * (f.coeff 1 * g.coeff 1)) ≤
      2 * (f.coeff 2 * g.coeff 2 * (f.coeff 1 * g.coeff 1)) := by
    have hfactor : 4 * γ ≤ (2 : ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right hfactor hcross_nonneg
  have hdisc : 4 * A * D ≤ B ^ 2 := by
    dsimp [A, B, D]
    nlinarith [hfdisc_scaled, hgdisc_scaled, hcross_scaled]
  have hqquad_splits : (C A * X ^ 2 + C B * X + C D : ℝ[X]).Splits :=
    quadraticPoly_splits_of_le hApos hdisc
  have hqsplits : q.Splits := by simpa [← hqform] using hqquad_splits
  have hqdeg_le : q.natDegree ≤ 2 := by
    dsimp [q]
    exact natDegree_rectangularAdditiveConvolution_le m 2 f g
  have hqflipform : degreeSignFlip 2 q = C A * X ^ 2 + C (-B) * X + C D := by
    rw [hqform]
    exact degreeSignFlip_two_quadratic A B D
  have hqflipnn : HasNonnegCoeffs (degreeSignFlip 2 q) := by
    rw [hqflipform]
    exact ((nonnegCoeffs_C_mul hApos.le (hasNonnegCoeffs_X.pow 2)).add
      (nonnegCoeffs_C_mul (neg_nonneg.mpr hBnonpos) hasNonnegCoeffs_X)).add
        (hasNonnegCoeffs_C hDnonneg)
  have hqflipsplits : (degreeSignFlip 2 q).Splits :=
    degreeSignFlip_splits_of_splits hqdeg_le hqsplits
  have hflip_roots_nonpos : ∀ r ∈ (degreeSignFlip 2 q).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hqflipsplits hqflipnn
  right
  refine ⟨hqsplits, ?_⟩
  intro r hr
  have hneg_mem : -r ∈ (degreeSignFlip 2 q).roots := by
    rw [roots_degreeSignFlip hqdeg_le]
    exact Multiset.mem_map.mpr ⟨r, hr, rfl⟩
  have hneg_nonpos : -r ≤ 0 := hflip_roots_nonpos (-r) hneg_mem
  linarith


end RealRooted
