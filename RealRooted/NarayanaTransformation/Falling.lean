import RealRooted.NarayanaTransformation.Basis

/-!
# Falling-factorial inverse transform.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Brenti's falling-factorial inverse transform, paper Lemma 3.9 / Brenti
Theorem 2.4.2. -/
abbrev brentiFallingFactorialStatement : Prop :=
  ∀ {p : ℝ[X]},
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Degree-zero case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_of_natDegree_eq_zero {p : ℝ[X]}
    (hpdeg : p.natDegree = 0)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
  rw [hpC] at h ⊢
  simpa [fallingFactorialPolynomial] using h

/-- Degree-one case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_of_natDegree_eq_one {p : ℝ[X]}
    (hpdeg : p.natDegree = 1)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  simpa [basisTransform_fallingFactorial_eq_self_of_natDegree_eq_one hpdeg] using h

private theorem brentiFallingFactorial_of_natDegree_eq_two_pos_leading {p : ℝ[X]}
    (hpdeg : p.natDegree = 2) (hpos : 0 < p.coeff 2)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  let q := basisTransform fallingFactorialPolynomial p
  have hqform : q = C (p.coeff 2) * X ^ 2 + C (p.coeff 1 - p.coeff 2) * X +
      C (p.coeff 0) := by
    exact basisTransform_fallingFactorial_eq_quadratic_of_natDegree_eq_two hpdeg
  have hqdeg : q.natDegree = 2 := by
    rw [hqform]
    exact Polynomial.natDegree_quadratic hpos.ne'
  have hqlead_eq : q.leadingCoeff = p.coeff 2 := by
    rw [Polynomial.leadingCoeff, hqdeg, hqform]
    simp
  have hqlead : HasPosLeadingCoeff q := by
    rw [HasPosLeadingCoeff, hqlead_eq]
    exact hpos
  have hq0 : q ≠ 0 := hqlead.ne_zero
  rcases h with hzero | ⟨hqsplits, hqroots⟩
  · exact (hq0 hzero).elim
  have hqnn : HasNonnegCoeffs q :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hqsplits).mpr
      ⟨hqlead, hqroots⟩).1
  have hd : 0 ≤ p.coeff 1 - p.coeff 2 := by
    have hcoeff := hqnn 1
    rw [hqform] at hcoeff
    simpa using hcoeff
  have hc : 0 ≤ p.coeff 0 := by
    have hcoeff := hqnn 0
    rw [hqform] at hcoeff
    simpa using hcoeff
  have hb : 0 ≤ p.coeff 1 := by nlinarith
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hpnn : HasNonnegCoeffs p := by
    rw [hpform]
    exact ((nonnegCoeffs_C_mul hpos.le (hasNonnegCoeffs_X.pow 2)).add
      (nonnegCoeffs_C_mul hb hasNonnegCoeffs_X)).add (hasNonnegCoeffs_C hc)
  have hqquad_splits : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1 - p.coeff 2) * X +
      C (p.coeff 0) : ℝ[X]).Splits := by
    rwa [← hqform]
  have hdisc_q : 4 * p.coeff 2 * p.coeff 0 ≤ (p.coeff 1 - p.coeff 2) ^ 2 :=
    (quadraticPoly_splits_iff_le hpos).mp hqquad_splits
  have hdisc_p : 4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 := by
    nlinarith [sq_nonneg (p.coeff 2), mul_nonneg hd hpos.le]
  have hpsplits_quad : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X +
      C (p.coeff 0) : ℝ[X]).Splits :=
    quadraticPoly_splits_of_le hpos hdisc_p
  have hpsplits : p.Splits := by simpa [← hpform] using hpsplits_quad
  exact HasOnlyNonposRoots.of_nonnegCoeffs_splits hpnn hpsplits

/-- Degree-two case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_of_natDegree_eq_two {p : ℝ[X]}
    (hpdeg : p.natDegree = 2)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hpdeg
  have hcoeff2_ne : p.coeff 2 ≠ 0 := by
    simpa [Polynomial.leadingCoeff, hpdeg] using (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  rcases lt_or_gt_of_ne hcoeff2_ne with hneg | hpos
  · have hnegdeg : (-p).natDegree = 2 := by rw [Polynomial.natDegree_neg, hpdeg]
    have hnegpos : 0 < (-p).coeff 2 := by
      simp
      linarith
    have htransform_neg : basisTransform fallingFactorialPolynomial (-p) =
        -basisTransform fallingFactorialPolynomial p := by
      rw [show (-p : ℝ[X]) = (-1 : ℝ) • p by simp, basisTransform_smul]
      simp
    have hnegroots : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial (-p)) := by
      rw [htransform_neg]
      exact h.neg
    have hpneg :=
      brentiFallingFactorial_of_natDegree_eq_two_pos_leading hnegdeg hnegpos hnegroots
    exact hpneg.of_neg
  · exact brentiFallingFactorial_of_natDegree_eq_two_pos_leading hpdeg hpos h

/-- Positive-degree leaf for Brenti's falling-factorial inverse transform. -/
abbrev brentiFallingFactorialPositiveDegreeStatement : Prop :=
  ∀ {p : ℝ[X]},
    0 < p.natDegree →
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Degree-at-least-three leaf for Brenti's falling-factorial inverse transform. -/
abbrev brentiFallingFactorialDegreeAtLeastThreeStatement : Prop :=
  ∀ {p : ℝ[X]},
    3 ≤ p.natDegree →
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Degree-at-least-three case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_degreeAtLeastThree :
    brentiFallingFactorialDegreeAtLeastThreeStatement := by
  intro p hpdeg h
  let q := basisTransform fallingFactorialPolynomial p
  have hinv : basisTransform touchard q = p :=
    basisTransform_touchard_fallingFactorial_leftInverse p
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hpdeg
  rcases h with hqzero | ⟨hqsplits, hqroots⟩
  · exfalso
    change q = 0 at hqzero
    apply hp0
    rw [← hinv, hqzero]
    simp
  have hq0 : q ≠ 0 := by
    intro hqzero
    apply hp0
    rw [← hinv, hqzero]
    simp
  have hq_lc_ne : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  rcases lt_or_gt_of_ne hq_lc_ne with hqneg | hqpos
  · have hnq_splits : (-q).Splits := hqsplits.neg
    have hnq_pos : HasPosLeadingCoeff (-q) := hasPosLeadingCoeff_neg hqneg
    have hnq_roots : ∀ r ∈ (-q).roots, r ≤ 0 := by simpa [Polynomial.roots_neg] using hqroots
    have hnq_nn : HasNonnegCoeffs (-q) :=
      ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hnq_splits).mpr
        ⟨hnq_pos, hnq_roots⟩).1
    have hnq_pf : IsPFPolynomial (-q) :=
      IsPFPolynomial.of_realRooted_nonneg hnq_nn hnq_splits
    have htransform_neg : basisTransform touchard (-q) = -basisTransform touchard q := by
      rw [show (-q : ℝ[X]) = (-1 : ℝ) • q by simp, basisTransform_smul]
      simp
    have hresult := (touchardTransformPreservesPF hnq_pf).hasOnlyNonposRoots
    rw [htransform_neg, hinv] at hresult
    exact hresult.of_neg
  · have hq_pos : HasPosLeadingCoeff q := hqpos
    have hq_nn : HasNonnegCoeffs q :=
      ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hqsplits).mpr
        ⟨hq_pos, hqroots⟩).1
    have hq_pf : IsPFPolynomial q :=
      IsPFPolynomial.of_realRooted_nonneg hq_nn hqsplits
    have hresult := (touchardTransformPreservesPF hq_pf).hasOnlyNonposRoots
    rwa [hinv] at hresult

/-- Degree-at-least-two case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_degreeAtLeastTwo {p : ℝ[X]} (hpdeg : 2 ≤ p.natDegree)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  by_cases hdeg2 : p.natDegree = 2
  · exact brentiFallingFactorial_of_natDegree_eq_two hdeg2 h
  · exact brentiFallingFactorial_degreeAtLeastThree (by lia) h

/-- Positive-degree case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_positiveDegree :
    brentiFallingFactorialPositiveDegreeStatement := by
  intro p hpdeg h
  by_cases hdeg1 : p.natDegree = 1
  · exact brentiFallingFactorial_of_natDegree_eq_one hdeg1 h
  · exact brentiFallingFactorial_degreeAtLeastTwo (by lia) h

/-- Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial : brentiFallingFactorialStatement := by
  intro p h
  rcases Nat.eq_zero_or_pos p.natDegree with hpdeg | hpdeg
  · exact brentiFallingFactorial_of_natDegree_eq_zero hpdeg h
  · exact brentiFallingFactorial_positiveDegree hpdeg h


end RealRooted
