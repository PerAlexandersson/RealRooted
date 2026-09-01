import RealRooted.NarayanaTransformation.Falling

/-!
# Rising-factorial transform preservation.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Su--Yang--Zhang generalized rising-factorial transform, paper Lemma 3.11.
-/
abbrev generalizedRisingFactorialPreservesPFStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

/-- Degree-zero case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_of_natDegree_eq_zero {μ : ℝ}
    {p : ℝ[X]} (hpdeg : p.natDegree = 0) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
  rw [hpC] at hp ⊢
  simpa [risingFactorialPolynomial] using hp

/-- Degree-one case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_of_natDegree_eq_one {μ : ℝ}
    {p : ℝ[X]} (hpdeg : p.natDegree = 1) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  simpa [basisTransform_risingFactorial_eq_self_of_natDegree_eq_one hpdeg] using hp

/-- Degree-two case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_of_natDegree_eq_two {μ : ℝ}
    (hμ : 0 ≤ μ) {p : ℝ[X]} (hpdeg : p.natDegree = 2) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  rw [basisTransform_risingFactorial_eq_quadratic_of_natDegree_eq_two hpdeg]
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hpdeg
  have hp_pos : HasPosLeadingCoeff p := hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have ha : 0 < p.coeff 2 := by
    simpa [HasPosLeadingCoeff, Polynomial.leadingCoeff, hpdeg] using hp_pos
  have hb : 0 ≤ p.coeff 1 := hp.hasNonnegCoeffs 1
  have hc : 0 ≤ p.coeff 0 := hp.hasNonnegCoeffs 0
  have hpsplits : p.Splits := (hp.ne_zero_and_splits hp0).2
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hquad_splits : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X +
      C (p.coeff 0) : ℝ[X]).Splits := by
    simpa [← hpform] using hpsplits
  have hdisc : 4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 :=
    (quadraticPoly_splits_iff_le ha).mp hquad_splits
  have hmu_a : 0 ≤ μ * p.coeff 2 := mul_nonneg hμ ha.le
  have hsquare : p.coeff 1 ^ 2 ≤ (p.coeff 1 + μ * p.coeff 2) ^ 2 := by
    nlinarith [sq_nonneg (μ * p.coeff 2), mul_nonneg hb hmu_a]
  have hdisc' : 4 * p.coeff 2 * p.coeff 0 ≤ (p.coeff 1 + μ * p.coeff 2) ^ 2 :=
    hdisc.trans hsquare
  exact IsPFPolynomial.of_realRooted_nonneg
    (((nonnegCoeffs_C_mul ha.le (hasNonnegCoeffs_X.pow 2)).add
      (nonnegCoeffs_C_mul (add_nonneg hb hmu_a) hasNonnegCoeffs_X)).add
        (hasNonnegCoeffs_C hc))
    (quadraticPoly_splits_of_le ha hdisc')

private theorem generalizedRisingFactorialPreservesPF_shiftPrec {μ : ℝ}
    (hμ : 0 < μ) :
    ∀ n (p : ℝ[X]), p.natDegree = n → p ≠ 0 → IsPFPolynomial p →
      let q := basisTransform (risingFactorialPolynomial μ) p
      IsPFPolynomial q ∧ Prec (q.comp (X + C μ)) q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hpdeg hp0 hp
      by_cases hn0 : n = 0
      · have hpdeg0 : p.natDegree = 0 := by lia
        have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg0
        have htransform : basisTransform (risingFactorialPolynomial μ) p = p := by
          rw [hpC]
          simp [risingFactorialPolynomial]
        rw [htransform]
        dsimp
        have hpcomp : p.comp (X + C μ) = p := by
          rw [hpC]
          simp
        rw [hpcomp]
        exact ⟨hp, prec_refl hp0 (hp.ne_zero_and_splits hp0).2⟩
      · have hnpos : 0 < p.natDegree := by lia
        rcases hp.exists_X_sub_C_factor_of_pos_natDegree hnpos with
          ⟨u, q, hu, hfactor, hq, hqdeg⟩
        have hq0 : q ≠ 0 := by
          intro hqzero
          apply hp0
          simp [hfactor, hqzero]
        have ihq := ih q.natDegree (by lia) q rfl hq0 hq
        have hstep := risingFactorialStep_pf_shiftPrec hμ.le (neg_nonneg.mpr hu)
          ihq.1 ihq.2
        have hfactor' : p = (X + C (-u)) * q := by simpa [sub_eq_add_neg] using hfactor
        rw [hfactor', basisTransform_risingFactorial_mul_X_add_C]
        exact hstep

/-- Positive-degree leaf for the Su--Yang--Zhang generalized rising-factorial
transform. -/
abbrev generalizedRisingFactorialPreservesPFPositiveDegreeStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    0 < p.natDegree →
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

/-- Degree-at-least-three leaf for the Su--Yang--Zhang generalized
rising-factorial transform. -/
abbrev generalizedRisingFactorialPreservesPFDegreeAtLeastThreeStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    3 ≤ p.natDegree →
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

/-- Degree-at-least-three case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_degreeAtLeastThree :
    generalizedRisingFactorialPreservesPFDegreeAtLeastThreeStatement := by
  intro μ hμ p hpdeg hp
  exact (generalizedRisingFactorialPreservesPF_shiftPrec hμ p.natDegree p rfl
    (by intro hpzero; simp [hpzero] at hpdeg) hp).1

/-- Degree-at-least-two case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_degreeAtLeastTwo {μ : ℝ} (hμ : 0 < μ)
    {p : ℝ[X]} (hpdeg : 2 ≤ p.natDegree) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  by_cases hdeg2 : p.natDegree = 2
  · exact generalizedRisingFactorialPreservesPF_of_natDegree_eq_two hμ.le hdeg2 hp
  · exact generalizedRisingFactorialPreservesPF_degreeAtLeastThree hμ (by lia) hp

/-- Positive-degree case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_positiveDegree :
    generalizedRisingFactorialPreservesPFPositiveDegreeStatement := by
  intro μ hμ p hpdeg hp
  by_cases hdeg1 : p.natDegree = 1
  · exact generalizedRisingFactorialPreservesPF_of_natDegree_eq_one hdeg1 hp
  · exact generalizedRisingFactorialPreservesPF_degreeAtLeastTwo hμ (by lia) hp

/-- Su--Yang--Zhang generalized rising-factorial transform preserves PF polynomials. -/
theorem generalizedRisingFactorialPreservesPF :
    generalizedRisingFactorialPreservesPFStatement := by
  intro μ hμ p hp
  rcases Nat.eq_zero_or_pos p.natDegree with hpdeg | hpdeg
  · exact generalizedRisingFactorialPreservesPF_of_natDegree_eq_zero hpdeg hp
  · exact generalizedRisingFactorialPreservesPF_positiveDegree hμ hpdeg hp


end RealRooted
