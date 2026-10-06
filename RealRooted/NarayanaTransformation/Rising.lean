import RealRooted.NarayanaTransformation.Falling

/-!
# Rising-factorial transform preservation.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

private theorem generalizedRisingFactorialPreservesPF_shiftStrictInterl {μ : ℝ}
    (hμ : 0 < μ) :
    ∀ n (p : ℝ[X]), p.natDegree = n → p ≠ 0 → IsPFPolynomial p →
      let q := basisTransform (risingFactorialPolynomial μ) p
      IsPFPolynomial q ∧ StrictInterl (q.comp (X + C μ)) q := by
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
        exact ⟨hp, StrictInterl.refl hp0 (hp.ne_zero_and_splits hp0).2⟩
      · have hnpos : 0 < p.natDegree := by lia
        rcases hp.exists_X_sub_C_factor_of_pos_natDegree hnpos with
          ⟨u, q, hu, hfactor, hq, hqdeg⟩
        have hq0 : q ≠ 0 := by
          intro hqzero
          apply hp0
          simp [hfactor, hqzero]
        have ihq := ih q.natDegree (by lia) q rfl hq0 hq
        have hstep := risingFactorialStep_pf_shiftStrictInterl hμ.le (neg_nonneg.mpr hu)
          ihq.1 ihq.2
        have hfactor' : p = (X + C (-u)) * q := by simpa [sub_eq_add_neg] using hfactor
        rw [hfactor', basisTransform_risingFactorial_mul_X_add_C]
        exact hstep

/-- Su--Yang--Zhang generalized rising-factorial transform preserves PF polynomials. -/
theorem generalizedRisingFactorialPreservesPF :
    ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
      IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  intro μ hμ p hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using IsPFPolynomial.zero
  · exact (generalizedRisingFactorialPreservesPF_shiftStrictInterl hμ p.natDegree p rfl
      hp0 hp).1


end RealRooted
