import RealRooted.AffineDerivative
import RealRooted.EulerOperator.OrderNumerator.Basic
import RealRooted.EulerOperator.Polar.Pencil

/-!
# Pólya-frequency preservation for the order-numerator step

The strict and tight parameter regimes have different degree behaviour.  This
leaf keeps both hypotheses explicit.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- In the strict regime, the order-numerator step preserves Pólya-frequency
polynomials. -/
theorem orderNumeratorStep_isPF_strict
    {m D : ℕ} {p : ℝ[X]} (hm : 1 ≤ m)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = m)
    (hpzero : p.coeff 0 ≠ 0) {c : ℝ} (hc : 0 < c)
    (hbound : (m : ℝ) < (D : ℝ) + 1 - c) :
    IsPFPolynomial (orderNumeratorStep c D p) := by
  let a := (D : ℝ) + 1 - c
  have hp0 : p ≠ 0 := fun h => hpzero (by simp [h])
  have hcore : Prec (C a * p + (1 - X) * p.derivative) p := by
    apply prec_affine_derivative_of_nonnegCoeffs
    · exact (hp.ne_zero_and_splits hp0).2
    · simpa [hpdeg] using hm
    · exact hp.hasNonnegCoeffs
    · simpa [a, hpdeg] using hbound
  have hcoreNN : HasNonnegCoeffs (C a * p + (1 - X) * p.derivative) := by
    have hscalar : HasNonnegCoeffs (C (a - m) * p) := by
      intro k
      rw [coeff_C_mul]
      exact mul_nonneg (by linarith) (hp.hasNonnegCoeffs k)
    have hsum := hscalar.add
      (hp.hasNonnegCoeffs.polarTheta hpdeg.le |>.add hp.hasNonnegCoeffs.derivative)
    have heq : C (a - m) * p + (polarTheta m p + p.derivative) =
        C a * p + (1 - X) * p.derivative := by
      simp [polarTheta, theta]
      ring
    rwa [heq] at hsum
  have hshift : Prec p (X * (C a * p + (1 - X) * p.derivative)) :=
    prec_mul_X_of_prec_of_nonneg hcore hcoreNN hp.hasNonnegCoeffs
  have hsplits : (orderNumeratorStep c D p).Splits := by
    have hcombo := allComboRealRooted_of_prec hshift c 1
    simpa [orderNumeratorStep, a] using hcombo
  have hnn : HasNonnegCoeffs (orderNumeratorStep c D p) := by
    apply HasNonnegCoeffs.add
    · intro k
      rw [coeff_C_mul]
      exact mul_nonneg hc.le (hp.hasNonnegCoeffs k)
    · exact hcoreNN.X_mul
  exact IsPFPolynomial.of_realRooted_nonneg hnn hsplits

/-- At the tight degree boundary, the order-numerator step still preserves
Pólya-frequency polynomials, but needs the polar-pencil argument. -/
theorem orderNumeratorStep_isPF_tight
    {m D : ℕ} {p : ℝ[X]} (hm : 2 ≤ m)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = m)
    (hpzero : p.coeff 0 ≠ 0) {c : ℝ} (hc : 0 < c)
    (hbound : (D : ℝ) + 1 - c = m) :
    IsPFPolynomial (orderNumeratorStep c D p) := by
  have hp0 : p ≠ 0 := fun h => hpzero (by simp [h])
  have hreflect : 2 ≤ (reciprocalShift m p).natDegree := by
    have htop : (reciprocalShift m p).coeff m ≠ 0 := by
      simp [hpzero]
    exact hm.trans (le_natDegree_of_ne_zero htop)
  have hpolar : Prec (polarTheta m p) p :=
    prec_polarTheta_self hp hpdeg.le hreflect
  have hderiv : Prec p.derivative p :=
    (derivative_interlaces (hp.ne_zero_and_splits hp0).2 (by lia)).toPrec
  have hpolarPos : HasPosLeadingCoeff (polarTheta m p) :=
    (polarTheta_preserves_pf hp hpdeg.le).hasNonnegCoeffs.pos_leadingCoeff hpolar.1.1
  have hderivPos : HasPosLeadingCoeff p.derivative :=
    (hp.hasNonnegCoeffs.pos_leadingCoeff hp0).derivative (by lia)
  have hcore : Prec (polarTheta m p + p.derivative) p :=
    prec_add_of_prec_right_of_posLeadingCoeff hpolar hderiv hpolarPos hderivPos
  have hcoreEq : polarTheta m p + p.derivative =
      C (m : ℝ) * p + (1 - X) * p.derivative := by
    simp [polarTheta, theta]
    ring
  rw [hcoreEq] at hcore
  have hcoreNN : HasNonnegCoeffs (C (m : ℝ) * p + (1 - X) * p.derivative) := by
    have hsum := (hp.hasNonnegCoeffs.polarTheta hpdeg.le).add hp.hasNonnegCoeffs.derivative
    rwa [hcoreEq] at hsum
  have hshift : Prec p (X * (C (m : ℝ) * p + (1 - X) * p.derivative)) :=
    prec_mul_X_of_prec_of_nonneg hcore hcoreNN hp.hasNonnegCoeffs
  have hsplits : (orderNumeratorStep c D p).Splits := by
    have hcombo := allComboRealRooted_of_prec hshift c 1
    simpa [orderNumeratorStep, hbound] using hcombo
  have hnn : HasNonnegCoeffs (orderNumeratorStep c D p) := by
    rw [orderNumeratorStep, hbound]
    apply HasNonnegCoeffs.add
    · intro k
      rw [coeff_C_mul]
      exact mul_nonneg hc.le (hp.hasNonnegCoeffs k)
    · exact hcoreNN.X_mul
  exact IsPFPolynomial.of_realRooted_nonneg hnn hsplits

/-- At the tight boundary, cancellation retains the input degree. -/
theorem orderNumeratorStep_natDegree_tight
    {m D : ℕ} {p : ℝ[X]} (hm : 1 ≤ m)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = m)
    {c : ℝ} (hc : 0 < c) (hbound : (D : ℝ) + 1 - c = m) :
    (orderNumeratorStep c D p).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
    rw [orderNumeratorStep_coeff_succ]
    have hzero1 : p.coeff (j + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa [hpdeg] using (show m < j + 1 by lia))
    rw [hzero1]
    by_cases hj : j = m
    · subst j
      rw [hbound]
      ring
    · have hmj : m < j := by lia
      have hzero : p.coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by simpa [hpdeg] using hmj)
      rw [hzero]
      ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
    rw [orderNumeratorStep_coeff_succ]
    have htop : 0 < p.coeff (j + 1) := by
      apply lt_of_le_of_ne' (hp.hasNonnegCoeffs (j + 1))
      have hp0 : p ≠ 0 := by
        intro hzero
        simp [hzero] at hpdeg
      have htopne : p.coeff (j + 1) ≠ 0 := by
        have htopne' : p.coeff (Nat.succ j) ≠ 0 := by
          rw [← hpdeg, coeff_natDegree]
          exact leadingCoeff_ne_zero.mpr hp0
        simpa only [Nat.succ_eq_add_one] using htopne'
      exact htopne
    have hbound' : (D : ℝ) + 1 - c - (j : ℝ) = 1 := by
      rw [hbound]
      push_cast
      ring
    rw [hbound']
    have hscalar : 0 < c + (j + 1 : ℕ) := by positivity
    have hjnn : 0 ≤ p.coeff j := hp.hasNonnegCoeffs j
    nlinarith [mul_pos hscalar htop]

end RealRooted
