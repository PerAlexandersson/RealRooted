module

public import RealRooted.PFPolynomial
public import RealRooted.Hermite.Poulain
import RealRooted.ExponentialRows.SubstitutionFactor
import RealRooted.ExponentialRows.SubstitutionPolynomialChain
import RealRooted.Hermite.PoulainSymbolDerivative
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.PosCombo
import RealRooted.WagnerRightSum.Sign
import Mathlib.Tactic

/-!
# PF polynomial outer symbols preserve the PF cone

A degree induction combines the differential-prefix interval with the
single-factor insertion step. Bounded-degree closure includes roots at zero.
Source: unpublished manuscript, RealRooted #2415, round four.
-/

public section

open Polynomial
open RealRooted.HermitePoulain

namespace RealRooted.ExponentialRows

/-- The differential-symbol interval closes one positive linear-factor step
once the operator preserves the preceding degree. -/
private theorem strictInterl_factor_of_polynomial_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {P : ℝ[X]} (hP : IsPFPolynomial P) (hPne : P ≠ 0)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hidentity : ∀ p, T (applyAsDifferentialOperator P p) =
      (T p).derivative + C (P.coeff 0) * T p)
    (hstep : ∀ p, T (X * p) = X * T (applyAsDifferentialOperator P.derivative p))
    {D : ℕ}
    (hmap : ∀ {p}, IsPFPolynomial p → p.natDegree ≤ D → IsPFPolynomial (T p))
    (hinterl : ∀ {f g}, IsPFPolynomial f → IsPFPolynomial g →
      f.natDegree ≤ D → g.natDegree ≤ D → Interl f g → Interl (T f) (T g))
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) (hpdeg : p.natDegree ≤ D)
    {r : ℝ} (hr : 0 < r) : StrictInterl (T p) (T ((X + C r) * p)) := by
  have hne : T p ≠ 0 := by
    intro hz
    have h := hp0
    rw [← hTc, hz, coeff_zero] at h
    exact (lt_irrefl 0) h
  have hnewne : T ((X + C r) * p) ≠ 0 := by
    intro hz
    have h : 0 < (T ((X + C r) * p)).coeff 0 := by
      rw [hTc, mul_coeff_zero, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      exact mul_pos hr hp0
    rw [hz, coeff_zero] at h
    exact (lt_irrefl 0) h
  have hnn := hTnn p hp.hasNonnegCoeffs
  have hdiffnn := hTnn _ (hasNonnegCoeffs_applyAsDifferentialOperator
    hP.hasNonnegCoeffs.derivative hp.hasNonnegCoeffs)
  have h := interl_map_applyDifferential_derivative T hP hPne hTnn hTc hidentity
    hmap hinterl hp hp0 hpdeg
  have hX := interl_mul_X_of_interl h hdiffnn hnn
  have hself : Interl (T p) (T p) := Interl.refl (fun _ => (hmap hp hpdeg).splits)
  have hout := interl_add_right_of_common_left_of_nonneg hX
    (hself.C_mul_right_of_nonneg hr.le) hdiffnn.X_mul (hasNonnegCoeffs_C_mul hr.le hnn)
  rw [← hstep, ← Polynomial.linearMap_C_mul, ← map_add, ← add_mul] at hout
  exact hout.toStrictInterl_of_ne hne hnewne

/-- The two polynomial kernel rules imply PF preservation in every degree,
together with the positive-constant single-factor interlacing invariant. -/
theorem isPFPolynomial_map_and_strictInterl_of_polynomial_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {P : ℝ[X]} (hP : IsPFPolynomial P) (hPne : P ≠ 0)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1) (hTdeg : ∀ p, (T p).natDegree ≤ p.natDegree)
    (hidentity : ∀ p, T (applyAsDifferentialOperator P p) =
      (T p).derivative + C (P.coeff 0) * T p)
    (hstep : ∀ p, T (X * p) = X * T (applyAsDifferentialOperator P.derivative p)) :
    (∀ {p}, IsPFPolynomial p → IsPFPolynomial (T p)) ∧
      ∀ {p}, IsPFPolynomial p → 0 < p.coeff 0 →
        ∀ r : ℝ, 0 < r → StrictInterl (T p) (T ((X + C r) * p)) := by
  have hbounded (D : ℕ) :
      (∀ {p}, IsPFPolynomial p → p.natDegree ≤ D → IsPFPolynomial (T p)) ∧
        (∀ {p}, IsPFPolynomial p → 0 < p.coeff 0 → p.natDegree < D →
          ∀ r : ℝ, 0 < r → StrictInterl (T p) (T ((X + C r) * p))) := by
    induction D with
    | zero =>
      constructor
      · intro p hp hpdeg
        have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (by lia)
        rw [hpc, ← mul_one (C (p.coeff 0)), Polynomial.linearMap_C_mul, hT1, mul_one]
        exact IsPFPolynomial.of_C_nonneg (hp.hasNonnegCoeffs 0)
      · intro p _ _ hpdeg
        lia
    | succ D ih =>
      have hlow : ∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
          f.natDegree ≤ D → g.natDegree ≤ D → Interl f g → Interl (T f) (T g) :=
        fun hf hg hfd hgd hfg =>
          interl_map_of_pos_constant_factor T hTnn hTc hTdeg ih.1 ih.2 hf hg hfd hgd hfg
      have hfactor {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0)
          (hpdeg : p.natDegree < D + 1) (r : ℝ) (hr : 0 < r) :
          StrictInterl (T p) (T ((X + C r) * p)) :=
        strictInterl_factor_of_polynomial_rule T hP hPne hTnn hTc hidentity hstep
          ih.1 hlow hp hp0 (by lia) hr
      refine ⟨?_, fun hp hp0 hpdeg r hr => hfactor hp hp0 hpdeg r hr⟩
      intro p hp hpdeg
      apply isPFPolynomial_map_of_isNegativeSimple_of_natDegree_le T _ hp hpdeg
      intro q hq hqdeg
      by_cases hsmall : q.natDegree ≤ D
      · exact ih.1 hq.isPFPolynomial hsmall
      have hqpf := hq.isPFPolynomial
      have hq0 : 0 < q.coeff 0 := by
        rw [coeff_zero_eq_eval_zero]
        exact eval_pos_of_all_roots_lt hq.1 hq.2.1 hq.2.2.2.1 hq.2.2.2.2
      obtain ⟨u, v, hu, hfac, hv, hvdeg⟩ :=
        hqpf.exists_X_sub_C_factor_of_pos_natDegree (by lia)
      have hconstant : 0 < -u * v.coeff 0 := by
        simpa only [hfac, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
          using hq0
      have hu' : 0 < -u := by
        have := hv.hasNonnegCoeffs 0
        nlinarith
      have hv0 : 0 < v.coeff 0 := by
        have := hv.hasNonnegCoeffs 0
        nlinarith
      have H := hfactor hv hv0 (by lia) (-u) hu'
      have hs : (T q).Splits := by
        have hvfac : q = (X + C (-u)) * v := by
          simpa only [sub_eq_add_neg, map_neg] using hfac
        rw [hvfac]
        exact H.2.1.2
      exact IsPFPolynomial.of_realRooted_nonneg (hTnn q hqpf.hasNonnegCoeffs) hs
  constructor
  · intro p hp
    exact (hbounded p.natDegree).1 hp le_rfl
  · intro p hp hp0 r hr
    exact (hbounded (p.natDegree + 1)).2 hp hp0 (Nat.lt_succ_self _) r hr

end RealRooted.ExponentialRows
