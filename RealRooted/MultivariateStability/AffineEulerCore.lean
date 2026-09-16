import RealRooted.Hyperbolicity
import RealRooted.Multiaffine.AffineEulerCore
import RealRooted.MultivariateStability.AllCombo
import RealRooted.MultivariateStability.DirectionalDerivative

/-!
# Stability of affine Euler cores

This module realizes the affine Euler operator as a dehomogenized
directional derivative.  Homogenization and the directional-derivative
pencil then place a stable polynomial and its affine Euler core in one
weakly stable real span.
-/

namespace RealRooted

open scoped BigOperators

noncomputable section

/-- Dehomogenizing the all-ones derivative of a degree-`d` ordinary
homogenization gives the degree-`d` affine Euler core. -/
theorem dehomogenize_directionalPDeriv_ordinaryHomogenization
    {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (d : Nat) (hdeg : P.totalDegree ≤ d) :
    MvPolynomial.dehomogenize
        (directionalPDeriv (fun _ : Option σ => (1 : R))
          (MvPolynomial.ordinaryHomogenization P d)) =
      MvPolynomial.affineEulerCore id (d : R) P := by
  let H := MvPolynomial.ordinaryHomogenization P d
  have hhom : H.IsHomogeneous d :=
    MvPolynomial.ordinaryHomogenization_isHomogeneous P d
  rw [directionalPDeriv, Fintype.sum_option, map_add, map_sum]
  simp_rw [map_mul, map_one, one_mul]
  rw [hhom.dehomogenize_pderiv_none]
  simp_rw [MvPolynomial.dehomogenize_pderiv_some]
  rw [MvPolynomial.dehomogenize_ordinaryHomogenization_of_totalDegree_le
    P hdeg]
  unfold MvPolynomial.affineEulerCore MvPolynomial.eulerOperator
  simp only [id_eq]

/-- Dehomogenization preserves weak real stability without a homogeneity
hypothesis, since it is boundary specialization at the real value one. -/
theorem MvRealStableOrZero.dehomogenize_general
    {σ : Type*} {P : MvPolynomial (Option σ) Real}
    (hP : MvRealStableOrZero P) :
    MvRealStableOrZero (MvPolynomial.dehomogenize P) := by
  have hspecialize := hP.specializeAt_general none 1
  rw [MvPolynomial.specializeAt_none_one_eq_rename_some_dehomogenize]
    at hspecialize
  exact MvRealStableOrZero.of_rename hspecialize
    (Option.some_injective σ)

/-- A stable polynomial with nonnegative coefficients and its admissible
affine Euler core lie in one weakly stable real span. -/
theorem MvRealStable.allCombo_affineEulerCore
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ Real} {d : Nat}
    (hP : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hdeg : P.totalDegree ≤ d) :
    AllComboMvRealStableOrZero P
      (MvPolynomial.affineEulerCore id (d : Real) P) := by
  let H := MvPolynomial.ordinaryHomogenization P d
  let D := directionalPDeriv (fun _ : Option σ => (1 : Real)) H
  have hH : MvRealStable H :=
    hP.ordinaryHomogenization_of_totalDegree_le hnn hP.ne_zero hdeg
  have hDcore : MvPolynomial.dehomogenize D =
      MvPolynomial.affineEulerCore id (d : Real) P := by
    exact dehomogenize_directionalPDeriv_ordinaryHomogenization P d hdeg
  apply allComboMvRealStableOrZero_of_affine
  · rw [← hDcore]
    exact (hH.directionalPDeriv_zero_or
      (fun _ : Option σ => (1 : Real)) fun _ => zero_le_one).dehomogenize_general
  · intro t
    have hpencil := hH.directionalPDeriv_pencil
      (fun _ : Option σ => (1 : Real)) fun _ => zero_le_one
    have haffine := hpencil.affineExtension_specialize_zero_or t
    have hdehom := haffine.dehomogenize_general
    have hC : MvPolynomial.dehomogenize
        (MvPolynomial.C t : MvPolynomial (Option σ) Real) =
        MvPolynomial.C t := by
      simp [MvPolynomial.dehomogenize]
    rw [map_add, map_mul, hC,
      MvPolynomial.dehomogenize_ordinaryHomogenization_of_totalDegree_le
        P hdeg, hDcore] at hdehom
    exact hdehom

end

end RealRooted
