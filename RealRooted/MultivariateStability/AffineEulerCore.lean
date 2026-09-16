import RealRooted.Hyperbolicity
import RealRooted.Multiaffine.AffineEulerCore
import RealRooted.MultivariateStability.AllCombo
import RealRooted.MultivariateStability.DirectionalDerivative
import RealRooted.MultivariateStability.HomogeneousPencilWronskian
import RealRooted.MultivariateStability.Rayleigh

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

/-- Dehomogenizing the all-ones derivative of a homogeneous polynomial gives
the affine Euler core of its dehomogenization. -/
theorem MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one
    {σ R : Type*} [Fintype σ] [CommRing R]
    {H : MvPolynomial (Option σ) R} {d : Nat}
    (hH : H.IsHomogeneous d) :
    MvPolynomial.dehomogenize
        (directionalPDeriv (fun _ : Option σ => (1 : R)) H) =
      MvPolynomial.affineEulerCore id (d : R)
        (MvPolynomial.dehomogenize H) := by
  rw [directionalPDeriv, Fintype.sum_option, map_add, map_sum]
  simp_rw [map_mul, map_one, one_mul]
  rw [hH.dehomogenize_pderiv_none]
  simp_rw [MvPolynomial.dehomogenize_pderiv_some]
  unfold MvPolynomial.affineEulerCore MvPolynomial.eulerOperator
  simp only [id_eq]

/-- Dehomogenizing the all-ones derivative of a degree-`d` ordinary
homogenization gives the degree-`d` affine Euler core. -/
theorem dehomogenize_directionalPDeriv_ordinaryHomogenization
    {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (d : Nat) (hdeg : P.totalDegree ≤ d) :
    MvPolynomial.dehomogenize
        (directionalPDeriv (fun _ : Option σ => (1 : R))
          (MvPolynomial.ordinaryHomogenization P d)) =
      MvPolynomial.affineEulerCore id (d : R) P := by
  rw [MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one
    (MvPolynomial.ordinaryHomogenization_isHomogeneous P d),
    MvPolynomial.dehomogenize_ordinaryHomogenization_of_totalDegree_le
      P hdeg]

/-- The affine Euler core inherited from a homogeneous Rayleigh polynomial
has the directional-derivative Wronskian orientation against its
dehomogenization. -/
theorem MvPolynomial.IsRayleigh.eval_coordinateWronskian_affineEulerCore_nonneg
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hH : H.IsRayleigh) (hhom : H.IsHomogeneous d) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.dehomogenize H))
        (MvPolynomial.dehomogenize H) i) := by
  intro i x
  rw [← MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hhom,
    ← MvPolynomial.dehomogenize_coordinateWronskian_some,
    MvPolynomial.eval_dehomogenize]
  exact hH.eval_coordinateWronskian_directionalPDeriv_nonneg
    (fun _ : Option σ => (1 : Real)) (fun _ => zero_le_one)
    (some i) (fun o => Option.elim o 1 x)

/-- For a stable multiaffine homogeneous polynomial, the affine Euler core
has the directional-derivative Wronskian orientation against its
dehomogenization. -/
theorem MvRealStable.eval_coordinateWronskian_affineEulerCore_nonneg
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hstable : MvRealStable H) (hma : MvPolynomial.IsMultiaffine H)
    (hhom : H.IsHomogeneous d) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.dehomogenize H))
        (MvPolynomial.dehomogenize H) i) :=
  MvPolynomial.IsRayleigh.eval_coordinateWronskian_affineEulerCore_nonneg
    (hstable.isRayleigh_of_isMultiaffine hma) hhom

/-- A positive-degree homogeneous stable polynomial with nonnegative
coefficients has its all-ones directional derivative Wronskian-oriented
against it, without any multiaffineness hypothesis. -/
theorem MvRealStable.eval_coordinateWronskian_directionalPDeriv_one_nonneg
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (directionalPDeriv (fun _ : σ => (1 : Real)) H) H i) := by
  let D := directionalPDeriv (fun _ : σ => (1 : Real)) H
  have hDhom : D.IsHomogeneous (d - 1) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa [D, directionalPDeriv] using hhom.pderiv (i := i)
  have hDnn : MvPolynomial.HasNonnegCoeffs D := by
    apply MvPolynomial.HasNonnegCoeffs.sum
    intro i hi
    simpa [D, directionalPDeriv] using hnn.pderiv i
  have hD0 : D ≠ 0 := by
    intro hzero
    have hD_eval : MvPolynomial.eval (fun _ : σ => (1 : Real)) D = 0 := by
      rw [hzero]
      simp
    have heuler := congrArg
      (MvPolynomial.eval (fun _ : σ => (1 : Real)))
      hhom.sum_X_mul_pderiv
    have hH_eval : 0 < MvPolynomial.eval (fun _ : σ => (1 : Real)) H :=
      hnn.eval_pos hstable.ne_zero fun _ => zero_lt_one
    simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      one_mul, map_nsmul] at heuler
    have hD_eval' : MvPolynomial.eval (fun _ : σ => (1 : Real)) D =
        ∑ i : σ, MvPolynomial.eval (fun _ : σ => (1 : Real))
          (MvPolynomial.pderiv i H) := by
      simp [D, directionalPDeriv]
    rw [← hD_eval', hD_eval] at heuler
    have hdpos : 0 < (d : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    simp only [nsmul_eq_mul] at heuler
    nlinarith
  have hpencil := hstable.directionalPDeriv_pencil
    (fun _ : σ => (1 : Real)) fun _ => zero_le_one
  exact hpencil.eval_coordinateWronskian_nonneg_of_homogeneous_affineExtension
    hhom hDhom hnn hDnn hstable.ne_zero hD0

/-- A positive-degree homogeneous stable polynomial with nonnegative
coefficients gives an oriented affine Euler core after dehomogenization. -/
theorem MvRealStable.eval_coordinateWronskian_affineEulerCore_nonneg_of_nonnegative
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.dehomogenize H))
        (MvPolynomial.dehomogenize H) i) := by
  intro i x
  rw [← MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hhom,
    ← MvPolynomial.dehomogenize_coordinateWronskian_some,
    MvPolynomial.eval_dehomogenize]
  exact hstable.eval_coordinateWronskian_directionalPDeriv_one_nonneg
    hnn hhom hd (some i) (fun o => Option.elim o 1 x)

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
