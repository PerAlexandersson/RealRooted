import RealRooted.LiebSokalPointwise
import RealRooted.Mathlib.Algebra.MvPolynomial.Equiv
import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
import RealRooted.Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Stability of homogeneous multivariate polynomials

This file provides general-degree stability closure for a distinguished
variable whose leading coefficient is a nonzero constant, together with the
homogeneous scaling algebra used for dehomogenization.
-/

namespace MvPolynomial

/-- Evaluating a homogeneous polynomial after scaling every variable extracts
the common scalar to the homogeneous degree. -/
theorem IsHomogeneous.eval_const_mul
    {R σ : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : R) (z : σ → R) :
    eval (fun i => c * z i) P = c ^ d * eval z P := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support hm]
  ac_rfl

/-- For a homogeneous polynomial, dehomogenizing the derivative in the
homogenizing variable equals degree times dehomogenization minus its Euler
derivative. -/
theorem IsHomogeneous.dehomogenize_pderiv_none
    {σ R : Type*} [Fintype σ] [CommRing R]
    {Q : MvPolynomial (Option σ) R} {d : ℕ}
    (hQ : Q.IsHomogeneous d) :
    dehomogenize (pderiv none Q) =
      C (d : R) * dehomogenize Q -
        eulerOperator (dehomogenize Q) := by
  rw [eq_sub_iff_add_eq]
  have h := congrArg dehomogenize hQ.eulerOperator_eq_C_mul
  have hC :
      dehomogenize (C (d : R) : MvPolynomial (Option σ) R) =
        C (d : R) := by
    simp [dehomogenize]
  rw [eulerOperator, Fintype.sum_option, map_add, map_sum] at h
  simp_rw [map_mul, dehomogenize_X_some,
    dehomogenize_pderiv_some] at h
  simp only [dehomogenize_X_none, one_mul, hC] at h
  rw [eulerOperator]
  exact h

end MvPolynomial

namespace RealRooted

open Complex Metric
open Polynomial

noncomputable section

/-- Differentiating a stable polynomial in a distinguished variable preserves
stability when its degree is positive and its leading coefficient in that
variable is a nonzero scalar. The constant leading coefficient prevents a
specialization of the other variables from lowering the fiber degree. -/
theorem MvUpperHalfPlaneStable.pderiv_none_of_top_coeff_C
    {σ : Type*} {P : MvPolynomial (Option σ) ℂ} {m : ℕ} {c : ℂ}
    (hP : MvUpperHalfPlaneStable P) (hm : m ≠ 0) (hc : c ≠ 0)
    (hdeg : P.degreeOf none ≤ m)
    (htop : (MvPolynomial.optionEquivLeft ℂ σ P).coeff m =
      MvPolynomial.C c) :
    MvUpperHalfPlaneStable (MvPolynomial.pderiv none P) := by
  classical
  intro z hz
  let p : Polynomial (MvPolynomial σ ℂ) :=
    MvPolynomial.optionEquivLeft ℂ σ P
  let x : σ → ℂ := fun i => z (some i)
  let q : Polynomial ℂ := Polynomial.map (MvPolynomial.eval x) p
  have hq (y : ℂ) (hy : 0 < y.im) : q.eval y ≠ 0 := by
    change Polynomial.eval y
      (Polynomial.map (MvPolynomial.eval x)
        (MvPolynomial.optionEquivLeft ℂ σ P)) ≠ 0
    rw [← MvPolynomial.optionEquivLeft_elim_eval ℂ σ x y P]
    exact hP (fun o => Option.elim o y x) (by
      intro o
      cases o with
      | none => exact hy
      | some i => exact hz i)
  have hqcoeff : q.coeff m = c := by
    simp only [q, Polynomial.coeff_map, p, htop]
    simp
  have hqnat_le : q.natDegree ≤ m := by
    calc
      q.natDegree ≤ p.natDegree := Polynomial.natDegree_map_le
      _ = P.degreeOf none :=
        MvPolynomial.natDegree_optionEquivLeft (R := ℂ) (σ := σ) P
      _ ≤ m := hdeg
  have hm_le : m ≤ q.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (hqcoeff.trans_ne hc)
  have hqnat : q.natDegree = m := le_antisymm hqnat_le hm_le
  have hqderiv : q.derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [hqnat]
    exact hm
  have hqstable : ∀ y : ℂ, 0 < y.im → q.derivative.eval y ≠ 0 :=
    (Polynomial.derivative_zero_or_upperHalfPlaneStable q hq).resolve_left
      hqderiv
  have heq :
      q.derivative.eval (z none) =
        MvPolynomial.eval z (MvPolynomial.pderiv none P) := by
    dsimp only [q, p]
    rw [Polynomial.derivative_map,
      ← MvPolynomial.optionEquivLeft_pderiv_none]
    rw [← MvPolynomial.optionEquivLeft_elim_eval ℂ σ
      x (z none) (MvPolynomial.pderiv none P)]
    have hx : (fun o => Option.elim o (z none) x) = z := by
      funext o
      cases o <;> rfl
    rw [hx]
  rw [← heq]
  exact hqstable (z none) (hz none)

/-- A finite family of upper-half-plane points admits an upper-half-plane
common multiplier whose products remain in the upper half-plane. -/
theorem exists_common_upperHalfPlane_multiplier
    {σ : Type*} [Finite σ] (z : σ → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    ∃ c : ℂ, 0 < c.im ∧ ∀ i, 0 < (c * z i).im := by
  let U : Set ℂ := {c | ∀ i, 0 < (c * z i).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ i, {c : ℂ | 0 < (c * z i).im} by
      ext c
      simp [U]]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (by fun_prop)
  have hone : (1 : ℂ) ∈ U := by
    intro i
    simpa using hz i
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 1 hone
  let δ : ℝ := ε / 2
  let c : ℂ := 1 + (δ : ℂ) * Complex.I
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hcball : c ∈ Metric.ball (1 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [c]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos hδ]
    dsimp [δ]
    linarith
  refine ⟨c, ?_, hball hcball⟩
  dsimp [c]
  simp [hδ]

/-- Dehomogenizing a homogeneous stable polynomial at the positive real value
one preserves upper-half-plane stability. -/
theorem MvUpperHalfPlaneStable.dehomogenize
    {σ : Type*} [Finite σ] {Q : MvPolynomial (Option σ) ℂ} {d : ℕ}
    (hQ : MvUpperHalfPlaneStable Q) (hhom : Q.IsHomogeneous d) :
    MvUpperHalfPlaneStable (MvPolynomial.dehomogenize Q) := by
  intro z hz hzero
  obtain ⟨c, hc, hcz⟩ := exists_common_upperHalfPlane_multiplier z hz
  let base : Option σ → ℂ := fun o => Option.elim o 1 z
  let scaled : Option σ → ℂ := fun o => c * base o
  have hscaled : scaled = fun o => Option.elim o c (fun i => c * z i) := by
    funext o
    cases o <;> simp [scaled, base]
  have hne : MvPolynomial.eval scaled Q ≠ 0 := by
    rw [hscaled]
    apply hQ
    intro o
    cases o with
    | none => exact hc
    | some i => exact hcz i
  have hscale := hhom.eval_const_mul c base
  have hbase : MvPolynomial.eval base Q = 0 := by
    simpa [base] using hzero
  exact hne (by rw [hscale, hbase, mul_zero])

end


end RealRooted
