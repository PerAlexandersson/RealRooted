import RealRooted.Basic
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import RealRooted.MultivariateStability
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Complex.Basic

/-!
# Foundational Hermite--Biehler definitions

This module contains real-polynomial complexification, univariate half-plane
stability, the Hermite--Biehler polynomial, and the splitness/stability bridge.
It is independent of the forward and converse proper-position arguments.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Complexification of a real polynomial. -/
def complexify (p : ℝ[X]) : ℂ[X] :=
  p.map Complex.ofRealHom

@[simp] theorem complexify_zero :
    complexify 0 = 0 := by
  simp only [complexify, Polynomial.map_zero]

@[simp] theorem complexify_one :
    complexify 1 = 1 := by
  simp [complexify]

@[simp] theorem complexify_C (a : ℝ) :
    complexify (C a) = C (a : ℂ) := by
  simp [complexify]

@[simp] theorem complexify_X :
    complexify X = X := by
  simp [complexify]

/-- A univariate complex polynomial is upper-half-plane stable if it has no root
with strictly positive imaginary part. -/
def IsUpperHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0

/-- Evaluation commutes with Mathlib's canonical identification of a
univariate polynomial with a multivariate polynomial in one variable. -/
@[simp] theorem eval_uniqueAlgEquiv_symm_finOne (p : ℂ[X]) (z : Fin 1 → ℂ) :
    MvPolynomial.eval z ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) =
      p.eval (z 0) := by
  change
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p).eval₂
        (RingHom.id ℂ) z = p.eval (z 0)
  rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm]
  rfl

/-- Univariate upper-half-plane stability agrees with multivariate stability
after Mathlib's canonical `Fin 1` identification. Both predicates exclude the
zero polynomial. -/
theorem isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable (p : ℂ[X]) :
    IsUpperHalfPlaneStable p ↔
      MvUpperHalfPlaneStable
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) := by
  change (∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) ↔
    ∀ z : Fin 1 → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) ≠ 0
  constructor
  · intro hp z hz
    rw [eval_uniqueAlgEquiv_symm_finOne]
    exact hp (z 0) (hz 0)
  · intro hp z hz
    simpa only [eval_uniqueAlgEquiv_symm_finOne] using
      hp (fun _ ↦ z) (fun _ ↦ hz)

namespace IsUpperHalfPlaneStable

/-- Multiplication transported from the general multivariate stability API. -/
theorem mul {p q : ℂ[X]} (hp : IsUpperHalfPlaneStable p)
    (hq : IsUpperHalfPlaneStable q) :
    IsUpperHalfPlaneStable (p * q) := by
  rw [isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable]
  simpa using
    ((isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable p).mp hp).mul
      ((isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable q).mp hq)

end IsUpperHalfPlaneStable

/-- A univariate complex polynomial is right-half-plane stable if it has no
root with strictly positive real part. -/
def IsRightHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.re → p.eval z ≠ 0

/-- Hurwitz stability for a real polynomial in the coefficient-positive
combinatorial convention used here. -/
def IsHurwitzStable (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ IsRightHalfPlaneStable (complexify p)

namespace IsHurwitzStable

theorem hasNonnegCoeffs {p : ℝ[X]} (hp : IsHurwitzStable p) :
    HasNonnegCoeffs p :=
  hp.1

theorem rightHalfPlaneStable {p : ℝ[X]} (hp : IsHurwitzStable p) :
    IsRightHalfPlaneStable (complexify p) :=
  hp.2

end IsHurwitzStable

/-- The classical Hermite--Biehler combination `f + i g`. -/
def hermiteBiehlerPolynomial (f g : ℝ[X]) : ℂ[X] :=
  complexify f + C Complex.I * complexify g

@[simp] theorem eval_hermiteBiehlerPolynomial (f g : ℝ[X]) (z : ℂ) :
    (hermiteBiehlerPolynomial f g).eval z =
      (complexify f).eval z + Complex.I * (complexify g).eval z := by
  simp [hermiteBiehlerPolynomial]

/-- A split real polynomial evaluates as its leading coefficient times its
complexified root factors. -/
theorem eval_complexify_eq_prod {p : ℝ[X]} (hp : p.Splits) {z : ℂ} :
    (complexify p).eval z =
      (p.leadingCoeff : ℂ) *
        (p.roots.map (fun r : ℝ ↦ z - (r : ℂ))).prod := by
  unfold complexify
  conv_lhs => rw [hp.eq_prod_roots]
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C,
    Polynomial.map_multiset_prod, Multiset.map_map, eval_multiset_prod,
    Function.comp, Polynomial.map_sub, Polynomial.map_X, eval_sub, eval_X,
    map_C, Complex.ofRealHom_eq_coe]

/-- A nonzero split real polynomial has no root in the open upper half-plane. -/
theorem eval_complexify_ne_zero_of_splits_of_im_pos
    {p : ℝ[X]} (hp : p.Splits) (hp₀ : p ≠ 0)
    {z : ℂ} (hz : 0 < z.im) : (complexify p).eval z ≠ 0 := by
  rw [eval_complexify_eq_prod hp]
  refine mul_ne_zero (by simp [hp₀]) ?_
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  rintro r - heq
  exact hz.ne' (by simpa using congrArg Complex.im heq)

theorem eval_complexify_conj (f : ℝ[X]) (z : ℂ) :
    (complexify f).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((complexify f).eval z) := by
  have : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext x
    simp
  simp [complexify, eval_map, hom_eval₂, this]

theorem complexify_conj_root {f : ℝ[X]} {z : ℂ}
    (hz : (complexify f).eval z = 0) :
    (complexify f).eval (starRingEnd ℂ z) = 0 := by
  rw [eval_complexify_conj, hz, map_zero]

/-- A nonzero split real polynomial has stable complexification. -/
theorem Polynomial.Splits.isUpperHalfPlaneStable_complexify
    {p : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0) :
    IsUpperHalfPlaneStable (complexify p) :=
  fun _ hz ↦ eval_complexify_ne_zero_of_splits_of_im_pos hp hp0 hz

/-- Upper-half-plane stability of a real polynomial's complexification forces
all its roots to be real. -/
theorem IsUpperHalfPlaneStable.splits_complexify {p : ℝ[X]}
    (hp : IsUpperHalfPlaneStable (complexify p)) :
    p.Splits := by
  apply Polynomial.splits_of_all_roots_real
  intro z hz
  by_contra him
  rcases lt_or_gt_of_ne him with hneg | hpos
  · exact hp (starRingEnd ℂ z) (by simpa using neg_pos.mpr hneg)
      (complexify_conj_root hz)
  · exact hp z hpos hz

end RealRooted
