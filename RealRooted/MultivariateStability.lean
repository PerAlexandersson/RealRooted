import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Multivariate stability

This file provides the common upper-half-plane stability vocabulary used by
the Borcea--Branden finite-symbol and rectangular-convolution developments.
It also defines the bivariate lift `p(x * y)` appearing in Gribinski--Marcus,
Lemma 2.5.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Complexification of a real multivariate polynomial. -/
def complexifyMv {sigma : Type*} (P : MvPolynomial sigma ℝ) :
    MvPolynomial sigma ℂ :=
  P.map Complex.ofRealHom

/-- Stability in a product of open upper half-planes. -/
def MvUpperHalfPlaneStable {sigma : Type*} (P : MvPolynomial sigma ℂ) : Prop :=
  ∀ z : sigma → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.eval z P ≠ 0

/-- Weak upper-half-plane stability: the polynomial is either zero or stable.
This is the natural conclusion convention for linear stability preservers. -/
def MvUpperHalfPlaneStableOrZero {sigma : Type*}
    (P : MvPolynomial sigma ℂ) : Prop :=
  P = 0 ∨ MvUpperHalfPlaneStable P

/-- The zero polynomial is weakly stable. -/
theorem MvUpperHalfPlaneStableOrZero.zero {sigma : Type*} :
    MvUpperHalfPlaneStableOrZero (0 : MvPolynomial sigma ℂ) :=
  Or.inl rfl

/-- A stable polynomial is weakly stable. -/
theorem MvUpperHalfPlaneStable.orZero {sigma : Type*}
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStableOrZero P :=
  Or.inr hP

/-- Real stability, expressed by complexifying the coefficients before
evaluation in a product of open upper half-planes. -/
def MvRealStable {sigma : Type*} (P : MvPolynomial sigma ℝ) : Prop :=
  MvUpperHalfPlaneStable (complexifyMv P)

/-- A nonzero multivariate polynomial has a nonzero evaluation in a product
of open upper half-planes. -/
theorem exists_upperHalfPlane_eval_ne_zero {sigma : Type*}
    {P : MvPolynomial sigma ℂ} (hP : P ≠ 0) :
    ∃ z : sigma → ℂ, (∀ i, 0 < (z i).im) ∧ MvPolynomial.eval z P ≠ 0 := by
  by_contra h
  push Not at h
  apply hP
  let s : sigma → Set ℂ := fun _ => {z | 0 < z.im}
  apply MvPolynomial.funext_set s
  · intro i
    exact Set.infinite_of_injective_forall_mem UpperHalfPlane.coe_injective
      fun z => z.coe_im_pos
  · intro z hz
    simpa using h z fun i => hz i (Set.mem_univ i)

/-- Restrict a multivariate complex polynomial to the affine line
`z + t * v`. -/
def affineLineRestriction {sigma : Type*} (z v : sigma → ℂ)
    (P : MvPolynomial sigma ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) P

@[simp] theorem eval_affineLineRestriction {sigma : Type*}
    (z v : sigma → ℂ) (P : MvPolynomial sigma ℂ) (t : ℂ) :
    (affineLineRestriction z v P).eval t =
      MvPolynomial.eval (fun i => z i + v i * t) P := by
  unfold affineLineRestriction
  change Polynomial.evalRingHom t
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext c
    simp
  rw [hC]
  rfl

theorem MvUpperHalfPlaneStable.C_mul {sigma : Type*}
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStable P)
    {c : ℂ} (hc : c ≠ 0) :
    MvUpperHalfPlaneStable (MvPolynomial.C c * P) := by
  intro z hz
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  exact mul_ne_zero hc (hP z hz)

theorem MvUpperHalfPlaneStable.mul {sigma : Type*}
    {P Q : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStable P)
    (hQ : MvUpperHalfPlaneStable Q) :
    MvUpperHalfPlaneStable (P * Q) := by
  intro z hz
  rw [MvPolynomial.eval_mul]
  exact mul_ne_zero (hP z hz) (hQ z hz)

/-- Arbitrary scalar multiplication preserves weak stability. -/
theorem MvUpperHalfPlaneStableOrZero.C_mul {sigma : Type*}
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStableOrZero P)
    (c : ℂ) :
    MvUpperHalfPlaneStableOrZero (MvPolynomial.C c * P) := by
  rcases hP with rfl | hP
  · left
    simp
  · by_cases hc : c = 0
    · left
      simp [hc]
    · exact (hP.C_mul hc).orZero

/-- Multiplication preserves weak stability. -/
theorem MvUpperHalfPlaneStableOrZero.mul {sigma : Type*}
    {P Q : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStableOrZero P)
    (hQ : MvUpperHalfPlaneStableOrZero Q) :
    MvUpperHalfPlaneStableOrZero (P * Q) := by
  rcases hP with rfl | hP
  · left
    simp
  rcases hQ with rfl | hQ
  · left
    simp
  exact (hP.mul hQ).orZero

/-- The sum of two variables is stable in the open upper half-plane. -/
theorem MvUpperHalfPlaneStable.X_add_X {sigma : Type*} (i j : sigma) :
    MvUpperHalfPlaneStable
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial sigma ℂ) := by
  intro z hz
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_X]
  intro hzero
  have him : 0 < (z i + z j).im := by
    simpa using add_pos (hz i) (hz j)
  rw [hzero] at him
  simp at him

/-- A homogeneous linear factor with a nonpositive real root is stable. -/
theorem MvUpperHalfPlaneStable.X_sub_nonpos_C_mul_X {sigma : Type*}
    (i j : sigma) {r : ℝ} (hr : r ≤ 0) :
    MvUpperHalfPlaneStable
      (MvPolynomial.X i - MvPolynomial.C (r : ℂ) * MvPolynomial.X j) := by
  intro z hz
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_mul, MvPolynomial.eval_C]
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  nlinarith [hz i, hz j]

/-- A product of homogeneous linear factors with nonpositive real roots is stable. -/
theorem MvUpperHalfPlaneStable.nonposRootFactorProduct {sigma : Type*}
    (i j : sigma) (roots : Multiset ℝ)
    (hroots : ∀ r ∈ roots, r ≤ 0) :
    MvUpperHalfPlaneStable
      (roots.map (fun r : ℝ =>
        MvPolynomial.X i - MvPolynomial.C (r : ℂ) * MvPolynomial.X j)).prod := by
  induction roots using Multiset.induction_on with
  | empty =>
      intro z hz
      simp
  | cons r roots ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      apply (MvUpperHalfPlaneStable.X_sub_nonpos_C_mul_X i j
        (hroots r (by simp))).mul
      apply ih
      intro s hs
      exact hroots s (by simp [hs])

/-- Multiplication by a power of the sum of two variables preserves stability. -/
theorem MvUpperHalfPlaneStable.mul_X_add_X_pow {sigma : Type*}
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStable P)
    (i j : sigma) (m : ℕ) :
    MvUpperHalfPlaneStable
      ((MvPolynomial.X i + MvPolynomial.X j) ^ m * P) := by
  induction m with
  | zero => simpa
  | succ m ih =>
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        (MvUpperHalfPlaneStable.X_add_X i j).mul ih

theorem MvUpperHalfPlaneStable.left_of_mul {sigma : Type*}
    {P Q : MvPolynomial sigma ℂ}
    (hPQ : MvUpperHalfPlaneStable (P * Q)) :
    MvUpperHalfPlaneStable P := by
  intro z hz hzero
  exact hPQ z hz (by simp [hzero])

theorem MvUpperHalfPlaneStable.right_of_mul {sigma : Type*}
    {P Q : MvPolynomial sigma ℂ}
    (hPQ : MvUpperHalfPlaneStable (P * Q)) :
    MvUpperHalfPlaneStable Q := by
  intro z hz hzero
  exact hPQ z hz (by simp [hzero])

theorem MvUpperHalfPlaneStable.rename {sigma tau : Type*}
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStable P)
    {f : sigma → tau} :
    MvUpperHalfPlaneStable (MvPolynomial.rename f P) := by
  intro z hz
  rw [MvPolynomial.eval_rename]
  exact hP (z ∘ f) fun i => hz (f i)

/-- Renaming variables preserves weak stability. -/
theorem MvUpperHalfPlaneStableOrZero.rename {sigma tau : Type*}
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStableOrZero P)
    (f : sigma → tau) :
    MvUpperHalfPlaneStableOrZero (MvPolynomial.rename f P) := by
  rcases hP with rfl | hP
  · left
    simp
  exact hP.rename.orZero

/-- Specialize the right block of variables in a polynomial on a sum type. -/
def specializeRight {sigma tau : Type*} (y : tau → ℂ)
    (P : MvPolynomial (Sum sigma tau) ℂ) : MvPolynomial sigma ℂ :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X (MvPolynomial.C ∘ y)) P

theorem eval_specializeRight {sigma tau : Type*} (x : sigma → ℂ)
    (y : tau → ℂ) (P : MvPolynomial (Sum sigma tau) ℂ) :
    MvPolynomial.eval x (specializeRight y P) =
      MvPolynomial.eval (Sum.elim x y) P := by
  unfold specializeRight
  change (MvPolynomial.aeval x)
      ((MvPolynomial.aeval
        (Sum.elim MvPolynomial.X (MvPolynomial.C ∘ y))) P) =
    (MvPolynomial.aeval (Sum.elim x y)) P
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  ext i
  cases i <;> simp

theorem MvUpperHalfPlaneStable.specializeRight
    {sigma tau : Type*} {P : MvPolynomial (Sum sigma tau) ℂ}
    (hP : MvUpperHalfPlaneStable P) {y : tau → ℂ}
    (hy : ∀ i, 0 < (y i).im) :
    MvUpperHalfPlaneStable (specializeRight y P) := by
  intro x hx
  rw [eval_specializeRight]
  exact hP (Sum.elim x y) fun i => by
    cases i with
    | inl i => exact hx i
    | inr i => exact hy i

/-- Specialize the left block of variables in a polynomial on a sum type. -/
def specializeLeft {sigma tau : Type*} (x : sigma → ℂ)
    (P : MvPolynomial (Sum sigma tau) ℂ) : MvPolynomial tau ℂ :=
  MvPolynomial.aeval (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X) P

theorem eval_specializeLeft {sigma tau : Type*} (x : sigma → ℂ)
    (y : tau → ℂ) (P : MvPolynomial (Sum sigma tau) ℂ) :
    MvPolynomial.eval y (specializeLeft x P) =
      MvPolynomial.eval (Sum.elim x y) P := by
  unfold specializeLeft
  change (MvPolynomial.aeval y)
      ((MvPolynomial.aeval
        (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)) P) =
    (MvPolynomial.aeval (Sum.elim x y)) P
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  ext i
  cases i <;> simp

theorem MvUpperHalfPlaneStable.specializeLeft
    {sigma tau : Type*} {P : MvPolynomial (Sum sigma tau) ℂ}
    (hP : MvUpperHalfPlaneStable P) {x : sigma → ℂ}
    (hx : ∀ i, 0 < (x i).im) :
    MvUpperHalfPlaneStable (specializeLeft x P) := by
  intro y hy
  rw [eval_specializeLeft]
  exact hP (Sum.elim x y) fun i => by
    cases i with
    | inl i => exact hx i
    | inr i => exact hy i

/-- The bivariate polynomial `p(x * y)`. -/
def xyLift {R : Type*} [CommSemiring R] (p : R[X]) :
    MvPolynomial (Fin 2) R :=
  p.eval₂ (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
    (MvPolynomial.X 0 * MvPolynomial.X 1)

@[simp] theorem eval_xyLift {R : Type*} [CommSemiring R]
    (p : R[X]) (z : Fin 2 → R) :
    MvPolynomial.eval z (xyLift p) = p.eval (z 0 * z 1) := by
  unfold xyLift
  rw [Polynomial.hom_eval₂]
  have hC :
      (MvPolynomial.eval z).comp
          (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R) =
        RingHom.id R := by
    ext r
    simp
  rw [hC, Polynomial.eval₂_id]
  simp

theorem xyLift_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    xyLift p ≠ 0 := by
  intro hxy
  apply hp
  apply Polynomial.funext
  intro x
  have heval := congrArg (MvPolynomial.eval ![x, 1]) hxy
  simpa using heval

@[simp] theorem complexifyMv_xyLift (p : ℝ[X]) :
    complexifyMv (xyLift p) = xyLift (p.map Complex.ofRealHom) := by
  unfold complexifyMv xyLift
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  have hC :
      (MvPolynomial.map Complex.ofRealHom :
          MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℂ).comp
          (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ) =
        (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ).comp
          Complex.ofRealHom := by
    ext r
    simp
  rw [hC]
  simp

@[simp] theorem eval_complexifyMv_xyLift (p : ℝ[X]) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (complexifyMv (xyLift p)) =
      (p.map Complex.ofRealHom).eval (z 0 * z 1) := by
  rw [complexifyMv_xyLift, eval_xyLift]

/-- The product of two points in the open upper half-plane cannot be a
nonnegative real number. -/
theorem mul_ne_ofReal_of_im_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    {r : ℝ} (hr : 0 ≤ r) :
    z * w ≠ r := by
  intro hmul
  have him : z.re * w.im + z.im * w.re = 0 := by
    have := congrArg Complex.im hmul
    simpa using this
  have hre : z.re * w.re - z.im * w.im = r := by
    have := congrArg Complex.re hmul
    simpa using this
  have hnorm : 0 < z.re ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg z.re]
  have hprod : 0 < w.im * (z.re ^ 2 + z.im ^ 2) :=
    mul_pos hw hnorm
  have hrim : 0 ≤ r * z.im := mul_nonneg hr hz.le
  have him_mul := congrArg (fun x : ℝ => z.re * x) him
  have hre_mul := congrArg (fun x : ℝ => z.im * x) hre
  ring_nf at him_mul hre_mul
  nlinarith

/-- Every complex number outside the nonnegative real axis is a product of two
points in the open upper half-plane. -/
theorem exists_upperHalfPlane_mul_eq {z : ℂ}
    (hz : ∀ r : ℝ, 0 ≤ r → z ≠ r) :
    ∃ x y : ℂ, 0 < x.im ∧ 0 < y.im ∧ x * y = z := by
  by_cases hb : z.im = 0
  · have ha : z.re < 0 := by
      by_contra ha
      apply hz z.re (le_of_not_gt ha)
      apply Complex.ext
      · simp
      · simpa using hb
    refine ⟨Complex.I, (-(z.re) : ℂ) * Complex.I, by simp, ?_, ?_⟩
    · simpa using neg_pos.mpr ha
    · apply Complex.ext <;> simp [hb]
  · let t : ℝ := (z.re + 1) / z.im
    let x : ℂ := t + Complex.I
    have hxim : x.im = 1 := by simp [x]
    have hxne : x ≠ 0 := by
      intro hx
      have := congrArg Complex.im hx
      simp [hxim] at this
    have hnum : z.im * t - z.re = 1 := by
      dsimp [t]
      field_simp
      ring
    have hyim : 0 < (z / x).im := by
      rw [Complex.div_im]
      have hxnorm : 0 < Complex.normSq x := Complex.normSq_pos.mpr hxne
      have hxre : x.re = t := by simp [x]
      rw [hxim, hxre, mul_one, div_sub_div_same, hnum]
      positivity
    refine ⟨x, z / x, by simp [hxim], hyim, ?_⟩
    field_simp

/-- Root-factor evaluation of a split real polynomial after complexifying its
coefficients. -/
theorem eval_map_ofReal_eq_prod {p : ℝ[X]} (hp : p.Splits) {z : ℂ} :
    (p.map Complex.ofRealHom).eval z =
      (p.leadingCoeff : ℂ) *
        (p.roots.map (fun r : ℝ => z - (r : ℂ))).prod := by
  conv_lhs => rw [hp.eq_prod_roots]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.map_multiset_prod, Multiset.map_map,
    Polynomial.eval_multiset_prod, Function.comp_apply, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_X,
    Complex.ofRealHom_eq_coe]

end

end RealRooted
