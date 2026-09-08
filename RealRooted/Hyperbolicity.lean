import Mathlib.Analysis.Convex.PathConnected
import RealRooted.HomogeneousComponentStability
import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic

/-!
# Hyperbolicity and multivariate real stability

This file relates Gårding hyperbolicity to multivariate real stability and
proves boundary hyperbolicity of ordinary homogenization.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The project-local real affine-line restriction is the real specialization
of the generic upstream-shaped definition. -/
theorem realAffineLineRestriction_eq_affineLineRestriction
    {σ : Type*} (x e : σ → ℝ) (P : MvPolynomial σ ℝ) :
    realAffineLineRestriction x e P =
      MvPolynomial.affineLineRestriction x e P := rfl

/-- Restricting a homogeneous polynomial to a line through zero produces a
monomial whose coefficient is its value at the direction vector. -/
theorem MvPolynomial.IsHomogeneous.affineLineRestriction_zero
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) (e : σ → ℝ) :
    MvPolynomial.affineLineRestriction (fun _ => 0) e P =
      Polynomial.C (MvPolynomial.eval e P) * Polynomial.X ^ d := by
  apply Polynomial.funext
  intro t
  rw [MvPolynomial.eval_affineLineRestriction]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  simpa [mul_comm] using hP.eval_smul t e

/-- For a homogeneous polynomial, hyperbolicity gives split and nonzero
affine-line restrictions in the hyperbolic direction. -/
theorem MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℝ} {e : σ → ℝ}
    (hP : P.HyperbolicAt e) {d : ℕ} (hhom : P.IsHomogeneous d)
    (x : σ → ℝ) :
    (MvPolynomial.affineLineRestriction x e P).Splits ∧
      MvPolynomial.affineLineRestriction x e P ≠ 0 := by
  refine ⟨hP.2 x, ?_⟩
  intro hzero
  have hcoeff :=
    MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction hhom x e
  apply hP.1
  rw [realAffineLineRestriction_eq_affineLineRestriction, hzero] at hcoeff
  simpa using hcoeff.symm

/-- A homogeneous real stable polynomial is hyperbolic in every strictly
positive direction. -/
theorem MvRealStable.hyperbolicAt_of_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    {d : ℕ} (hhom : P.IsHomogeneous d) {e : σ → ℝ}
    (he : ∀ i, 0 < e i) :
    P.HyperbolicAt e := by
  have hline := hst.realAffineLineRestriction_splits_ne_zero
    (fun _ => 0) e he
  refine ⟨?_, fun x => ?_⟩
  · intro heval
    apply hline.2
    rw [realAffineLineRestriction_eq_affineLineRestriction,
      MvPolynomial.IsHomogeneous.affineLineRestriction_zero hhom e, heval]
    simp
  · simpa [← realAffineLineRestriction_eq_affineLineRestriction] using
      (hst.realAffineLineRestriction_splits_ne_zero x e he).1

/-- If a homogeneous polynomial is hyperbolic in every strictly positive
direction, then it is multivariate real stable. -/
theorem mvRealStable_of_forall_hyperbolicAt_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d)
    (hP : ∀ e : σ → ℝ, (∀ i, 0 < e i) → P.HyperbolicAt e) :
    MvRealStable P := by
  apply mvRealStable_of_forall_realAffineLineRestriction
  intro a b hb
  have hh := hP b hb
  simpa [realAffineLineRestriction_eq_affineLineRestriction] using
    MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
      hh hhom a

/-- A homogeneous polynomial is real stable exactly when it is hyperbolic in
every strictly positive direction. -/
theorem MvPolynomial.IsHomogeneous.mvRealStable_iff_forall_hyperbolicAt_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d) :
    MvRealStable P ↔
      ∀ e : σ → ℝ, (∀ i, 0 < e i) → P.HyperbolicAt e := by
  exact ⟨fun hst e he => hst.hyperbolicAt_of_pos hhom he,
    mvRealStable_of_forall_hyperbolicAt_pos hhom⟩

private theorem restriction_ordinaryHomogenization_eq_of_none_ne_zero
    {σ : Type*} (P : MvPolynomial σ ℝ) (x : Option σ → ℝ)
    (b : σ → ℝ) (hx : x none ≠ 0) :
    realAffineLineRestriction x (fun o => Option.elim o 0 b)
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) =
      Polynomial.C ((x none) ^ P.totalDegree) *
        realAffineLineRestriction (fun i => x (some i) / x none)
          (fun i => b i / x none) P := by
  apply Polynomial.funext
  intro t
  rw [eval_realAffineLineRestriction, Polynomial.eval_mul,
    Polynomial.eval_C, eval_realAffineLineRestriction]
  have hvec :
      (fun o => x o + Option.elim o 0 b * t) =
        fun o => Option.elim o (x none)
          (fun i => x (some i) + b i * t) := by
    funext o
    cases o <;> simp
  rw [hvec,
    MvPolynomial.eval_ordinaryHomogenization_eq_pow_mul_eval_div
      P le_rfl hx]
  congr 1
  apply congrArg (fun z => MvPolynomial.eval z P)
  funext i
  field_simp

private theorem restriction_ordinaryHomogenization_eq_of_none_eq_zero
    {σ : Type*} (P : MvPolynomial σ ℝ) (x : Option σ → ℝ)
    (b : σ → ℝ) (hx : x none = 0) :
    realAffineLineRestriction x (fun o => Option.elim o 0 b)
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) =
      realAffineLineRestriction (fun i => x (some i)) b
        (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  apply Polynomial.funext
  intro t
  rw [eval_realAffineLineRestriction, eval_realAffineLineRestriction]
  have hvec :
      (fun o => x o + Option.elim o 0 b * t) =
        fun o => Option.elim o 0 (fun i => x (some i) + b i * t) := by
    funext o
    cases o <;> simp [hx]
  rw [hvec, MvPolynomial.eval_ordinaryHomogenization_zero]

private theorem realAffineLineRestriction_neg_direction
    {σ : Type*} (P : MvPolynomial σ ℝ) (a b : σ → ℝ) :
    realAffineLineRestriction a (fun i => -b i) P =
      (realAffineLineRestriction a b P).comp (-Polynomial.X) := by
  apply Polynomial.funext
  intro t
  simp [eval_realAffineLineRestriction, Polynomial.eval_comp]

/-- Ordinary homogenization is hyperbolic in every direction that is positive
on the original coordinates and zero on the homogenizing coordinate. This is
the boundary-direction part of the stability--hyperbolicity bridge. -/
theorem MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0)
    (b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    (MvPolynomial.ordinaryHomogenization P P.totalDegree).HyperbolicAt
      (fun o => Option.elim o 0 b) := by
  let H := MvPolynomial.ordinaryHomogenization P P.totalDegree
  let e : Option σ → ℝ := fun o => Option.elim o 0 b
  let Htop := MvPolynomial.homogeneousComponent P.totalDegree P
  have hHtopNe : Htop ≠ 0 := by
    exact MvPolynomial.homogeneousComponent_totalDegree_ne_zero hP
  have hHtopNN : MvPolynomial.HasNonnegCoeffs Htop := by
    exact hnn.homogeneousComponent P.totalDegree
  have hEvalTopPos : 0 < MvPolynomial.eval b Htop :=
    hHtopNN.eval_pos hHtopNe hb
  have hEval : MvPolynomial.eval e H = MvPolynomial.eval b Htop := by
    simpa [e, H, Htop] using
      MvPolynomial.eval_ordinaryHomogenization_zero P P.totalDegree b
  refine ⟨hEval.trans_ne hEvalTopPos.ne', ?_⟩
  intro x
  change (realAffineLineRestriction x e H).Splits
  by_cases hx : x none = 0
  · rw [restriction_ordinaryHomogenization_eq_of_none_eq_zero P x b hx]
    exact (MvRealStable.realAffineLineRestriction_splits_ne_zero
      (MvRealStable.homogeneousComponent_totalDegree hst hnn hP)
        (fun i => x (some i)) b hb).1
  · rw [restriction_ordinaryHomogenization_eq_of_none_ne_zero P x b hx]
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · let a : σ → ℝ := fun i => x (some i) / x none
      let c : σ → ℝ := fun i => -(b i / x none)
      have hc : ∀ i, 0 < c i := by
        intro i
        exact neg_pos.mpr (div_neg_of_pos_of_neg (hb i) hxneg)
      have hsplits :=
        (hst.realAffineLineRestriction_splits_ne_zero a c hc).1
      have hreflect :
          realAffineLineRestriction (fun i => x (some i) / x none)
              (fun i => b i / x none) P =
            (realAffineLineRestriction a c P).comp (-Polynomial.X) := by
        simpa [a, c] using
          realAffineLineRestriction_neg_direction P a c
      rw [hreflect]
      exact hsplits.comp_neg_X.C_mul _
    · exact ((hst.realAffineLineRestriction_splits_ne_zero
        (fun i => x (some i) / x none) (fun i => b i / x none)
        (fun i => div_pos (hb i) hxpos)).1).C_mul _

/-- Every positive original-coordinate boundary direction is joined to every
strictly positive direction inside the nonvanishing locus of a nonzero
ordinary homogenization with nonnegative coefficients. -/
theorem MvPolynomial.HasNonnegCoeffs.ordinaryHomogenization_boundary_joinedIn_positive
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0)
    (b : σ → ℝ) (hb : ∀ i, 0 < b i)
    (u : Option σ → ℝ) (hu : ∀ o, 0 < u o) :
    JoinedIn
      {x | MvPolynomial.eval x
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) ≠ 0}
      (fun o => Option.elim o 0 b) u := by
  let Q := MvPolynomial.ordinaryHomogenization P P.totalDegree
  let e : Option σ → ℝ := fun o => Option.elim o 0 b
  let Htop := MvPolynomial.homogeneousComponent P.totalDegree P
  have hQnn : MvPolynomial.HasNonnegCoeffs Q := by
    exact hnn.ordinaryHomogenization P.totalDegree
  have hQne : Q ≠ 0 := MvPolynomial.ordinaryHomogenization_ne_zero hP
  have hHtopNe : Htop ≠ 0 :=
    MvPolynomial.homogeneousComponent_totalDegree_ne_zero hP
  have hboundaryPos : 0 < MvPolynomial.eval e Q := by
    rw [show MvPolynomial.eval e Q = MvPolynomial.eval b Htop by
      simpa [e, Q, Htop] using
        MvPolynomial.eval_ordinaryHomogenization_zero P P.totalDegree b]
    exact (hnn.homogeneousComponent P.totalDegree).eval_pos hHtopNe hb
  apply JoinedIn.of_segment_subset
  rw [segment_eq_image]
  rintro x ⟨t, ht, rfl⟩
  rcases ht with ⟨ht0, ht1⟩
  by_cases htzero : t = 0
  · subst t
    simpa [e] using hboundaryPos.ne'
  · apply (hQnn.eval_pos hQne ?_).ne'
    intro o
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    cases o with
    | none =>
        simpa [e] using mul_pos htpos (hu none)
    | some i =>
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr ht1) (hb i).le)
          (mul_pos htpos (hu (some i)))

end

end RealRooted
