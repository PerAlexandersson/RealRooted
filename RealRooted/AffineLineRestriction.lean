import RealRooted.MultivariateStability
import RealRooted.RootContinuity

/-!
# Affine-line restrictions of multivariate stable polynomials

This file characterizes multivariate real stability by the splitness and
non-vanishing of real affine-line restrictions in strictly positive
directions.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Restriction of a real multivariate polynomial to a real affine line. -/
def realAffineLineRestriction {σ : Type*} (a b : σ → ℝ)
    (P : MvPolynomial σ ℝ) : ℝ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) P

@[simp] theorem eval_realAffineLineRestriction {σ : Type*}
    (a b : σ → ℝ) (P : MvPolynomial σ ℝ) (t : ℝ) :
    (realAffineLineRestriction a b P).eval t =
      MvPolynomial.eval (fun i => a i + b i * t) P := by
  unfold realAffineLineRestriction
  change Polynomial.evalRingHom t
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext c
    simp
  rw [hC]
  rfl

@[simp] theorem eval_complexify_realAffineLineRestriction {σ : Type*}
    (a b : σ → ℝ) (P : MvPolynomial σ ℝ) :
    ∀ t : ℂ,
      ((realAffineLineRestriction a b P).map (algebraMap ℝ ℂ)).eval t =
      MvPolynomial.eval (fun i => a i + b i * t) (complexifyMv P) := by
  intro t
  unfold realAffineLineRestriction complexifyMv
  rw [Polynomial.eval_map]
  change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) t)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hC :
      (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) t).comp Polynomial.C =
        algebraMap ℝ ℂ := by
    ext r
    simp
  rw [hC]
  rw [MvPolynomial.eval_map]
  apply MvPolynomial.eval₂Hom_congr ?_ ?_ rfl
  · ext r
    simp
  · funext i
    simp

@[simp] theorem aeval_realAffineLineRestriction {σ : Type*}
    (a b : σ → ℝ) (P : MvPolynomial σ ℝ) (t : ℂ) :
    (realAffineLineRestriction a b P).aeval t =
      MvPolynomial.eval (fun i => a i + b i * t) (complexifyMv P) := by
  rw [Polynomial.aeval_def]
  rw [← Polynomial.eval_map]
  exact eval_complexify_realAffineLineRestriction a b P t

/-- Every positive-direction real affine restriction of a real stable
multivariate polynomial is nonzero and real-rooted. -/
theorem MvRealStable.realAffineLineRestriction_splits_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    (a b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    (realAffineLineRestriction a b P).Splits ∧
      realAffineLineRestriction a b P ≠ 0 := by
  let q := realAffineLineRestriction a b P
  have hq_splits : q.Splits := by
    apply splits_of_forall_aeval_im_eq_zero
    intro w hw
    by_contra him
    rcases lt_or_gt_of_ne him with him_neg | him_pos
    · have hw_conj : q.aeval (starRingEnd ℂ w) = 0 := by
        rw [Polynomial.aeval_conj, hw, map_zero]
      rw [aeval_realAffineLineRestriction] at hw_conj
      apply hP (fun i => (a i : ℂ) + (b i : ℂ) * starRingEnd ℂ w) ?_
        hw_conj
      intro i
      change 0 < ((a i : ℂ) + (b i : ℂ) * starRingEnd ℂ w).im
      simpa using mul_pos (hb i) (neg_pos.mpr him_neg)
    · rw [aeval_realAffineLineRestriction] at hw
      apply hP (fun i => (a i : ℂ) + (b i : ℂ) * w) ?_ hw
      intro i
      change 0 < ((a i : ℂ) + (b i : ℂ) * w).im
      simpa using mul_pos (hb i) him_pos
  refine ⟨hq_splits, ?_⟩
  intro hq_zero
  change q = 0 at hq_zero
  have hi : q.aeval Complex.I = 0 := by
    rw [hq_zero]
    simp
  rw [aeval_realAffineLineRestriction] at hi
  apply hP (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I) ?_ hi
  intro i
  simpa using hb i

/-- If every positive-direction real affine restriction is nonzero and
real-rooted, then the multivariate polynomial is real stable. -/
theorem mvRealStable_of_forall_realAffineLineRestriction
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : ∀ a b : σ → ℝ, (∀ i, 0 < b i) →
      (realAffineLineRestriction a b P).Splits ∧
        realAffineLineRestriction a b P ≠ 0) :
    MvRealStable P := by
  intro z hz
  let a : σ → ℝ := fun i => (z i).re
  let b : σ → ℝ := fun i => (z i).im
  have hb : ∀ i, 0 < b i := hz
  obtain ⟨hq_splits, hq_ne⟩ := hP a b hb
  intro hzero
  have hi : (realAffineLineRestriction a b P).aeval Complex.I = 0 := by
    rw [aeval_realAffineLineRestriction]
    have hz_eq :
        (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I) = z := by
      funext i
      exact Complex.ext (by simp [a, b]) (by simp [a, b])
    rw [hz_eq]
    exact hzero
  have him := im_eq_zero_of_aeval_eq_zero hq_ne hq_splits hi
  simp at him

/-- Real stability is equivalent to nonzero real-rootedness of every real
affine-line restriction in a strictly positive direction. -/
theorem mvRealStable_iff_forall_realAffineLineRestriction
    {σ : Type*} {P : MvPolynomial σ ℝ} :
    MvRealStable P ↔
      ∀ a b : σ → ℝ, (∀ i, 0 < b i) →
        (realAffineLineRestriction a b P).Splits ∧
          realAffineLineRestriction a b P ≠ 0 := by
  constructor
  · exact fun hP => hP.realAffineLineRestriction_splits_ne_zero
  · exact mvRealStable_of_forall_realAffineLineRestriction

end

end RealRooted
