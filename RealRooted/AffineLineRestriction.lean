import RealRooted.MultivariateStability
import RealRooted.Mathlib.RingTheory.MvPolynomial.Homogeneous
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

private theorem coeff_prod_affine_pow_total
    {σ : Type*} (s : Finset σ) (a b : σ → ℝ) (e : σ → ℕ) :
    (∏ i ∈ s,
      (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) ^ e i).coeff
        (∑ i ∈ s, e i) =
      ∏ i ∈ s, b i ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      let g : σ → ℝ[X] := fun j =>
        Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X
      have hlin (j : σ) : (g j).natDegree ≤ 1 := by
        apply (Polynomial.natDegree_add_le _ _).trans
        exact max_le (by simp)
          ((Polynomial.natDegree_C_mul_le (b j) Polynomial.X).trans
            Polynomial.natDegree_X_le)
      have hpow (j : σ) : ((g j) ^ e j).natDegree ≤ e j := by
        simpa using Polynomial.natDegree_pow_le_of_le (e j) (hlin j)
      have hrest :
          (∏ j ∈ s, (g j) ^ e j).natDegree ≤ ∑ j ∈ s, e j :=
        (Polynomial.natDegree_prod_le s fun j => (g j) ^ e j).trans
          (Finset.sum_le_sum fun j hj => hpow j)
      have hcoeff : ((g i) ^ e i).coeff (e i) = b i ^ e i := by
        simpa [g] using
          Polynomial.coeff_pow_of_natDegree_le (m := e i) (hlin i)
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hpow i) hrest,
        hcoeff, ih]

private theorem natDegree_prod_affine_pow_le_total
    {σ : Type*} (s : Finset σ) (a b : σ → ℝ) (e : σ → ℕ) :
    (∏ i ∈ s,
      (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) ^ e i).natDegree ≤
      ∑ i ∈ s, e i := by
  classical
  apply (Polynomial.natDegree_prod_le s fun i =>
    (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) ^ e i).trans
  apply Finset.sum_le_sum
  intro i hi
  have hlin :
      (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simp)
      ((Polynomial.natDegree_C_mul_le (b i) Polynomial.X).trans
        Polynomial.natDegree_X_le)
  simpa using Polynomial.natDegree_pow_le_of_le (e i) hlin

/-- The top coefficient of an affine-line restriction of a homogeneous
polynomial is its evaluation on the direction vector. -/
theorem MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction
    {σ : Type*} {H : MvPolynomial σ ℝ} {d : ℕ}
    (hH : H.IsHomogeneous d) (a b : σ → ℝ) :
    (realAffineLineRestriction a b H).coeff d =
      MvPolynomial.eval b H := by
  classical
  unfold realAffineLineRestriction
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) H).coeff d = _
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff,
    MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hH.degree_eq_sum_deg_support hm, Polynomial.coeff_C_mul,
    coeff_prod_affine_pow_total]

/-- An affine-line restriction of a degree-`d` homogeneous polynomial has
univariate degree at most `d`. -/
theorem MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
    {σ : Type*} {H : MvPolynomial σ ℝ} {d : ℕ}
    (hH : H.IsHomogeneous d) (a b : σ → ℝ) :
    (realAffineLineRestriction a b H).natDegree ≤ d := by
  classical
  unfold realAffineLineRestriction
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) H).natDegree ≤ d
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [hH.degree_eq_sum_deg_support hm]
  exact natDegree_prod_affine_pow_le_total m.support a b m

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
