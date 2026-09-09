import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Hyperbolic multivariate polynomials

This file contains definitions intended for upstreaming to
`Mathlib.RingTheory.MvPolynomial.Hyperbolic`.
-/

open Polynomial

namespace MvPolynomial

noncomputable section

/-- Restrict a multivariate polynomial to the affine line `x + t e`. -/
def affineLineRestriction {σ R : Type*} [CommSemiring R]
    (x e : σ → R) (P : MvPolynomial σ R) : R[X] :=
  eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (e i) * Polynomial.X) P

@[simp] theorem eval_affineLineRestriction
    {σ R : Type*} [CommSemiring R] (x e : σ → R)
    (P : MvPolynomial σ R) (t : R) :
    (affineLineRestriction x e P).eval t =
      MvPolynomial.eval (fun i => x i + e i * t) P := by
  unfold affineLineRestriction
  change Polynomial.evalRingHom t
      (eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) + Polynomial.C (e i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id R := by
    ext c
    simp
  rw [hC]
  rfl

private theorem coeff_prod_affine_pow_total
    {σ R : Type*} [CommSemiring R] (s : Finset σ)
    (a b : σ → R) (e : σ → ℕ) :
    (∏ i ∈ s,
      (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) ^ e i).coeff
        (∑ i ∈ s, e i) =
      ∏ i ∈ s, b i ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      let g : σ → R[X] := fun j =>
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
    {σ R : Type*} [CommSemiring R] (s : Finset σ)
    (a b : σ → R) (e : σ → ℕ) :
    (∏ i ∈ s,
      (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) ^ e i).natDegree ≤
      ∑ i ∈ s, e i := by
  classical
  apply (Polynomial.natDegree_prod_le s fun i =>
    (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) ^ e i).trans
  apply Finset.sum_le_sum
  intro i hi
  have hlin :
      (Polynomial.C (a i) +
        Polynomial.C (b i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simp)
      ((Polynomial.natDegree_C_mul_le (b i) Polynomial.X).trans
        Polynomial.natDegree_X_le)
  simpa using Polynomial.natDegree_pow_le_of_le (e i) hlin

/-- An affine-line restriction has univariate degree at most the total degree
of the multivariate polynomial. -/
theorem natDegree_affineLineRestriction_le
    {σ R : Type*} [CommSemiring R] (a b : σ → R)
    (P : MvPolynomial σ R) :
    (affineLineRestriction a b P).natDegree ≤ P.totalDegree := by
  classical
  unfold affineLineRestriction
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) +
      Polynomial.C (b i) * Polynomial.X) P).natDegree ≤ P.totalDegree
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact (natDegree_prod_affine_pow_le_total m.support a b m).trans
    (MvPolynomial.le_totalDegree hm)

/-- The top coefficient of an affine-line restriction of a homogeneous
polynomial is its evaluation on the direction vector. -/
theorem IsHomogeneous.coeff_affineLineRestriction
    {σ R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) (a b : σ → R) :
    (affineLineRestriction a b P).coeff d = MvPolynomial.eval b P := by
  classical
  unfold affineLineRestriction
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) P).coeff d = _
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff,
    MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hP.degree_eq_sum_deg_support hm, Polynomial.coeff_C_mul,
    coeff_prod_affine_pow_total]

/-- An affine-line restriction of a degree-`d` homogeneous polynomial has
univariate degree at most `d`. -/
theorem IsHomogeneous.natDegree_affineLineRestriction_le
    {σ R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) (a b : σ → R) :
    (affineLineRestriction a b P).natDegree ≤ d := by
  classical
  unfold affineLineRestriction
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) +
      Polynomial.C (b i) * Polynomial.X) P).natDegree ≤ d
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [hP.degree_eq_sum_deg_support hm]
  exact natDegree_prod_affine_pow_le_total m.support a b m

/-- If the value at the direction vector is nonzero, a homogeneous
affine-line restriction has exactly the homogeneous degree. -/
theorem IsHomogeneous.natDegree_affineLineRestriction_eq
    {σ R : Type*} [CommSemiring R] [Nontrivial R]
    {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) (a b : σ → R)
    (hb : MvPolynomial.eval b P ≠ 0) :
    (affineLineRestriction a b P).natDegree = d := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hP.natDegree_affineLineRestriction_le a b)
    ((hP.coeff_affineLineRestriction a b).trans_ne hb)

/-- Restrict a multivariate polynomial to the linear plane spanned by `e` and
`u`, with plane coordinates indexed by `Fin 2`. -/
def linearPlaneRestriction {σ R : Type*} [CommSemiring R]
    (e u : σ → R) (P : MvPolynomial σ R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval
    (fun i => MvPolynomial.C (e i) * MvPolynomial.X 0 +
      MvPolynomial.C (u i) * MvPolynomial.X 1) P

@[simp] theorem eval_linearPlaneRestriction
    {σ R : Type*} [CommSemiring R] (e u : σ → R)
    (P : MvPolynomial σ R) (z : Fin 2 → R) :
    MvPolynomial.eval z (linearPlaneRestriction e u P) =
      MvPolynomial.eval (fun i => e i * z 0 + u i * z 1) P := by
  unfold linearPlaneRestriction
  change MvPolynomial.eval₂Hom (RingHom.id R) z
      (eval₂Hom MvPolynomial.C
        (fun i => MvPolynomial.C (e i) * MvPolynomial.X 0 +
          MvPolynomial.C (u i) * MvPolynomial.X 1) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hC : (MvPolynomial.eval₂Hom (RingHom.id R) z).comp
      MvPolynomial.C = RingHom.id R := by
    ext c
    simp
  rw [hC]
  apply MvPolynomial.eval₂_congr _ _
  intro i _ _ _
  simp

/-- A polynomial is hyperbolic at `e` when it does not vanish there and every
affine-line restriction in direction `e` splits over the coefficient semiring.
For the standard notion, use this predicate with a homogeneity hypothesis. -/
def HyperbolicAt {σ R : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (e : σ → R) : Prop :=
  MvPolynomial.eval e P ≠ 0 ∧
    ∀ x : σ → R, (affineLineRestriction x e P).Splits

end

end MvPolynomial
