import RealRooted.Multiaffine.CoordinateWronskian

/-!
# Finite-index affine Euler cores

This file packages the affine Euler core attached to a finite family of
coordinates.  The construction is independent of any particular
combinatorial indexing convention and commutes with injective variable
renaming.
-/

namespace MvPolynomial

open scoped BigOperators

noncomputable section

/-- The affine Euler core over the coordinates selected by `e`. -/
def affineEulerCore {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (c : R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  C c * P - ∑ i : ι, X (e i) * pderiv (e i) P +
    ∑ i : ι, pderiv (e i) P

/-- Affine Euler cores commute with injective variable renaming. -/
theorem rename_affineEulerCore
    {R σ τ ι : Type*} [CommRing R] [Fintype ι]
    (g : σ → τ) (hg : Function.Injective g) (e : ι → σ)
    (c : R) (P : MvPolynomial σ R) :
    rename g (affineEulerCore e c P) =
      affineEulerCore (g ∘ e) c (rename g P) := by
  classical
  simp only [affineEulerCore, map_add, map_sub, map_mul, map_sum,
    rename_C, rename_X, pderiv_rename hg, Function.comp_apply]

/-- Affine Euler cores preserve multiaffineness. -/
theorem IsMultiaffine.affineEulerCore
    {R σ ι : Type*} [CommRing R] [Nontrivial R] [Fintype ι]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (e : ι → σ) (c : R) : IsMultiaffine (affineEulerCore e c P) := by
  classical
  unfold MvPolynomial.affineEulerCore
  have hweighted : IsMultiaffine
      (∑ i : ι, MvPolynomial.X (e i) *
        MvPolynomial.pderiv (e i) P) := by
    apply IsMultiaffine.sum
    intro i hi
    exact (hP.pderiv (e i)).X_mul_of_notMem_vars
      (hP.notMem_vars_pderiv_self (e i))
  have hderivs : IsMultiaffine
      (∑ i : ι, MvPolynomial.pderiv (e i) P) := by
    apply IsMultiaffine.sum
    intro i hi
    exact hP.pderiv (e i)
  exact ((hP.C_mul c).sub hweighted).add hderivs

/-- The Wronskian of an affine Euler core against its source is the source
derivative plus an affine-weighted row of Rayleigh differences. -/
theorem coordinateWronskian_affineEulerCore
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (he : Function.Injective e) (c : R)
    (P : MvPolynomial σ R) (i : ι) :
    coordinateWronskian (affineEulerCore e c P) P (e i) =
      P * pderiv (e i) P +
        ∑ j : ι, (1 - X (e j)) * rayleighDifference P (e i) (e j) := by
  classical
  have hderiv := coordinateWronskian_sum_pderiv_left
    e (fun _ : ι => (1 : R)) P (e i)
  simp only [map_one, one_mul] at hderiv
  have heuler := coordinateWronskian_sum_X_mul_pderiv_left e he P i
  have hsum :
      (∑ j : ι, (1 - X (e j)) * rayleighDifference P (e i) (e j)) =
        (∑ j : ι, rayleighDifference P (e i) (e j)) -
          ∑ j : ι, X (e j) * rayleighDifference P (e i) (e j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold affineEulerCore
  rw [coordinateWronskian_add_left, coordinateWronskian_sub_left,
    coordinateWronskian_C_mul_left, coordinateWronskian_self, mul_zero,
    zero_sub, heuler, hderiv, hsum]
  ring

end

end MvPolynomial
