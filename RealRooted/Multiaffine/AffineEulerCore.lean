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

/-- The Rayleigh row naturally paired with a finite-index affine Euler core. -/
def affineEulerRayleighRow {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (P : MvPolynomial σ R) (i : ι) : MvPolynomial σ R :=
  P * pderiv (e i) P +
    ∑ j : ι, (1 - X (e j)) * rayleighDifference P (e i) (e j)

/-- The affine-Euler Rayleigh terms away from the selected row. -/
def affineEulerRayleighRemainder
    {R σ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (e : ι → σ) (P : MvPolynomial σ R) (i : ι) : MvPolynomial σ R :=
  ∑ j ∈ Finset.univ.erase i,
    (1 - X (e j)) * rayleighDifference P (e i) (e j)

private theorem affineEulerCore_X_mul_identity
    {S : Type*} [CommRing S] (c x b w d : S) :
    b + x * ((c - 1) * b - w + d) =
      c * (x * b) - (x * b + x * w) + (b + x * d) := by
  ring

/-- The affine Euler core is additive in its polynomial argument. -/
theorem affineEulerCore_add
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (c : R) (A B : MvPolynomial σ R) :
    affineEulerCore e c (A + B) =
      affineEulerCore e c A + affineEulerCore e c B := by
  classical
  simp only [affineEulerCore, mul_add, map_add,
    Finset.sum_add_distrib]
  ring_nf

/-- Adjoining a selected coordinate as a factor lowers the affine Euler
coefficient on the remaining factor by one. -/
theorem affineEulerCore_X_mul
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (he : Function.Injective e) (c : R)
    (B : MvPolynomial σ R) (i : ι) :
    affineEulerCore e c (X (e i) * B) =
      B + X (e i) * affineEulerCore e (c - 1) B := by
  classical
  have hsum : (∑ x : ι, (if i = x then 1 else 0) * B) = B := by
    simp
  have hweighted :
      (∑ x : ι, X (e x) *
        ((if i = x then 1 else 0) * B +
          X (e i) * pderiv (e x) B)) =
        X (e i) * B +
          X (e i) * (∑ x : ι, X (e x) * pderiv (e x) B) := by
    have hfirst : (∑ x : ι,
        X (e x) * (if i = x then 1 else 0) * B) =
        X (e i) * B := by
      simp
    have hsecond : (∑ x : ι,
        X (e x) * (X (e i) * pderiv (e x) B)) =
        X (e i) * ∑ x : ι, X (e x) * pderiv (e x) B := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    calc
      _ = ∑ x : ι, (X (e x) * (if i = x then 1 else 0) * B +
          X (e x) * (X (e i) * pderiv (e x) B)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := by rw [Finset.sum_add_distrib, hfirst, hsecond]
  have hderivs :
      (∑ x : ι, ((if i = x then 1 else 0) * B +
        X (e i) * pderiv (e x) B)) =
        B + X (e i) * ∑ x : ι, pderiv (e x) B := by
    rw [Finset.sum_add_distrib, hsum, Finset.mul_sum]
  have hC : C (c - 1) = (C c - 1 : MvPolynomial σ R) := by
    simp
  have hpderiv (x : ι) :
      pderiv (e x) (X (e i) * B) =
        (if i = x then 1 else 0) * B +
          X (e i) * pderiv (e x) B := by
    simp [pderiv_X, Pi.single_apply, he.eq_iff, eq_comm]
    ring
  unfold affineEulerCore
  simp_rw [hpderiv]
  rw [hweighted, hderivs, hC]
  exact (affineEulerCore_X_mul_identity _ _ _ _ _).symm

/-- The affine Euler core of an affine extension splits into its base core,
its slope, and the lowered-coefficient slope core. -/
theorem affineEulerCore_add_X_mul
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (he : Function.Injective e) (c : R)
    (A B : MvPolynomial σ R) (i : ι) :
    affineEulerCore e c (A + X (e i) * B) =
      affineEulerCore e c A + B +
        X (e i) * affineEulerCore e (c - 1) B := by
  rw [affineEulerCore_add, affineEulerCore_X_mul e he c B i]
  ring

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

/-- Specialization at one commutes with an affine Euler core in any selected
coordinate. -/
theorem specializeAt_one_affineEulerCore
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (he : Function.Injective e) (c : R)
    (P : MvPolynomial σ R) (i : ι) :
    specializeAt (e i) 1 (affineEulerCore e c P) =
      affineEulerCore e c (specializeAt (e i) 1 P) := by
  classical
  have hweighted :
      specializeAt (e i) 1
          (∑ j : ι, X (e j) * pderiv (e j) P) =
        (∑ j : ι, X (e j) *
          pderiv (e j) (specializeAt (e i) 1 P)) +
          specializeAt (e i) 1 (pderiv (e i) P) := by
    rw [specializeAt_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [specializeAt_mul, specializeAt_X,
      pderiv_specializeAt_self, mul_zero, add_zero]
    simp only [if_true, map_one, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have heji : e j ≠ e i := fun h => hji (he h)
    rw [if_neg heji, pderiv_specializeAt_of_ne heji]
  have hderivs :
      specializeAt (e i) 1 (∑ j : ι, pderiv (e j) P) =
        (∑ j : ι, pderiv (e j) (specializeAt (e i) 1 P)) +
          specializeAt (e i) 1 (pderiv (e i) P) := by
    rw [specializeAt_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [pderiv_specializeAt_self, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact (pderiv_specializeAt_of_ne (fun h => hji (he h)) 1 P).symm
  unfold affineEulerCore
  simp only [specializeAt_add, specializeAt_sub, specializeAt_mul,
    specializeAt_C, hweighted, hderivs]
  ring

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

/-- Partial differentiation lowers the affine Euler coefficient by one. -/
theorem pderiv_affineEulerCore
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (he : Function.Injective e) (c : R)
    (P : MvPolynomial σ R) (i : ι) :
    pderiv (e i) (affineEulerCore e c P) =
      affineEulerCore e (c - 1) (pderiv (e i) P) := by
  classical
  simp [affineEulerCore, pderiv_comm, Pi.single_apply, he.eq_iff,
    eq_comm, Finset.sum_add_distrib]
  ring

/-- The Wronskian of an affine Euler core against its source is the source
derivative plus an affine-weighted row of Rayleigh differences. -/
theorem coordinateWronskian_affineEulerCore
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (e : ι → σ) (he : Function.Injective e) (c : R)
    (P : MvPolynomial σ R) (i : ι) :
    coordinateWronskian (affineEulerCore e c P) P (e i) =
      affineEulerRayleighRow e P i := by
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
  unfold affineEulerCore affineEulerRayleighRow
  rw [coordinateWronskian_add_left, coordinateWronskian_sub_left,
    coordinateWronskian_C_mul_left, coordinateWronskian_self, mul_zero,
    zero_sub, heuler, hderiv, hsum]
  ring

/-- The affine-Euler Rayleigh row separates into its endpoint derivative
product and the Rayleigh terms away from the selected index. -/
theorem IsMultiaffine.affineEulerRayleighRow_eq_erase
    {R σ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (e : ι → σ) (i : ι) :
    affineEulerRayleighRow e P i =
      (specializeZero (e i) P + MvPolynomial.pderiv (e i) P) *
        MvPolynomial.pderiv (e i) P +
        affineEulerRayleighRemainder e P i := by
  classical
  have hdecomp := hP.eq_specializeZero_add_X_mul_pderiv (e i)
  unfold affineEulerRayleighRow affineEulerRayleighRemainder
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i),
    hP.rayleighDifference_self]
  linear_combination MvPolynomial.pderiv (e i) P * hdecomp

/-- A multiaffine affine-Euler Rayleigh row is independent of its own row
coordinate. -/
theorem IsMultiaffine.notMem_vars_affineEulerRayleighRow
    {R σ ι : Type*} [CommRing R] [Nontrivial R] [Fintype ι]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (e : ι → σ) (he : Function.Injective e) (i : ι) :
    e i ∉ (affineEulerRayleighRow e P i).vars := by
  rw [← coordinateWronskian_affineEulerCore e he 0 P i]
  exact (hP.affineEulerCore e 0).notMem_vars_coordinateWronskian hP (e i)

/-- For an injective coordinate family, the off-row remainder of a
multiaffine polynomial does not depend on the selected row coordinate. -/
theorem IsMultiaffine.notMem_vars_affineEulerRayleighRemainder
    {R σ ι : Type*} [CommRing R] [Nontrivial R] [Fintype ι]
    [DecidableEq ι] {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (e : ι → σ) (he : Function.Injective e) (i : ι) :
    e i ∉ (affineEulerRayleighRemainder e P i).vars := by
  classical
  have hzero : e i ∉ (specializeZero (e i) P).vars := by
    intro h
    have herase := vars_specializeZero_subset_erase P (e i) h
    exact (Finset.mem_erase.mp herase).1 rfl
  have hderiv : e i ∉ (MvPolynomial.pderiv (e i) P).vars :=
    hP.notMem_vars_pderiv_self (e i)
  have hadd : e i ∉
      (specializeZero (e i) P + MvPolynomial.pderiv (e i) P).vars := by
    intro h
    exact (Finset.mem_union.mp (vars_add_subset _ _ h)).elim hzero hderiv
  have hproduct : e i ∉
      ((specializeZero (e i) P + MvPolynomial.pderiv (e i) P) *
        MvPolynomial.pderiv (e i) P).vars := by
    intro h
    exact (Finset.mem_union.mp (vars_mul _ _ h)).elim hadd hderiv
  have hremainder : affineEulerRayleighRemainder e P i =
      affineEulerRayleighRow e P i -
        (specializeZero (e i) P + MvPolynomial.pderiv (e i) P) *
          MvPolynomial.pderiv (e i) P := by
    have hrow := hP.affineEulerRayleighRow_eq_erase e i
    calc
      _ = ((specializeZero (e i) P + MvPolynomial.pderiv (e i) P) *
          MvPolynomial.pderiv (e i) P +
            affineEulerRayleighRemainder e P i) -
          (specializeZero (e i) P + MvPolynomial.pderiv (e i) P) *
            MvPolynomial.pderiv (e i) P := by ring
      _ = _ := by rw [← hrow]
  rw [hremainder]
  intro h
  exact (Finset.mem_union.mp (vars_sub_subset
    (p := affineEulerRayleighRow e P i)
    (q := (specializeZero (e i) P + MvPolynomial.pderiv (e i) P) *
      MvPolynomial.pderiv (e i) P) h)).elim
    (hP.notMem_vars_affineEulerRayleighRow e he i) hproduct

end

end MvPolynomial
