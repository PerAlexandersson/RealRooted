import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative

/-!
# Ordinary homogenization of multivariate polynomials

This file defines total-degree homogenization by adjoining one distinguished
variable. It also records the algebraic identities needed by multivariate
stability arguments.
-/

open scoped BigOperators

namespace MvPolynomial

noncomputable section

/-- Ordinary total-degree homogenization. The new variable is indexed by
`none`; the original variables are indexed by `some i`. -/
def ordinaryHomogenization {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (d : ℕ) : MvPolynomial (Option σ) R :=
  ∑ k ∈ Finset.range (d + 1),
    X none ^ (d - k) * rename some (homogeneousComponent k p)

/-- Set the distinguished homogenizing variable to one. -/
def dehomogenize {σ R : Type*} [CommSemiring R] :
    MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R :=
  aeval fun o => Option.elim o 1 X

/-- Ordinary homogenization is homogeneous of the requested total degree. -/
theorem ordinaryHomogenization_isHomogeneous
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) (d : ℕ) :
    (ordinaryHomogenization p d).IsHomogeneous d := by
  unfold ordinaryHomogenization
  apply IsHomogeneous.sum
  intro k hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  convert (isHomogeneous_X_pow (R := R) (none : Option σ) (d - k)).mul
    (homogeneousComponent_isHomogeneous k p).rename_isHomogeneous using 1
  exact (Nat.sub_add_cancel hk').symm

/-- Taking a homogeneous component commutes with a coefficient map. -/
theorem map_homogeneousComponent {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (k : ℕ) (p : MvPolynomial σ R) :
    map f (homogeneousComponent k p) = homogeneousComponent k (map f p) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split <;> simp

/-- Ordinary homogenization commutes with a coefficient map. -/
theorem map_ordinaryHomogenization {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : MvPolynomial σ R) (d : ℕ) :
    map f (ordinaryHomogenization p d) = ordinaryHomogenization (map f p) d := by
  simp [ordinaryHomogenization, map_homogeneousComponent, map_rename]

/-- Ordinary homogenization preserves coefficientwise nonnegativity. -/
theorem HasNonnegCoeffs.ordinaryHomogenization {σ : Type*}
    {p : MvPolynomial σ ℝ} (hp : HasNonnegCoeffs p) (d : ℕ) :
    HasNonnegCoeffs (MvPolynomial.ordinaryHomogenization p d) := by
  classical
  unfold MvPolynomial.ordinaryHomogenization
  apply HasNonnegCoeffs.sum
  intro k _
  exact (HasNonnegCoeffs.X (none : Option σ)).pow (d - k) |>.mul
    ((hp.homogeneousComponent k).rename_of_injective
      (Option.some_injective σ))

/-- Dehomogenizing an ordinary homogenization whose requested degree is at
least the total degree recovers the source polynomial. -/
theorem dehomogenize_ordinaryHomogenization_of_totalDegree_le
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) {d : ℕ}
    (hdeg : p.totalDegree ≤ d) :
    dehomogenize (ordinaryHomogenization p d) = p := by
  rw [ordinaryHomogenization, map_sum]
  simp only [dehomogenize, map_mul, map_pow, aeval_X, Option.elim, one_pow,
    one_mul, aeval_rename]
  rw [← map_sum]
  have hsum :
      (∑ k ∈ Finset.range (d + 1), homogeneousComponent k p) = p := by
    calc
      _ = ∑ k ∈ Finset.range (p.totalDegree + 1), homogeneousComponent k p := by
        symm
        apply Finset.sum_subset
          (Finset.range_mono (Nat.add_le_add_right hdeg 1))
        intro k _ hk
        rw [homogeneousComponent_eq_zero]
        simp only [Finset.mem_range, Nat.not_lt] at hk
        exact lt_of_lt_of_le (Nat.lt_succ_self p.totalDegree) hk
      _ = p := sum_homogeneousComponent p
  rw [hsum]
  change aeval X p = p
  have h : aeval X = AlgHom.id R (MvPolynomial σ R) := by
    apply algHom_ext
    simp
  rw [h]
  rfl

/-- Dehomogenizing the exact total-degree homogenization recovers the source
polynomial. -/
theorem dehomogenize_ordinaryHomogenization
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) :
    dehomogenize (ordinaryHomogenization p p.totalDegree) = p :=
  dehomogenize_ordinaryHomogenization_of_totalDegree_le p le_rfl

/-- Ordinary homogenization above the total degree preserves nonzeroness. -/
theorem ordinaryHomogenization_ne_zero_of_totalDegree_le
    {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R} {d : ℕ}
    (hp : p ≠ 0) (hdeg : p.totalDegree ≤ d) :
    ordinaryHomogenization p d ≠ 0 := by
  intro h
  apply hp
  rw [← dehomogenize_ordinaryHomogenization_of_totalDegree_le p hdeg, h,
    map_zero]

/-- Exact total-degree homogenization preserves nonzeroness. -/
theorem ordinaryHomogenization_ne_zero
    {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ordinaryHomogenization p p.totalDegree ≠ 0 :=
  ordinaryHomogenization_ne_zero_of_totalDegree_le hp le_rfl

end

end MvPolynomial
