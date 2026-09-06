import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative
import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv

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

@[simp] theorem eval_dehomogenize {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial (Option σ) R) (z : σ → R) :
    eval z (dehomogenize p) =
      eval (fun o => Option.elim o 1 z) p := by
  unfold dehomogenize
  change (aeval z) ((aeval (fun o => Option.elim o (C 1) X)) p) =
    (aeval (fun o => Option.elim o 1 z)) p
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 1
  apply algHom_ext
  intro o
  cases o <;> simp

/-- Dehomogenization is evaluation of the distinguished-variable polynomial
at one. -/
theorem dehomogenize_eq_optionEquivLeft_eval_one
    {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial (Option σ) R) :
    dehomogenize p = (optionEquivLeft R σ p).eval 1 := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [dehomogenize]
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      cases i <;> simp [dehomogenize]

/-- Dehomogenization commutes with a rename that preserves the distinguished
variable. -/
theorem dehomogenize_rename_option_map
    {R σ τ : Type*} [CommSemiring R] (f : σ → τ)
    (p : MvPolynomial (Option σ) R) :
    dehomogenize (rename (Option.map f) p) =
      rename f (dehomogenize p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [dehomogenize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      cases i <;> simp [dehomogenize]

/-- Dehomogenizing after embedding every source variable as an ordinary
variable recovers the source polynomial. -/
@[simp] theorem dehomogenize_rename_some
    {R σ : Type*} [CommSemiring R] (p : MvPolynomial σ R) :
    dehomogenize (rename some p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [dehomogenize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      simp [dehomogenize]

/-- The top coefficient in the homogenizing variable is the constant term of
the dehomogenized homogeneous polynomial. -/
theorem IsHomogeneous.optionEquivLeft_coeff_eq_C_coeff_zero_dehomogenize
    {R σ : Type*} [CommSemiring R] [Finite σ]
    {p : MvPolynomial (Option σ) R} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (optionEquivLeft R σ p).coeff d =
      C (coeff 0 (dehomogenize p)) := by
  let q : Polynomial (MvPolynomial σ R) := optionEquivLeft R σ p
  have hqdeg : q.natDegree ≤ d := by
    calc
      q.natDegree = p.degreeOf none :=
        natDegree_optionEquivLeft (R := R) (σ := σ) p
      _ ≤ p.totalDegree := degreeOf_le_totalDegree p none
      _ ≤ d := hp.totalDegree_le
  have hconst : q.coeff d = C (coeff 0 (q.coeff d)) := by
    rw [← totalDegree_eq_zero_iff_eq_C]
    rw [totalDegree_zero_iff_isHomogeneous]
    apply coeff_isHomogeneous_of_optionEquivLeft_symm
      (n := d) (i := d) (j := 0)
    · simpa [q] using hp
    · lia
  rw [show optionEquivLeft R σ p = q by rfl, hconst]
  congr 1
  rw [dehomogenize_eq_optionEquivLeft_eval_one]
  change coeff 0 (q.coeff d) = coeff 0 (q.eval 1)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hqdeg)]
  simp only [one_pow, mul_one]
  rw [coeff_sum]
  rw [Finset.sum_eq_single d]
  · intro i hi hid
    have hi_le : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hihom : (q.coeff i).IsHomogeneous (d - i) := by
      apply coeff_isHomogeneous_of_optionEquivLeft_symm
        (n := d) (i := i) (j := d - i)
      · simpa [q] using hp
      · lia
    by_contra hcoeff
    have hmem : 0 ∈ (q.coeff i).support := mem_support_iff.mpr hcoeff
    have hdegree := hihom.degree_eq_sum_deg_support hmem
    have : d - i = 0 := by simpa using hdegree
    lia
  · simp

@[simp] theorem dehomogenize_X_none {σ R : Type*} [CommSemiring R] :
    dehomogenize (X (none : Option σ) : MvPolynomial (Option σ) R) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_X_some {σ R : Type*} [CommSemiring R]
    (i : σ) :
    dehomogenize (X (some i) : MvPolynomial (Option σ) R) = X i := by
  simp [dehomogenize]

/-- Dehomogenization commutes with differentiation in an original variable. -/
theorem dehomogenize_pderiv_some {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial (Option σ) R) (i : σ) :
    dehomogenize (pderiv (some i) p) =
      pderiv i (dehomogenize p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      cases j with
      | none => simp [hp]
      | some j =>
          by_cases hij : i = j
          · subst j
            simp [hp]
          · simp [hp, hij]

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

/-- Raising the requested homogenization degree only adds a power of the
distinguished variable. -/
theorem ordinaryHomogenization_eq_X_pow_mul
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) {d : ℕ}
    (hdeg : p.totalDegree ≤ d) :
    ordinaryHomogenization p d =
      X none ^ (d - p.totalDegree) *
        ordinaryHomogenization p p.totalDegree := by
  classical
  rw [ordinaryHomogenization, ordinaryHomogenization, Finset.mul_sum]
  calc
    _ = ∑ k ∈ Finset.range (p.totalDegree + 1),
        X none ^ (d - k) * rename some (homogeneousComponent k p) := by
      symm
      apply Finset.sum_subset
        (Finset.range_mono (Nat.add_le_add_right hdeg 1))
      intro k _ hk
      rw [homogeneousComponent_eq_zero]
      · simp
      · simp only [Finset.mem_range, Nat.not_lt] at hk
        exact lt_of_lt_of_le (Nat.lt_succ_self p.totalDegree) hk
    _ = ∑ k ∈ Finset.range (p.totalDegree + 1),
        X none ^ (d - p.totalDegree) *
          (X none ^ (p.totalDegree - k) *
            rename some (homogeneousComponent k p)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ p.totalDegree :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hexp :
          d - p.totalDegree + (p.totalDegree - k) = d - k := by
        rw [← Nat.add_sub_assoc hk', Nat.sub_add_cancel hdeg]
      rw [← mul_assoc, ← pow_add, hexp]
    _ = _ := rfl

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
