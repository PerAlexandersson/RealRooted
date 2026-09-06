import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Multivariate polynomials with nonnegative coefficients

This file provides the coefficientwise nonnegativity predicate and its basic
closure properties for real multivariate polynomials.
-/

open scoped BigOperators

namespace MvPolynomial

/-- Every coefficient of `P` is nonnegative. -/
def HasNonnegCoeffs {σ : Type*} (P : MvPolynomial σ ℝ) : Prop :=
  ∀ m, 0 ≤ coeff m P

namespace HasNonnegCoeffs

theorem zero {σ : Type*} : HasNonnegCoeffs (0 : MvPolynomial σ ℝ) := by
  intro m
  simp

theorem one {σ : Type*} : HasNonnegCoeffs (1 : MvPolynomial σ ℝ) := by
  classical
  intro m
  simp only [coeff_one]
  split <;> simp

theorem C {σ : Type*} {r : ℝ} (hr : 0 ≤ r) :
    HasNonnegCoeffs (MvPolynomial.C r : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [coeff_C]
  split <;> simp_all

theorem X {σ : Type*} (i : σ) :
    HasNonnegCoeffs (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  classical
  intro m
  simp only [coeff_X]
  split <;> simp

theorem add {σ : Type*} {P Q : MvPolynomial σ ℝ}
    (hP : HasNonnegCoeffs P) (hQ : HasNonnegCoeffs Q) :
    HasNonnegCoeffs (P + Q) := by
  intro m
  rw [coeff_add]
  exact add_nonneg (hP m) (hQ m)

theorem mul {σ : Type*} {P Q : MvPolynomial σ ℝ}
    (hP : HasNonnegCoeffs P) (hQ : HasNonnegCoeffs Q) :
    HasNonnegCoeffs (P * Q) := by
  classical
  intro m
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hP x.1) (hQ x.2)

theorem pow {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : HasNonnegCoeffs P) (n : ℕ) :
    HasNonnegCoeffs (P ^ n) := by
  induction n with
  | zero => simpa using (one (σ := σ))
  | succ n ih => simpa [pow_succ] using mul ih hP

theorem rename_of_injective {σ τ : Type*} {P : MvPolynomial σ ℝ}
    (hP : HasNonnegCoeffs P) {f : σ → τ} (hf : Function.Injective f) :
    HasNonnegCoeffs (MvPolynomial.rename f P) := by
  classical
  intro m
  by_cases hm : MvPolynomial.coeff m (MvPolynomial.rename f P) = 0
  · simp [hm]
  · obtain ⟨u, rfl, _⟩ := MvPolynomial.coeff_rename_ne_zero f P m hm
    rw [MvPolynomial.coeff_rename_mapDomain f hf]
    exact hP u

theorem homogeneousComponent {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : HasNonnegCoeffs P) (n : ℕ) :
    HasNonnegCoeffs (MvPolynomial.homogeneousComponent n P) := by
  intro m
  rw [MvPolynomial.coeff_homogeneousComponent]
  split
  · exact hP m
  · exact le_rfl

theorem sum {σ ι : Type*} {s : Finset ι}
    {P : ι → MvPolynomial σ ℝ} (hP : ∀ i ∈ s, HasNonnegCoeffs (P i)) :
    HasNonnegCoeffs (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (σ := σ))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add (hP i (Finset.mem_insert_self i s))
        (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

theorem prod {σ ι : Type*} {s : Finset ι}
    {P : ι → MvPolynomial σ ℝ} (hP : ∀ i ∈ s, HasNonnegCoeffs (P i)) :
    HasNonnegCoeffs (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (σ := σ))
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact mul (hP i (Finset.mem_insert_self i s))
        (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

end HasNonnegCoeffs

end MvPolynomial
