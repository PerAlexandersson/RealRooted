/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degree bounds for univariate multivariate-polynomial equivalences

This file contains Mathlib-shaped compatibility lemmas for
`MvPolynomial.uniqueAlgEquiv`, `MvPolynomial.optionEquivLeft` and `MvPolynomial.sumAlgEquiv`.
-/

public section

namespace MvPolynomial

/-- Viewing `none` as the univariate variable turns its partial derivative
into the ordinary polynomial derivative. -/
theorem optionEquivLeft_pderiv_none
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial (Option σ) R) :
    optionEquivLeft R σ (pderiv none p) =
      (optionEquivLeft R σ p).derivative := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      cases i <;> simp [hp, Polynomial.derivative_mul] <;> ac_rfl

/-- Renaming both the distinguished-variable polynomial and its coefficient
variables agrees with mapping the univariate polynomial's coefficients. -/
theorem optionEquivLeft_rename_option_map
    {R σ τ : Type*} [CommSemiring R] (f : σ → τ)
    (p : MvPolynomial (Option σ) R) :
    optionEquivLeft R τ (rename (Option.map f) p) =
      Polynomial.map (rename f).toRingHom (optionEquivLeft R σ p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      cases i <;> simp [hp]

/-- Mapping scalars commutes with taking a coefficient in the distinguished
variable. -/
theorem map_optionEquivLeft_coeff
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial (Option σ) R) (k : ℕ) :
    map f ((optionEquivLeft R σ p).coeff k) =
      (optionEquivLeft S σ (map f p)).coeff k := by
  ext m
  simp only [coeff_map, optionEquivLeft_coeff_coeff]

/-- Multiplying by the distinguished variable plus one coefficient variable
shifts a known scalar leading coefficient by one degree. -/
theorem optionEquivLeft_coeff_succ_mul_X_none_add_new
    {R σ : Type*} [CommSemiring R]
    (p : MvPolynomial (Option σ) R) (d : ℕ) (c : R)
    (hdeg : p.degreeOf none ≤ d)
    (htop : (optionEquivLeft R σ p).coeff d = C c) :
    (optionEquivLeft R (Option σ)
      ((X none + X (some none)) * rename (Option.map some) p)).coeff
        (d + 1) = C c := by
  have hzero : (optionEquivLeft R σ p).coeff (d + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [natDegree_optionEquivLeft]
    lia
  rw [map_mul, map_add (optionEquivLeft R (Option σ)), optionEquivLeft_X_none,
    optionEquivLeft_X_some, optionEquivLeft_rename_option_map, add_mul,
    Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_map, htop]
  simp [hzero]

/-- The degree in the unique variable after converting a univariate polynomial
to an `MvPolynomial` is its natural degree. -/
theorem degreeOf_uniqueAlgEquiv_symm
    {σ R : Type*} [Unique σ] [CommSemiring R] (p : Polynomial R) :
    degreeOf default ((MvPolynomial.uniqueAlgEquiv R σ).symm p) =
      p.natDegree := by
  apply le_antisymm
  · rw [degreeOf_le_iff]
    intro d hd
    have hcoeff : p.coeff (d default) ≠ 0 := by
      rw [← MvPolynomial.coeff_uniqueAlgEquiv_symm R p d]
      exact MvPolynomial.mem_support_iff.mp hd
    exact Polynomial.le_natDegree_of_ne_zero hcoeff
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have hnotmem :
        Finsupp.single default n ∉
          ((MvPolynomial.uniqueAlgEquiv R σ).symm p).support := by
      apply MvPolynomial.notMem_support_of_degreeOf_lt default
      simpa using hn
    have hzero := MvPolynomial.notMem_support_iff.mp hnotmem
    rw [MvPolynomial.coeff_uniqueAlgEquiv_symm R p
      (Finsupp.single default n)] at hzero
    simpa using hzero

/-- Passing from a uniquely indexed multivariate polynomial to a univariate
polynomial does not increase total degree. -/
theorem natDegree_uniqueAlgEquiv_le_totalDegree
    {σ R : Type*} [Unique σ] [CommSemiring R] (p : MvPolynomial σ R) :
    (MvPolynomial.uniqueAlgEquiv R σ p).natDegree ≤ p.totalDegree := by
  calc
    (MvPolynomial.uniqueAlgEquiv R σ p).natDegree =
        degreeOf default
          ((MvPolynomial.uniqueAlgEquiv R σ).symm
            (MvPolynomial.uniqueAlgEquiv R σ p)) :=
      (degreeOf_uniqueAlgEquiv_symm
        (MvPolynomial.uniqueAlgEquiv R σ p)).symm
    _ = degreeOf default p := by rw [AlgEquiv.symm_apply_apply]
    _ ≤ p.totalDegree := degreeOf_le_totalDegree p default

/-- `sumAlgEquiv` sends a monomial in the disjoint union of variable types to the corresponding
iterated monomial. -/
theorem sumAlgEquiv_monomial
    {S₁ S₂ R : Type*} [CommSemiring R]
    (a : S₁ →₀ ℕ) (b : S₂ →₀ ℕ) (r : R) :
    MvPolynomial.sumAlgEquiv R S₁ S₂
        (MvPolynomial.monomial (a.sumElim b) r) =
      MvPolynomial.monomial a (MvPolynomial.monomial b r) := by
  classical
  rw [MvPolynomial.monomial_eq, MvPolynomial.monomial_eq,
    MvPolynomial.monomial_eq, Finsupp.prod_sumElim]
  simp only [map_mul, MvPolynomial.sumAlgEquiv_C_inl]
  simp [Finsupp.prod]
  simp only [← map_pow, ← map_prod]
  simp only [MvPolynomial.prod_X_pow_eq_monomial]
  ring

/-- Extracting an outer and then an inner coefficient through `sumAlgEquiv`
is the same as extracting the combined exponent from the original polynomial. -/
theorem coeff_coeff_sumAlgEquiv
    {S₁ S₂ R : Type*} [CommSemiring R]
    (P : MvPolynomial (S₁ ⊕ S₂) R)
    (a : S₁ →₀ ℕ) (b : S₂ →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv R S₁ S₂ P).coeff a).coeff b =
      P.coeff (a.sumElim b) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | monomial d r =>
      let d₁ : S₁ →₀ ℕ :=
        Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn
      let d₂ : S₂ →₀ ℕ :=
        Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn
      have hd : d₁.sumElim d₂ = d :=
        Finsupp.comapDomain_sumElim_comapDomain d
      rw [← hd, sumAlgEquiv_monomial]
      have hsum : d₁.sumElim d₂ = a.sumElim b ↔ d₁ = a ∧ d₂ = b := by
        constructor
        · exact fun h => ⟨Finsupp.ext fun i => DFunLike.congr_fun h (Sum.inl i),
            Finsupp.ext fun i => DFunLike.congr_fun h (Sum.inr i)⟩
        · rintro ⟨rfl, rfl⟩
          rfl
      by_cases hda : d₁ = a
      · have hright : a.sumElim d₂ = a.sumElim b ↔ d₂ = b :=
          ⟨fun h => Finsupp.ext fun i => DFunLike.congr_fun h (Sum.inr i),
            congrArg (Finsupp.sumElim a)⟩
        simp [MvPolynomial.coeff_monomial, hda, hright]
      · simp [MvPolynomial.coeff_monomial, hsum, hda]

end MvPolynomial
