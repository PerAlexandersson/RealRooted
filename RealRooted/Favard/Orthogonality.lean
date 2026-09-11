/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Favard.Recurrence

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Tactic.Linarith

/-!
# Algebraic Favard orthogonality

A monic Favard recurrence determines a normalized linear functional on
polynomials.  Its product pairing makes the recurrence family orthogonal, with
squared norms given by products of the subdiagonal coefficients.  This is the
algebraic core of Favard's theorem; analytic representing measures and their
supports belong in family-specific child modules.
-/

@[expose] public section

open Module Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The squared norm prescribed by the subdiagonal coefficients of a monic
Favard recurrence. -/
def favardNormSq {R : Type*} [CommMonoid R] (β : Nat → R) (n : Nat) : R :=
  ∏ k ∈ Finset.range n, β (k + 1)

@[simp] theorem favardNormSq_zero {R : Type*} [CommMonoid R] (β : Nat → R) :
    favardNormSq β 0 = 1 := by
  simp [favardNormSq]

@[simp] theorem favardNormSq_succ {R : Type*} [CommMonoid R]
    (β : Nat → R) (n : Nat) :
    favardNormSq β (n + 1) = favardNormSq β n * β (n + 1) := by
  unfold favardNormSq
  rw [Finset.prod_range_succ]

/-- The Favard squared norm for the natural-number subdiagonal is a
factorial. -/
@[simp] theorem favardNormSq_natCast {R : Type*} [CommSemiring R] (n : Nat) :
    favardNormSq (fun k : Nat ↦ (k : R)) n = (n.factorial : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [favardNormSq_succ, ih, Nat.factorial_succ, mul_comm]

/-- A product of nonzero Favard subdiagonal coefficients is nonzero. -/
theorem favardNormSq_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {β : Nat → R} (hβ : ∀ n, β (n + 1) ≠ 0) (n : Nat) :
    favardNormSq β n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [favardNormSq_succ, ih, hβ n]

/-- Positive Favard subdiagonal coefficients give positive prescribed
squared norms. -/
theorem favardNormSq_pos {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {β : Nat → R}
    (hβ : ∀ n, 0 < β (n + 1)) (n : Nat) :
    0 < favardNormSq β n := by
  induction n with
  | zero => simp
  | succ n ih => rw [favardNormSq_succ]; exact mul_pos ih (hβ n)

namespace SatisfiesFavardRecurrence

variable {R : Type*} [CommRing R] [IsDomain R]
variable {P : Nat → R[X]} {α β : Nat → R}

/-- The normalized Favard functional: extraction of the degree-zero
coordinate in the recurrence basis. -/
def functional (hrec : SatisfiesFavardRecurrence P α β) : R[X] →ₗ[R] R :=
  hrec.basis.coord 0

@[simp] theorem functional_apply_basis
    (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    hrec.functional (P n) = if n = 0 then 1 else 0 := by
  rw [← hrec.basis_apply n]
  simp only [functional, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

@[simp] theorem functional_one
    (hrec : SatisfiesFavardRecurrence P α β) :
    hrec.functional 1 = 1 := by
  rw [← hrec.1]
  simp

/-- The symmetric product pairing induced by the normalized Favard
functional. -/
def pairing (hrec : SatisfiesFavardRecurrence P α β) :
    LinearMap.BilinForm R R[X] :=
  (LinearMap.mul R R[X]).compr₂ hrec.functional

@[simp] theorem pairing_apply
    (hrec : SatisfiesFavardRecurrence P α β) (p q : R[X]) :
    hrec.pairing p q = hrec.functional (p * q) :=
  rfl

/-- The diagonal form prescribed on the Favard basis. -/
private def diagonalForm (hrec : SatisfiesFavardRecurrence P α β) :
    LinearMap.BilinForm R R[X] :=
  hrec.basis.constr R fun i ↦
    hrec.basis.constr R fun j ↦
      if i = j then favardNormSq β i else 0

@[simp] private theorem diagonalForm_apply_basis
    (hrec : SatisfiesFavardRecurrence P α β) (i j : Nat) :
    diagonalForm hrec (P i) (P j) =
      if i = j then favardNormSq β i else 0 := by
  rw [← hrec.basis_apply i, ← hrec.basis_apply j]
  simp only [diagonalForm, Basis.constr_basis]

/-- Multiplication by `X` is self-adjoint for the diagonal Favard form. -/
private theorem diagonalForm_isAdjointPair_X
    (hrec : SatisfiesFavardRecurrence P α β) :
    LinearMap.IsAdjointPair (diagonalForm hrec) (diagonalForm hrec)
      (LinearMap.mulLeft R X) (LinearMap.mulLeft R X) := by
  classical
  rw [LinearMap.isAdjointPair_iff_comp_eq_compl₂]
  apply LinearMap.ext_basis hrec.basis hrec.basis
  intro i j
  simp only [LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.mulLeft_apply, hrec.basis_apply]
  cases i with
  | zero =>
      cases j with
      | zero =>
          simp [hrec.X_mul_zero, diagonalForm_apply_basis]
      | succ j =>
          rw [hrec.X_mul_zero, hrec.X_mul_succ j]
          by_cases hj : j = 0
          · subst j
            simp [diagonalForm_apply_basis,
              favardNormSq_succ, mul_comm]
          · have h0j : 0 ≠ j := Ne.symm hj
            simp [diagonalForm_apply_basis, hj, h0j]
  | succ i =>
      cases j with
      | zero =>
          rw [hrec.X_mul_succ i, hrec.X_mul_zero]
          by_cases hi : i = 0
          · subst i
            simp [diagonalForm_apply_basis,
              favardNormSq_succ, mul_comm]
          · simp [diagonalForm_apply_basis, hi]
      | succ j =>
          rw [hrec.X_mul_succ i, hrec.X_mul_succ j]
          by_cases hij : i = j
          · subst j
            simp [diagonalForm_apply_basis]
          · by_cases hij1 : i + 1 = j
            · subst j
              have hne : i ≠ i + 1 + 1 := by lia
              simp [diagonalForm_apply_basis,
                favardNormSq_succ, mul_comm, hne]
            · by_cases hji1 : j + 1 = i
              · subst i
                have hne : j + 1 + 1 ≠ j := by lia
                simp [diagonalForm_apply_basis,
                  favardNormSq_succ, mul_comm, hne]
              · have h1 : i + 2 ≠ j + 1 := by lia
                have h3 : i ≠ j + 1 := by lia
                have h5 : i + 1 ≠ j := by lia
                simp [diagonalForm_apply_basis, hij, h1, h3, h5]

/-- The pointwise self-adjointness identity for multiplication by `X`. -/
private theorem diagonalForm_X_mul
    (hrec : SatisfiesFavardRecurrence P α β) (p q : R[X]) :
    diagonalForm hrec (X * p) q = diagonalForm hrec p (X * q) :=
  diagonalForm_isAdjointPair_X hrec p q

/-- Multiplication by any polynomial is self-adjoint for the diagonal Favard
form. -/
private theorem diagonalForm_mul
    (hrec : SatisfiesFavardRecurrence P α β) (r p q : R[X]) :
    diagonalForm hrec (r * p) q = diagonalForm hrec p (r * q) := by
  have hpow : ∀ (n : Nat) (p q : R[X]),
      diagonalForm hrec (X ^ n * p) q =
        diagonalForm hrec p (X ^ n * q) := by
    intro n
    induction n with
    | zero => intro p q; simp
    | succ n ih =>
        intro p q
        calc
          diagonalForm hrec (X ^ (n + 1) * p) q =
              diagonalForm hrec (X * (X ^ n * p)) q := by
                rw [pow_succ', mul_assoc]
          _ = diagonalForm hrec (X ^ n * p) (X * q) :=
            diagonalForm_X_mul hrec _ _
          _ = diagonalForm hrec p (X ^ n * (X * q)) := ih _ _
          _ = diagonalForm hrec p (X ^ (n + 1) * q) := by
                rw [pow_succ, mul_assoc]
  induction r using Polynomial.induction_on' with
  | add r s hr hs =>
      simp only [add_mul, map_add, LinearMap.add_apply]
      rw [hr, hs]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        ← Polynomial.smul_eq_C_mul]
      rw [smul_mul_assoc, smul_mul_assoc, LinearMap.map_smul₂, map_smul,
        hpow]

/-- The normalized functional is the degree-zero row of the diagonal form. -/
private theorem functional_eq_diagonalForm_zero
    (hrec : SatisfiesFavardRecurrence P α β) :
    hrec.functional = diagonalForm hrec (P 0) := by
  apply hrec.basis.ext
  intro n
  rw [hrec.basis_apply]
  simp [functional_apply_basis, diagonalForm_apply_basis, favardNormSq, eq_comm]

/-- The product pairing induced by the normalized functional is precisely the
diagonal Favard form. -/
private theorem pairing_eq_diagonalForm
    (hrec : SatisfiesFavardRecurrence P α β) :
    hrec.pairing = diagonalForm hrec := by
  apply LinearMap.ext_basis hrec.basis hrec.basis
  intro i j
  rw [hrec.basis_apply, hrec.basis_apply, pairing_apply,
    LinearMap.congr_fun (functional_eq_diagonalForm_zero hrec)]
  have hs := diagonalForm_mul hrec (P i) (P 0) (P j)
  simpa [hrec.1] using hs.symm

/-- Favard basis elements are orthogonal, with squared norm equal to the
product of the preceding subdiagonal coefficients. -/
@[simp] theorem pairing_apply_basis
    (hrec : SatisfiesFavardRecurrence P α β) (i j : Nat) :
    hrec.pairing (P i) (P j) =
      if i = j then favardNormSq β i else 0 := by
  rw [pairing_eq_diagonalForm hrec, diagonalForm_apply_basis]

/-- A Favard recurrence is an orthogonal family for its normalized product
pairing. -/
theorem pairing_iIsOrtho
    (hrec : SatisfiesFavardRecurrence P α β) :
    hrec.pairing.iIsOrtho P := by
  intro i j hij
  change hrec.pairing (P i) (P j) = 0
  rw [pairing_apply_basis]
  simp [hij]

/-- The normalized Favard product pairing is symmetric. -/
theorem pairing_isSymm
    (hrec : SatisfiesFavardRecurrence P α β) :
    hrec.pairing.IsSymm :=
  ⟨fun p q ↦ by simp only [pairing_apply]; rw [mul_comm]⟩

/-- Nonzero subdiagonal coefficients make the Favard pairing
nondegenerate. -/
theorem pairing_nondegenerate
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, β (n + 1) ≠ 0) :
    hrec.pairing.Nondegenerate := by
  have hO : hrec.pairing.iIsOrtho hrec.basis := by
    intro i j hij
    simp only [Function.onFun, LinearMap.isOrtho_def, hrec.basis_apply]
    rw [pairing_apply_basis]
    simp [hij]
  apply (hO.nondegenerate_iff_not_isOrtho_basis_self
    hrec.pairing hrec.basis).2
  intro i
  simpa only [LinearMap.BilinForm.isOrtho_def, hrec.basis_apply,
    pairing_apply_basis, if_pos] using favardNormSq_ne_zero hβ i

/-- A linear functional that vanishes on all positive-degree members of a
Favard basis is uniquely determined by its value at `1`. -/
theorem linearMap_eq_smul_functional
    (hrec : SatisfiesFavardRecurrence P α β) (L : R[X] →ₗ[R] R)
    (hvanish : ∀ n, n ≠ 0 → L (P n) = 0) :
    L = L 1 • hrec.functional := by
  apply hrec.basis.ext
  intro n
  rw [hrec.basis_apply]
  cases n with
  | zero => simp [hrec.1]
  | succ n => simp [hvanish]

/-- A linear functional for which distinct Favard basis elements are
orthogonal is the normalized Favard functional, up to its total mass. -/
theorem linearMap_eq_smul_functional_of_orthogonal
    (hrec : SatisfiesFavardRecurrence P α β) (L : R[X] →ₗ[R] R)
    (horth : ∀ i j, i ≠ j → L (P i * P j) = 0) :
    L = L 1 • hrec.functional := by
  apply hrec.linearMap_eq_smul_functional
  intro n hn
  simpa [hrec.1] using horth 0 n (Ne.symm hn)

end SatisfiesFavardRecurrence

namespace SatisfiesFavardRecurrence

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {P : Nat → R[X]} {α β : Nat → R}

/-- Positive subdiagonal coefficients make the diagonal Favard form positive
definite. -/
private theorem diagonalForm_posDef
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, 0 < β (n + 1)) :
    (diagonalForm hrec).toQuadraticMap.PosDef := by
  intro p hp
  rw [LinearMap.BilinMap.toQuadraticMap_apply,
    ← LinearMap.sum_repr_mul_repr_mul hrec.basis hrec.basis p p]
  have hrepr : hrec.basis.repr p ≠ 0 :=
    hrec.basis.repr.map_ne_zero_iff.mpr hp
  refine Finsupp.sum_pos' ?_ ?_
  · intro i hi
    apply Finsupp.sum_nonneg
    intro j hj
    by_cases hij : i = j
    · subst j
      simp only [hrec.basis_apply, diagonalForm_apply_basis, if_pos, smul_eq_mul]
      rw [← mul_assoc]
      exact mul_nonneg (mul_self_nonneg _) (favardNormSq_pos hβ i).le
    · simp [hrec.basis_apply, diagonalForm_apply_basis, hij]
  have hex : ∃ i, hrec.basis.repr p i ≠ 0 := by
    by_contra h
    apply hrepr
    ext i
    simp only [Finsupp.zero_apply]
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hxi⟩ := hex
  have hi : i ∈ (hrec.basis.repr p).support :=
    Finsupp.mem_support_iff.mpr hxi
  refine ⟨i, hi, Finsupp.sum_pos' ?_ ⟨i, hi, ?_⟩⟩
  · intro j hj
    by_cases hij : i = j
    · subst j
      simp only [hrec.basis_apply, diagonalForm_apply_basis, if_pos, smul_eq_mul]
      rw [← mul_assoc]
      exact mul_nonneg (mul_self_nonneg _) (favardNormSq_pos hβ i).le
    · simp [hrec.basis_apply, diagonalForm_apply_basis, hij]
  · simp only [hrec.basis_apply, diagonalForm_apply_basis, if_pos, smul_eq_mul]
    rw [← mul_assoc]
    exact mul_pos (mul_self_pos.mpr hxi) (favardNormSq_pos hβ i)

/-- Positive subdiagonal coefficients make the normalized Favard product
pairing positive definite. -/
theorem pairing_posDef
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, 0 < β (n + 1)) :
    hrec.pairing.toQuadraticMap.PosDef := by
  rw [pairing_eq_diagonalForm hrec]
  exact diagonalForm_posDef hrec hβ

/-- The normalized Favard functional is strictly positive on every nonzero
polynomial square. -/
theorem functional_mul_self_pos
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, 0 < β (n + 1)) {p : R[X]} (hp : p ≠ 0) :
    0 < hrec.functional (p * p) := by
  simpa only [← pairing_apply, LinearMap.BilinMap.toQuadraticMap_apply] using
    hrec.pairing_posDef hβ p hp

/-- The normalized Favard functional is nonnegative on every polynomial
square. -/
theorem functional_mul_self_nonneg
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, 0 < β (n + 1)) (p : R[X]) :
    0 ≤ hrec.functional (p * p) := by
  simpa only [← pairing_apply, LinearMap.BilinMap.toQuadraticMap_apply] using
    (hrec.pairing_posDef hβ).nonneg p

/-- Positive Favard subdiagonal coefficients make the normalized functional
nonnegative on every polynomial sum of squares. -/
theorem functional_nonneg_of_isSumSq
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, 0 < β (n + 1)) {p : R[X]} (hp : IsSumSq p) :
    0 ≤ hrec.functional p := by
  induction hp with
  | zero => simp
  | sq_add q _ ih =>
      simpa using add_nonneg (hrec.functional_mul_self_nonneg hβ q) ih

end SatisfiesFavardRecurrence

end RealRooted
