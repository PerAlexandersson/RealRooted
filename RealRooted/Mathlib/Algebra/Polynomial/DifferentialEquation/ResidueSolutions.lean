/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.TwoDiagonal
public import RealRooted.Mathlib.Algebra.Polynomial.Veronese
import Mathlib.Tactic

/-!
# Coefficient systems in residue classes

The recurrence with step `r` is the product of independent two-diagonal systems
on its residue classes. Source: unpublished proof notes, RealRooted issue #2345,
comment of 2026-11-01, equations (1) and (2).
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- Finitely supported coefficient solutions with a fixed positive step. -/
@[expose] def residueSolutions (a b : ℕ → K) (r : ℕ) : Submodule K K[X] where
  carrier := {p | ∀ k, a k * p.coeff (k + r) = b k * p.coeff k}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq k
    simp only [coeff_add]
    linear_combination hp k + hq k
  smul_mem' := by
    intro c p hp k
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    linear_combination c * hp k

/-- The coefficient system splits exactly into the existing Veronese sections. -/
theorem mem_residueSolutions_iff (a b : ℕ → K) {r : ℕ} (hr : 0 < r) (p : K[X]) :
    p ∈ residueSolutions a b r ↔ ∀ i : Fin r,
      p.veroneseSection r i ∈ twoDiagonalSolutions
        (fun k => a (i + r * k)) (fun k => b (i + r * k)) := by
  constructor
  · intro hp i k
    simpa only [coeff_veroneseSection hr, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc] using hp (i + r * k)
  · intro hp k
    have h := hp ⟨k % r, Nat.mod_lt k hr⟩ (k / r)
    simpa only [coeff_veroneseSection hr, Nat.mul_add, Nat.mul_one,
      ← Nat.add_assoc, Nat.mod_add_div] using h

/-- The full solution space is the product of the solution spaces in its residue classes. -/
@[expose] noncomputable def residueSolutionsEquiv (a b : ℕ → K) {r : ℕ} (hr : 0 < r) :
    residueSolutions a b r ≃ₗ[K] ∀ i : Fin r,
      twoDiagonalSolutions (fun k => a (i + r * k)) (fun k => b (i + r * k)) where
  toFun p i := ⟨(p : K[X]).veroneseSection r i,
    (mem_residueSolutions_iff a b hr p).mp p.property i⟩
  invFun v := ⟨veroneseRecompose r (fun i => (v i : K[X])),
    (mem_residueSolutions_iff a b hr _).mpr (by
      intro i
      rw [veroneseSection_veroneseRecompose hr]
      exact (v i).property)⟩
  left_inv p := by
    apply Subtype.ext
    exact veroneseRecompose_veroneseSection (A := K) hr (p : K[X])
  right_inv v := by
    funext i
    apply Subtype.ext
    exact veroneseSection_veroneseRecompose (A := K) hr (fun j => (v j : K[X])) i
  map_add' p q := by
    funext i
    apply Subtype.ext
    exact veroneseSection_add (A := K) r i (p : K[X]) (q : K[X])
  map_smul' c p := by
    funext i
    apply Subtype.ext
    change (c • (p : K[X])).veroneseSection r i = c • (p : K[X]).veroneseSection r i
    simpa only [smul_eq_C_mul] using veroneseSection_C_mul (A := K) r i c (p : K[X])

/-- Exact free coordinates in every residue class, for arbitrary finite
supersets of the diagonal zeros in those classes. -/
noncomputable def residueSolutionCoordinates (a b : ℕ → K) {r : ℕ} (hr : 0 < r)
    (E : Fin r → Finset ℕ) (hE : ∀ (i : Fin r) (k : ℕ), b (i + r * k) = 0 → k ∈ E i) :
    residueSolutions a b r ≃ₗ[K] ∀ i : Fin r,
      twoDiagonalDegrees (fun k => a (i + r * k)) (fun k => b (i + r * k)) (E i) → K :=
  (residueSolutionsEquiv a b hr).trans
    (LinearEquiv.piCongrRight fun i => twoDiagonalEquiv _ _ (E i) (hE i))

/-- The dimension is the sum of the admissible-degree counts over residue classes. -/
theorem finrank_residueSolutions (a b : ℕ → K) {r : ℕ} (hr : 0 < r)
    (E : Fin r → Finset ℕ) (hE : ∀ (i : Fin r) (k : ℕ), b (i + r * k) = 0 → k ∈ E i) :
    Module.finrank K (residueSolutions a b r) =
      ∑ i : Fin r,
        (twoDiagonalDegrees (fun k => a (i + r * k)) (fun k => b (i + r * k)) (E i)).card := by
  rw [(residueSolutionCoordinates a b hr E hE).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- A basis obtained by placing each canonical monic section solution in its
own residue class and setting all other sections to zero. -/
noncomputable def residueSolutionBasis (a b : ℕ → K) {r : ℕ} (hr : 0 < r)
    (E : Fin r → Finset ℕ) (hE : ∀ (i : Fin r) (k : ℕ), b (i + r * k) = 0 → k ∈ E i) :
    Module.Basis (Σ i : Fin r, twoDiagonalDegrees
      (fun k => a (i + r * k)) (fun k => b (i + r * k)) (E i)) K
      (residueSolutions a b r) :=
  (Pi.basis fun i => twoDiagonalBasis _ _ (E i) (hE i)).map
    (residueSolutionsEquiv a b hr).symm

/-- Every admissible section degree gives a monic solution supported in that
single residue class. This is also the explicit basis construction. -/
theorem exists_monic_residueSolution {a b : ℕ → K} {r : ℕ} (hr : 0 < r)
    (i : Fin r) (n : ℕ)
    (hn : TwoDiagonalDegree (fun k => a (i + r * k)) (fun k => b (i + r * k)) n) :
    ∃ p ∈ residueSolutions a b r, p.Monic ∧ p.natDegree = i + r * n ∧
      ∀ j : Fin r, j ≠ i → p.veroneseSection r j = 0 := by
  let q := twoDiagonalPolynomial (fun k => a (i + r * k)) (fun k => b (i + r * k)) n
  have hq : q.Monic := monic_twoDiagonalPolynomial _ _ _
  have hqe : (expand K r q).Monic := (monic_expand_iff hr).mpr hq
  refine ⟨X ^ (i : ℕ) * expand K r q, ?_, (monic_X_pow _).mul hqe, ?_, ?_⟩
  · apply (mem_residueSolutions_iff a b hr _).mpr
    intro j
    rw [veroneseSection_X_pow_mul_expand hr]
    split_ifs with hji
    · subst j
      exact twoDiagonalPolynomial_mem hn
    · exact (twoDiagonalSolutions _ _).zero_mem
  · rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hqe.ne_zero, natDegree_X_pow,
      natDegree_expand, natDegree_twoDiagonalPolynomial]
    ring
  · intro j hji
    rw [veroneseSection_X_pow_mul_expand hr, ite_eq_right hji]

/-- Possible nonzero degrees of the full step recurrence are exactly the
admissible degrees in the corresponding residue classes. -/
theorem exists_residueSolution_natDegree_iff (a b : ℕ → K) {r : ℕ} (hr : 0 < r) (d : ℕ) :
    (∃ p ∈ residueSolutions a b r, p ≠ 0 ∧ p.natDegree = d) ↔
      TwoDiagonalDegree (fun k => a (d % r + r * k))
        (fun k => b (d % r + r * k)) (d / r) := by
  constructor
  · rintro ⟨p, hp, hne, hd⟩
    let i : Fin r := ⟨d % r, Nat.mod_lt d hr⟩
    have hmem := (mem_residueSolutions_iff a b hr p).mp hp i
    have hcoeff : (p.veroneseSection r i).coeff (d / r) ≠ 0 := by
      rw [coeff_veroneseSection hr, Nat.mod_add_div, ← hd, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hne
    have hqne : p.veroneseSection r i ≠ 0 := by
      intro hz
      simp [hz] at hcoeff
    have hdeg : (p.veroneseSection r i).natDegree = d / r := by
      apply natDegree_eq_of_le_of_coeff_ne_zero _ hcoeff
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_veroneseSection hr]
      apply coeff_eq_zero_of_natDegree_lt
      have hmod := Nat.mod_add_div d r
      change p.natDegree < d % r + r * k
      rw [hd]
      nlinarith
    simpa only [hdeg] using twoDiagonalDegree_natDegree hmem hqne
  · intro hn
    obtain ⟨p, hp, hmonic, hd, _⟩ := exists_monic_residueSolution hr
      ⟨d % r, Nat.mod_lt d hr⟩ (d / r) hn
    exact ⟨p, hp, hmonic.ne_zero, hd.trans (Nat.mod_add_div d r)⟩

end Polynomial
