module

import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Wronskian
public import RealRooted.Mathlib.RingTheory.Polynomial.Wronskian

/-!
# Cauchy--Binet expansion of the Wronskian of two linear combinations

For a family `h` of polynomials and real coefficient vectors `a`, `b`, the Wronskian of
`∑ a_k h_k` and `∑ b_k h_k` is `∑_{k < ℓ} (a_k b_ℓ - a_ℓ b_k) W(h_k, h_ℓ)`
(`RealRooted.le_eval_wronskian_sum_sum`). In particular, if every term of the sum is nonnegative at
a point `x`, the Wronskian at `x` dominates each single term
(`RealRooted.le_eval_wronskian_sum_sum`).
This is the `2 × 2` Cauchy--Binet formula for `W((R h)_i, (R h)_j)` with a constant matrix `R`.
-/

public section

open Polynomial

noncomputable section

namespace Polynomial

section Sums

variable {R : Type*} [CommRing R]

lemma wronskian_sum_left {ι : Type*} (s : Finset ι) (f : ι → R[X]) (g : R[X]) :
    wronskian (∑ i ∈ s, f i) g = ∑ i ∈ s, wronskian (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wronskian_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wronskian_add_left, ih]

lemma wronskian_sum_right {ι : Type*} (s : Finset ι) (f : R[X]) (g : ι → R[X]) :
    wronskian f (∑ i ∈ s, g i) = ∑ i ∈ s, wronskian f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wronskian_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wronskian_add_right, ih]

end Sums

end Polynomial

namespace RealRooted

/-- A double sum over `Fin m × Fin m` splits along the diagonal. -/
private lemma sum_sum_eq_sum_sum_lt {m : ℕ} (F : Fin m → Fin m → ℝ) :
    ∑ k, ∑ ℓ, F k ℓ =
      ∑ k, ∑ ℓ, (if k < ℓ then F k ℓ + F ℓ k else 0) + ∑ k, F k k := by
  have hpt : ∀ k ℓ, F k ℓ = (if k < ℓ then F k ℓ else 0) + (if ℓ < k then F k ℓ else 0) +
      (if k = ℓ then F k ℓ else 0) := fun k ℓ => by
    rcases lt_trichotomy k ℓ with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have h1 : ∑ k, ∑ ℓ, F k ℓ = ∑ k, ∑ ℓ, (if k < ℓ then F k ℓ else 0) +
      ∑ k, ∑ ℓ, (if ℓ < k then F k ℓ else 0) + ∑ k, ∑ ℓ, (if k = ℓ then F k ℓ else 0) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ℓ _ => hpt k ℓ
  have h2 : ∑ k, ∑ ℓ, (if ℓ < k then F k ℓ else 0) = ∑ k, ∑ ℓ, (if k < ℓ then F ℓ k else 0) :=
    Finset.sum_comm
  rw [h1, h2]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.sum_add_distrib,
    ite_add_ite, add_zero]

/-- **Cauchy–Binet for the Wronskian.** For two linear combinations of a family `h` with real
coefficients `a`, `b`, the value of their Wronskian at `x` is at least any single `2 × 2`-minor term
`(a_k b_ℓ - a_ℓ b_k) W(h_k, h_ℓ)(x)`, provided all such terms (`k < ℓ`) are nonnegative. -/
theorem le_eval_wronskian_sum_sum {m : ℕ} (a b : Fin m → ℝ) (h : Fin m → ℝ[X]) (x : ℝ)
    (hnn : ∀ k ℓ, k < ℓ → 0 ≤ (a k * b ℓ - a ℓ * b k) * (wronskian (h k) (h ℓ)).eval x)
    {k₀ ℓ₀ : Fin m} (hk : k₀ < ℓ₀) :
    (a k₀ * b ℓ₀ - a ℓ₀ * b k₀) * (wronskian (h k₀) (h ℓ₀)).eval x ≤
      (wronskian (∑ k, C (a k) * h k) (∑ k, C (b k) * h k)).eval x := by
  have hW : (wronskian (∑ k, C (a k) * h k) (∑ k, C (b k) * h k)).eval x =
      ∑ k, ∑ ℓ, a k * b ℓ * (wronskian (h k) (h ℓ)).eval x := by
    rw [wronskian_sum_left, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wronskian_sum_right, eval_finsetSum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [wronskian_C_mul_left, wronskian_C_mul_right, ← mul_assoc, ← C_mul]
    simp [eval_mul]
  rw [hW, sum_sum_eq_sum_sum_lt]
  have hdiag : ∑ k, a k * b k * (wronskian (h k) (h k)).eval x = 0 := by
    simp [wronskian_self_eq_zero]
  have hterm : ∀ k ℓ, (if k < ℓ then a k * b ℓ * (wronskian (h k) (h ℓ)).eval x +
      a ℓ * b k * (wronskian (h ℓ) (h k)).eval x else 0) =
        if k < ℓ then (a k * b ℓ - a ℓ * b k) * (wronskian (h k) (h ℓ)).eval x else 0 := by
    intro k ℓ
    split_ifs
    · rw [← wronskian_neg_eq (h k) (h ℓ), eval_neg]
      ring
    · rfl
  simp only [hdiag, add_zero, hterm]
  have hnn' : ∀ k ℓ, 0 ≤ (if k < ℓ then (a k * b ℓ - a ℓ * b k) *
      (wronskian (h k) (h ℓ)).eval x else 0) := fun k ℓ => by
    split_ifs with hlt
    · exact hnn k ℓ hlt
    · exact le_rfl
  calc _ = (if k₀ < ℓ₀ then (a k₀ * b ℓ₀ - a ℓ₀ * b k₀) * (wronskian (h k₀) (h ℓ₀)).eval x
        else 0) := by simp [hk]
    _ ≤ ∑ ℓ, (if k₀ < ℓ then (a k₀ * b ℓ - a ℓ * b k₀) * (wronskian (h k₀) (h ℓ)).eval x
        else 0) := Finset.single_le_sum (f := fun ℓ => if k₀ < ℓ then (a k₀ * b ℓ - a ℓ * b k₀) *
          (wronskian (h k₀) (h ℓ)).eval x else 0) (fun ℓ _ => hnn' k₀ ℓ) (Finset.mem_univ ℓ₀)
    _ ≤ _ := Finset.single_le_sum (f := fun k => ∑ ℓ, (if k < ℓ then
          (a k * b ℓ - a ℓ * b k) * (wronskian (h k) (h ℓ)).eval x else 0))
        (fun k _ => Finset.sum_nonneg fun ℓ _ => hnn' k ℓ) (Finset.mem_univ k₀)

end RealRooted

end
