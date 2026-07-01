import Mathlib.Algebra.Polynomial.Coeff

/-!
# Finite apolarity

This module records the finite binomial apolar pairing for univariate
polynomials.  The classical Grace apolarity theorem uses the specialization to
complex coefficients, but the algebraic pairing and its elementary API are
valid over any commutative ring.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The finite apolar pairing in degree `n`.

With the coefficient convention `f = ∑ a_k X^k` and `g = ∑ b_k X^k`, this is
`∑_{k=0}^n (-1)^k * choose n k * a_k * b_{n-k}`. -/
def apolarPairing {R : Type*} [CommRing R] (n : Nat) (f g : R[X]) : R :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (-1 : R) ^ k * (Nat.choose n k : R) * f.coeff k * g.coeff (n - k)

/-- Two polynomials are apolar in degree `n` if their finite apolar pairing
vanishes. -/
def AreApolar {R : Type*} [CommRing R] (n : Nat) (f g : R[X]) : Prop :=
  apolarPairing n f g = 0

@[simp] theorem apolarPairing_zero_left {R : Type*} [CommRing R]
    (n : Nat) (g : R[X]) :
    apolarPairing n 0 g = 0 := by
  simp [apolarPairing]

@[simp] theorem apolarPairing_zero_right {R : Type*} [CommRing R]
    (n : Nat) (f : R[X]) :
    apolarPairing n f 0 = 0 := by
  simp [apolarPairing]

@[simp] theorem areApolar_zero_left {R : Type*} [CommRing R]
    (n : Nat) (g : R[X]) :
    AreApolar n 0 g := by
  simp [AreApolar]

@[simp] theorem areApolar_zero_right {R : Type*} [CommRing R]
    (n : Nat) (f : R[X]) :
    AreApolar n f 0 := by
  simp [AreApolar]

theorem apolarPairing_add_left {R : Type*} [CommRing R]
    (n : Nat) (f₁ f₂ g : R[X]) :
    apolarPairing n (f₁ + f₂) g = apolarPairing n f₁ g + apolarPairing n f₂ g := by
  rw [apolarPairing, apolarPairing, apolarPairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Polynomial.coeff_add]
  ring_nf

theorem apolarPairing_add_right {R : Type*} [CommRing R]
    (n : Nat) (f g₁ g₂ : R[X]) :
    apolarPairing n f (g₁ + g₂) = apolarPairing n f g₁ + apolarPairing n f g₂ := by
  rw [apolarPairing, apolarPairing, apolarPairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Polynomial.coeff_add]
  ring_nf

theorem apolarPairing_C_mul_left {R : Type*} [CommRing R]
    (n : Nat) (a : R) (f g : R[X]) :
    apolarPairing n (C a * f) g = a * apolarPairing n f g := by
  rw [apolarPairing, apolarPairing, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Polynomial.coeff_C_mul]
  ring_nf

theorem apolarPairing_C_mul_right {R : Type*} [CommRing R]
    (n : Nat) (f g : R[X]) (a : R) :
    apolarPairing n f (C a * g) = a * apolarPairing n f g := by
  rw [apolarPairing, apolarPairing, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Polynomial.coeff_C_mul]
  ring_nf

theorem apolarPairing_monomial_left {R : Type*} [CommRing R]
    (n i : Nat) (a : R) (g : R[X]) :
    apolarPairing n (monomial i a) g =
      if i ≤ n then (-1 : R) ^ i * (Nat.choose n i : R) * a * g.coeff (n - i) else 0 := by
  classical
  by_cases hi : i ≤ n
  · rw [if_pos hi, apolarPairing]
    have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    rw [Finset.sum_eq_single_of_mem i hmem]
    · simp
    · intro k _ hki
      have hik : i ≠ k := fun h => hki h.symm
      simp [coeff_monomial, hik]
  · rw [if_neg hi, apolarPairing]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hki : k ≠ i := by
      intro h
      subst k
      exact hi (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have hik : i ≠ k := fun h => hki h.symm
    simp [coeff_monomial, hik]

theorem apolarPairing_monomial_right {R : Type*} [CommRing R]
    (n j : Nat) (f : R[X]) (b : R) :
    apolarPairing n f (monomial j b) =
      if j ≤ n then
        (-1 : R) ^ (n - j) * (Nat.choose n (n - j) : R) * f.coeff (n - j) * b
      else 0 := by
  classical
  by_cases hj : j ≤ n
  · rw [if_pos hj, apolarPairing]
    have hmem : n - j ∈ Finset.range (n + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n j))
    rw [Finset.sum_eq_single_of_mem (n - j) hmem]
    · have hsub : n - (n - j) = j := Nat.sub_sub_self hj
      simp [hsub]
    · intro k hk hk_ne
      have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hneq : j ≠ n - k := by
        intro h
        apply hk_ne
        lia
      simp [coeff_monomial, hneq]
  · rw [if_neg hj, apolarPairing]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hneq : j ≠ n - k := by
      intro h
      have : j ≤ n := by lia
      exact hj this
    simp [coeff_monomial, hneq]

end RealRooted
