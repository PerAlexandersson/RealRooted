import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Complex.Basic

/-!
# Finite apolarity

This module records the finite binomial apolar pairing for univariate
polynomials.  The classical Grace apolarity theorem uses the specialization to
complex coefficients, but the algebraic pairing and its elementary API are
valid over any commutative ring.
-/

open Polynomial

noncomputable section

namespace Polynomial

/-- All roots of `p` lie in `s`. -/
def RootsIn {R : Type*} [Semiring R] (s : Set R) (p : R[X]) : Prop :=
  ∀ z : R, p.IsRoot z → z ∈ s

/-- The polynomial `p` has at least one root in `s`. -/
def HasRootIn {R : Type*} [Semiring R] (s : Set R) (p : R[X]) : Prop :=
  ∃ z : R, p.IsRoot z ∧ z ∈ s

@[simp] theorem rootsIn_univ {R : Type*} [Semiring R] (p : R[X]) :
    p.RootsIn Set.univ :=
  fun z _ => Set.mem_univ z

theorem RootsIn.mono {R : Type*} [Semiring R] {s t : Set R} {p : R[X]}
    (hst : s ⊆ t) (h : p.RootsIn s) :
    p.RootsIn t := by
  intro z hz
  exact hst (h z hz)

theorem HasRootIn.mono {R : Type*} [Semiring R] {s t : Set R} {p : R[X]}
    (hst : s ⊆ t) (h : p.HasRootIn s) :
    p.HasRootIn t := by
  rcases h with ⟨z, hzroot, hzs⟩
  exact ⟨z, hzroot, hst hzs⟩

theorem hasRootIn_of_isRoot {R : Type*} [Semiring R] {s : Set R} {p : R[X]} {z : R}
    (hzroot : p.IsRoot z) (hzs : z ∈ s) :
    p.HasRootIn s :=
  ⟨z, hzroot, hzs⟩

end Polynomial

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

theorem AreApolar.add_left {R : Type*} [CommRing R]
    {n : Nat} {f₁ f₂ g : R[X]}
    (h₁ : AreApolar n f₁ g) (h₂ : AreApolar n f₂ g) :
    AreApolar n (f₁ + f₂) g := by
  rw [AreApolar, apolarPairing_add_left, h₁, h₂, add_zero]

theorem AreApolar.add_right {R : Type*} [CommRing R]
    {n : Nat} {f g₁ g₂ : R[X]}
    (h₁ : AreApolar n f g₁) (h₂ : AreApolar n f g₂) :
    AreApolar n f (g₁ + g₂) := by
  rw [AreApolar, apolarPairing_add_right, h₁, h₂, add_zero]

theorem AreApolar.C_mul_left {R : Type*} [CommRing R]
    {n : Nat} {f g : R[X]} (a : R) (h : AreApolar n f g) :
    AreApolar n (C a * f) g := by
  rw [AreApolar, apolarPairing_C_mul_left, h, mul_zero]

theorem AreApolar.C_mul_right {R : Type*} [CommRing R]
    {n : Nat} {f g : R[X]} (a : R) (h : AreApolar n f g) :
    AreApolar n f (C a * g) := by
  rw [AreApolar, apolarPairing_C_mul_right, h, mul_zero]

private lemma neg_one_pow_sub_eq_mul {R : Type*} [CommRing R]
    {n k : Nat} (hk : k ≤ n) :
    (-1 : R) ^ (n - k) = (-1 : R) ^ n * (-1 : R) ^ k := by
  conv_rhs =>
    rw [← Nat.sub_add_cancel hk, pow_add]
  rw [mul_assoc]
  have hsq : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
    rw [← pow_add]
    have heven : Even (k + k) := ⟨k, rfl⟩
    simp [heven.neg_one_pow (α := R)]
  rw [hsq, mul_one]

/-- Swapping the two arguments in the apolar pairing introduces the usual
degree-`n` sign. -/
theorem apolarPairing_comm_sign {R : Type*} [CommRing R]
    (n : Nat) (f g : R[X]) :
    apolarPairing n g f = (-1 : R) ^ n * apolarPairing n f g := by
  rw [apolarPairing, apolarPairing]
  conv_lhs =>
    rw [← Finset.sum_range_reflect
      (fun k => (-1 : R) ^ k * (Nat.choose n k : R) * g.coeff k * f.coeff (n - k))
      (n + 1)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hsub : n - (n - k) = k := Nat.sub_sub_self hk_le
  rw [Nat.add_sub_cancel, hsub]
  rw [Nat.choose_symm hk_le]
  rw [neg_one_pow_sub_eq_mul (R := R) hk_le]
  ring_nf

theorem AreApolar.symm {R : Type*} [CommRing R]
    {n : Nat} {f g : R[X]} (h : AreApolar n f g) :
    AreApolar n g f := by
  rw [AreApolar, apolarPairing_comm_sign, h, mul_zero]

theorem areApolar_comm {R : Type*} [CommRing R]
    {n : Nat} {f g : R[X]} :
    AreApolar n f g ↔ AreApolar n g f :=
  ⟨AreApolar.symm, AreApolar.symm⟩

/-- Statement-level interface for Grace's apolarity theorem.

The predicate `IsGraceDomain` is intentionally a parameter: later work can
instantiate it with the chosen formal notion of circular domain, a half-plane
specialization, or whichever root-location class is sufficient for the
Hadamard/Schur--Szego route. -/
def GraceApolarityStatement (IsGraceDomain : Set ℂ → Prop) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃s : Set ℂ⦄ ⦃f g : ℂ[X]⦄,
    IsGraceDomain s →
    f.natDegree = n →
    g.natDegree = n →
    AreApolar n f g →
    f.RootsIn s →
    g.HasRootIn s

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
