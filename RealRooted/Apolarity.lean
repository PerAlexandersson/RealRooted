import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

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

theorem apolarPairing_neg_left {R : Type*} [CommRing R]
    (n : Nat) (f g : R[X]) :
    apolarPairing n (-f) g = -apolarPairing n f g := by
  simpa using apolarPairing_C_mul_left (n := n) (-1) f g

theorem apolarPairing_neg_right {R : Type*} [CommRing R]
    (n : Nat) (f g : R[X]) :
    apolarPairing n f (-g) = -apolarPairing n f g := by
  simpa using apolarPairing_C_mul_right (n := n) f g (-1)

theorem apolarPairing_sub_left {R : Type*} [CommRing R]
    (n : Nat) (f₁ f₂ g : R[X]) :
    apolarPairing n (f₁ - f₂) g =
      apolarPairing n f₁ g - apolarPairing n f₂ g := by
  rw [sub_eq_add_neg, apolarPairing_add_left, apolarPairing_neg_left, sub_eq_add_neg]

theorem apolarPairing_sub_right {R : Type*} [CommRing R]
    (n : Nat) (f g₁ g₂ : R[X]) :
    apolarPairing n f (g₁ - g₂) =
      apolarPairing n f g₁ - apolarPairing n f g₂ := by
  rw [sub_eq_add_neg, apolarPairing_add_right, apolarPairing_neg_right, sub_eq_add_neg]

theorem apolarPairing_sum_left {R : Type*} [CommRing R]
    {ι : Type*} (n : Nat) (s : Finset ι) (f : ι → R[X]) (g : R[X]) :
    apolarPairing n (Finset.sum s f) g =
      Finset.sum s fun i => apolarPairing n (f i) g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    simp [ha, apolarPairing_add_left, ih]

theorem apolarPairing_sum_right {R : Type*} [CommRing R]
    {ι : Type*} (n : Nat) (f : R[X]) (s : Finset ι) (g : ι → R[X]) :
    apolarPairing n f (Finset.sum s g) =
      Finset.sum s fun i => apolarPairing n f (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    simp [ha, apolarPairing_add_right, ih]

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

theorem AreApolar.neg_left {R : Type*} [CommRing R]
    {n : Nat} {f g : R[X]} (h : AreApolar n f g) :
    AreApolar n (-f) g := by
  rw [AreApolar, apolarPairing_neg_left, h, neg_zero]

theorem AreApolar.neg_right {R : Type*} [CommRing R]
    {n : Nat} {f g : R[X]} (h : AreApolar n f g) :
    AreApolar n f (-g) := by
  rw [AreApolar, apolarPairing_neg_right, h, neg_zero]

theorem AreApolar.sub_left {R : Type*} [CommRing R]
    {n : Nat} {f₁ f₂ g : R[X]}
    (h₁ : AreApolar n f₁ g) (h₂ : AreApolar n f₂ g) :
    AreApolar n (f₁ - f₂) g := by
  rw [AreApolar, apolarPairing_sub_left, h₁, h₂, sub_self]

theorem AreApolar.sub_right {R : Type*} [CommRing R]
    {n : Nat} {f g₁ g₂ : R[X]}
    (h₁ : AreApolar n f g₁) (h₂ : AreApolar n f g₂) :
    AreApolar n f (g₁ - g₂) := by
  rw [AreApolar, apolarPairing_sub_right, h₁, h₂, sub_self]

theorem AreApolar.sum_left {R : Type*} [CommRing R]
    {ι : Type*} {n : Nat} {s : Finset ι} {f : ι → R[X]} {g : R[X]}
    (h : ∀ i ∈ s, AreApolar n (f i) g) :
    AreApolar n (Finset.sum s f) g := by
  rw [AreApolar, apolarPairing_sum_left]
  exact Finset.sum_eq_zero fun i hi => h i hi

theorem AreApolar.sum_right {R : Type*} [CommRing R]
    {ι : Type*} {n : Nat} {f : R[X]} {s : Finset ι} {g : ι → R[X]}
    (h : ∀ i ∈ s, AreApolar n f (g i)) :
    AreApolar n f (Finset.sum s g) := by
  rw [AreApolar, apolarPairing_sum_right]
  exact Finset.sum_eq_zero fun i hi => h i hi

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

/-- The apolar pairing of two monomials is supported exactly on complementary
degrees. -/
theorem apolarPairing_monomial_monomial {R : Type*} [CommRing R]
    (n i j : Nat) (a b : R) :
    apolarPairing n (monomial i a) (monomial j b) =
      if i + j = n then (-1 : R) ^ i * (Nat.choose n i : R) * a * b else 0 := by
  rw [apolarPairing_monomial_left]
  by_cases hsum : i + j = n
  · rw [if_pos hsum]
    have hi : i ≤ n := by lia
    rw [if_pos hi]
    have hsub : n - i = j := by lia
    simp [hsub]
  · rw [if_neg hsum]
    by_cases hi : i ≤ n
    · rw [if_pos hi]
      have hneq : j ≠ n - i := by
        intro h
        apply hsum
        lia
      simp [coeff_monomial, hneq]
    · rw [if_neg hi]

/-- Pairing with a power of `X` on the left, obtained from
`apolarPairing_monomial_left` since `X ^ i = monomial i 1`. -/
theorem apolarPairing_X_pow_left {R : Type*} [CommRing R]
    (n i : Nat) (g : R[X]) :
    apolarPairing n (X ^ i) g =
      if i ≤ n then (-1 : R) ^ i * (Nat.choose n i : R) * g.coeff (n - i) else 0 := by
  rw [X_pow_eq_monomial, apolarPairing_monomial_left]
  by_cases hi : i ≤ n <;> simp [hi]

/-- Pairing with a power of `X` on the right, obtained from
`apolarPairing_monomial_right`. -/
theorem apolarPairing_X_pow_right {R : Type*} [CommRing R]
    (n j : Nat) (f : R[X]) :
    apolarPairing n f (X ^ j) =
      if j ≤ n then
        (-1 : R) ^ (n - j) * (Nat.choose n (n - j) : R) * f.coeff (n - j) else 0 := by
  rw [X_pow_eq_monomial, apolarPairing_monomial_right]
  by_cases hj : j ≤ n <;> simp [hj]

/-- Pairing with a constant on the left picks out the top coefficient of `g`. -/
theorem apolarPairing_C_left {R : Type*} [CommRing R]
    (n : Nat) (a : R) (g : R[X]) :
    apolarPairing n (C a) g = a * g.coeff n := by
  rw [← monomial_zero_left, apolarPairing_monomial_left]
  simp

/-- Pairing with a constant on the right picks out the top coefficient of `f`,
twisted by the degree sign. -/
theorem apolarPairing_C_right {R : Type*} [CommRing R]
    (n : Nat) (f : R[X]) (b : R) :
    apolarPairing n f (C b) = (-1 : R) ^ n * f.coeff n * b := by
  rw [← monomial_zero_left, apolarPairing_monomial_right]
  simp

/-- Antidiagonal form of the apolar pairing: the sum ranges over all pairs of
complementary degrees summing to `n`. -/
theorem apolarPairing_eq_sum_antidiagonal {R : Type*} [CommRing R]
    (n : Nat) (f g : R[X]) :
    apolarPairing n f g =
      Finset.sum (Finset.antidiagonal n) fun p =>
        (-1 : R) ^ p.1 * (Nat.choose n p.1 : R) * f.coeff p.1 * g.coeff p.2 := by
  rw [apolarPairing, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Two monomials whose degrees do not sum to `n` are always apolar in degree
`n`, over an arbitrary commutative ring. -/
theorem areApolar_monomial_monomial_of_add_ne {R : Type*} [CommRing R]
    {n i j : Nat} (a b : R) (h : i + j ≠ n) :
    AreApolar n (monomial i a) (monomial j b) := by
  rw [AreApolar, apolarPairing_monomial_monomial, if_neg h]

/-- Over `ℂ`, two monomials are apolar in degree `n` exactly when their degrees
fail to sum to `n`, or one of the coefficients vanishes. -/
theorem areApolar_monomial_monomial_iff_complex
    {n i j : Nat} {a b : ℂ} :
    AreApolar n (monomial i a) (monomial j b) ↔ i + j ≠ n ∨ a = 0 ∨ b = 0 := by
  rw [AreApolar, apolarPairing_monomial_monomial]
  by_cases hsum : i + j = n
  · rw [if_pos hsum]
    have hi : i ≤ n := by lia
    have hchoose : (Nat.choose n i : ℂ) ≠ 0 := by
      have : 0 < Nat.choose n i := Nat.choose_pos hi
      exact_mod_cast this.ne'
    have hsign : ((-1 : ℂ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
    constructor
    · intro hzero
      right
      rcases mul_eq_zero.mp hzero with hpre | hb
      · rcases mul_eq_zero.mp hpre with hpre2 | ha
        · rcases mul_eq_zero.mp hpre2 with hs | hc
          · exact absurd hs hsign
          · exact absurd hc hchoose
        · exact Or.inl ha
      · exact Or.inr hb
    · rintro (hne | ha | hb)
      · exact absurd hsum hne
      · simp [ha]
      · simp [hb]
  · rw [if_neg hsum]
    simp [hsum]

/-- Symmetric companion of a Grace-type apolarity statement: since apolarity is
symmetric, having all roots of `g` in `s` (rather than `f`) forces `f` to have a
root in `s`. -/
theorem GraceApolarityStatement.hasRootIn_left
    {IsGraceDomain : Set ℂ → Prop} (h : GraceApolarityStatement IsGraceDomain)
    ⦃n : Nat⦄ ⦃s : Set ℂ⦄ ⦃f g : ℂ[X]⦄
    (hs : IsGraceDomain s) (hf : f.natDegree = n) (hg : g.natDegree = n)
    (hap : AreApolar n f g) (hroots : g.RootsIn s) :
    f.HasRootIn s :=
  h hs hg hf hap.symm hroots

/-!
## Binomial evaluation and the apolarity-root dictionary

The apolar pairing carries a single binomial weight, so the natural degree-`n`
polynomial attached to a coefficient sequence `f.coeff` is its *binomial lift*
`binomialLift n f = ∑ k ∈ range (n + 1), C(n, k) f_k X^k`.  Its value at `z` is
the `apolarEval`.  The polynomial `coApolarPoint n z` is the reduced coefficient
sequence dual to evaluation at `z`: pairing any `f` against it computes exactly
`apolarEval n f z`.
-/

/-- Binomial evaluation of `f` at `z` in degree `n`:
`apolarEval n f z = ∑ k ∈ range (n + 1), C(n, k) * f.coeff k * z^k`. -/
def apolarEval {R : Type*} [CommRing R] (n : Nat) (f : R[X]) (z : R) : R :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k : R) * f.coeff k * z ^ k

/-- The degree-`n` binomial lift of a coefficient sequence:
`binomialLift n f = ∑ k ∈ range (n + 1), C(n, k) * f.coeff k * X^k`. -/
def binomialLift {R : Type*} [CommRing R] (n : Nat) (f : R[X]) : R[X] :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    monomial k ((Nat.choose n k : R) * f.coeff k)

/-- The reduced coefficient sequence dual to evaluation at `z`. -/
def coApolarPoint {R : Type*} [CommRing R] (n : Nat) (z : R) : R[X] :=
  Finset.sum (Finset.range (n + 1)) fun k => monomial k ((-z) ^ (n - k))

theorem coeff_binomialLift {R : Type*} [CommRing R] (n : Nat) (f : R[X]) (k : Nat) :
    (binomialLift n f).coeff k =
      if k ≤ n then (Nat.choose n k : R) * f.coeff k else 0 := by
  simp only [binomialLift, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) k]
  simp

theorem natDegree_binomialLift_le {R : Type*} [CommRing R] (n : Nat) (f : R[X]) :
    (binomialLift n f).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero]
  simp +contextual [binomialLift, Polynomial.coeff_monomial]

theorem natDegree_coApolarPoint_le {R : Type*} [CommRing R] (n : Nat) (z : R) :
    (coApolarPoint n z).natDegree ≤ n := by
  refine (Polynomial.natDegree_sum_le _ _).trans <| Finset.sup_le fun k hk =>
    (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range_succ_iff.mp hk)

/-- The binomial lift evaluates to the binomial evaluation. -/
theorem eval_binomialLift {R : Type*} [CommRing R] (n : Nat) (f : R[X]) (z : R) :
    (binomialLift n f).eval z = apolarEval n f z := by
  unfold apolarEval binomialLift
  simp +decide [Polynomial.eval_finsetSum]

/-- Key evaluation identity: pairing `f` against `coApolarPoint n z` recovers the
binomial evaluation of `f` at `z`. -/
theorem apolarPairing_coApolarPoint {R : Type*} [CommRing R]
    (n : Nat) (f : R[X]) (z : R) :
    apolarPairing n f (coApolarPoint n z) = apolarEval n f z := by
  rw [coApolarPoint, apolarPairing_sum_right, apolarEval,
    ← Finset.sum_range_reflect
      (fun k => (Nat.choose n k : R) * f.coeff k * z ^ k) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [apolarPairing_monomial_right, if_pos hk', neg_pow z (n - k)]
  have h1 : (-1 : R) ^ (n - k) * (-1 : R) ^ (n - k) = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (↑(n.choose (n - k)) * f.coeff (n - k) * z ^ (n - k)) * h1

/-- `f` is apolar to `coApolarPoint n z` exactly when its binomial evaluation at
`z` vanishes. -/
theorem areApolar_coApolarPoint_iff {R : Type*} [CommRing R]
    (n : Nat) (f : R[X]) (z : R) :
    AreApolar n f (coApolarPoint n z) ↔ apolarEval n f z = 0 := by
  rw [AreApolar, apolarPairing_coApolarPoint]

/-- Apolarity dictionary: `f` is apolar to `coApolarPoint n z` exactly when `z`
is a root of the binomial lift of `f`. -/
theorem areApolar_coApolarPoint_iff_isRoot {R : Type*} [CommRing R]
    (n : Nat) (f : R[X]) (z : R) :
    AreApolar n f (coApolarPoint n z) ↔ (binomialLift n f).IsRoot z := by
  rw [areApolar_coApolarPoint_iff, IsRoot.def, eval_binomialLift]

@[simp] theorem apolarEval_zero {R : Type*} [CommRing R] (n : Nat) (z : R) :
    apolarEval n (0 : R[X]) z = 0 := by
  simp [apolarEval]

theorem apolarEval_add {R : Type*} [CommRing R]
    (n : Nat) (f₁ f₂ : R[X]) (z : R) :
    apolarEval n (f₁ + f₂) z = apolarEval n f₁ z + apolarEval n f₂ z := by
  simp only [apolarEval, Polynomial.coeff_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

theorem apolarEval_C_mul {R : Type*} [CommRing R]
    (n : Nat) (a : R) (f : R[X]) (z : R) :
    apolarEval n (C a * f) z = a * apolarEval n f z := by
  simp only [apolarEval, Polynomial.coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-!
## Grace's apolarity theorem

We prove the closed-disk case of Grace's apolarity theorem via the classical
route.  The *polar derivative* `polarDeriv n ζ A = n • A + (ζ - X) • A'` obeys
Laguerre's theorem: if all zeros of `A` (of degree `n`) lie in a closed disk and
the pole `ζ` is outside the disk, then all zeros of `polarDeriv n ζ A` also lie
in the disk (`polarDeriv_rootsIn`), and the degree drops by exactly one
(`polarDeriv_natDegree`).  Dually, apolarity is preserved when one lift is
polar-shifted and the other is deflated by one of its roots
(`apolarPairing_deflation`).  Induction on the degree then moves a zero from
`binomialLift n f` into `binomialLift n g`.

**Correction to the original statement.**  As originally phrased (with no
constraint on `r`) the theorem is *false* in the degenerate case `n = 0` with an
empty ball `r < 0`: take `f = C 1`, `g = 0`.  Then `binomialLift 0 f = C 1` has
no root, so `RootsIn (closedBall c r)` holds vacuously; `binomialLift 0 g = 0`;
the apolar pairing vanishes; yet `(0 : ℂ[X])` has no root in the empty ball.  We
therefore add the hypothesis `0 ≤ r`, i.e. that `closedBall c r` is a genuine
(nonempty) closed disk — precisely the intended notion of circular region.  The
original signature (without `0 ≤ r`) is recorded in the comment below.

```
theorem grace_apolarity_closedBall {n : Nat} {c : ℂ} {r : ℝ} {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (Metric.closedBall c r)) :
    (binomialLift n g).HasRootIn (Metric.closedBall c r)
```
-/

/-- The order-`n` polar derivative of `A` with pole `ζ`:
`polarDeriv n ζ A = n • A + (ζ - X) • A'`. -/
def polarDeriv (n : Nat) (ζ : ℂ) (A : ℂ[X]) : ℂ[X] :=
  C (n : ℂ) * A + (C ζ - X) * derivative A

/-- The coefficient shift dual to the polar derivative:
`(polarShift ζ f).coeff k = f.coeff k + ζ * f.coeff (k + 1)`. -/
def polarShift (ζ : ℂ) (f : ℂ[X]) : ℂ[X] := f + C ζ * divX f

@[simp] theorem coeff_polarShift (ζ : ℂ) (f : ℂ[X]) (k : Nat) :
    (polarShift ζ f).coeff k = f.coeff k + ζ * f.coeff (k + 1) := by
  simp [polarShift, coeff_divX]

/-
Every polynomial of degree at most `n` (over `ℂ`) is a binomial lift in
degree `n`.
-/
theorem exists_binomialLift_eq {n : Nat} (Q : ℂ[X]) (hQ : Q.natDegree ≤ n) :
    ∃ h : ℂ[X], binomialLift n h = Q := by
  use ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k ( Q.coeff k / Nat.choose n k );
  ext k;
  by_cases hk : k ≤ n <;> simp_all +decide [ binomialLift, Polynomial.coeff_monomial ];
  · rw [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos hk ) ];
  · rw [ if_neg hk.not_ge, Polynomial.coeff_eq_zero_of_natDegree_lt ( by linarith ) ]

/-
Geometric core of Laguerre's theorem.  If `w` lies outside the closed disk,
all `z ∈ S` lie inside it, and `S.card / (w - ζ)` equals the sum of the
reciprocals `1 / (w - z)` over the nonempty multiset `S` (equivalently
`1/(w-ζ)` is the equal-weight average of the `1/(w - z)`), then `ζ` lies inside
the disk.
-/
set_option maxHeartbeats 1200000 in
-- The disk-membership proof normalizes a large complex quadratic inequality.
theorem mem_closedBall_of_recip_avg {c : ℂ} {r : ℝ} (hr : 0 ≤ r) {w ζ : ℂ}
    (S : Multiset ℂ) (hS : S ≠ 0)
    (hw : w ∉ Metric.closedBall c r)
    (hz : ∀ z ∈ S, z ∈ Metric.closedBall c r)
    (hζ : (S.card : ℂ) / (w - ζ) = (S.map (fun z => 1 / (w - z))).sum) :
    ζ ∈ Metric.closedBall c r := by
  -- Since `w ∉ closedBall c r` we have `r < ‖w - c‖`.  Set `α = w - c` and
  -- `A = ‖w - c‖² - r² > 0`.
  set α : ℂ := w - c
  set A : ℝ := Complex.normSq α - r^2
  have hA_pos : 0 < A := by
    simp +zetaDelta at *;
    simpa [ Complex.normSq_eq_norm_sq, dist_eq_norm ] using
      pow_lt_pow_left₀ hw hr two_ne_zero;
  -- By definition of $S$, we know that $1 / (w - z) \in S$ for all $z \in S$.
  have h_reciprocal_in_S : ∀ z ∈ S,
      (1 / (w - z)) ∈ {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0} := by
    intro z hzS
    have hz_dist : Complex.normSq (z - c) ≤ r^2 := by
      have hz_norm : ‖z - c‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz z hzS
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg (z - c)) hz_norm 2
    have hz_reciprocal :
        Complex.normSq (α * (1 / (w - z)) - 1) ≤ r^2 * Complex.normSq (1 / (w - z)) := by
      have hwz_ne : w - z ≠ 0 := by
        intro h
        apply hw
        have hw_eq_z : w = z := sub_eq_zero.mp h
        simpa [hw_eq_z] using hz z hzS
      have hmul : α * (1 / (w - z)) - 1 = (z - c) * (1 / (w - z)) := by
        field_simp [hwz_ne, α]
        ring
      rw [hmul, Complex.normSq_mul]
      exact mul_le_mul_of_nonneg_right hz_dist (Complex.normSq_nonneg (1 / (w - z)))
    simp_all +decide [ Complex.normSq_sub ];
    grind +extAll;
  -- By definition of $S$, we know that $1 / (w - ζ) \in S$.
  have h_reciprocal_in_S_ζ :
      (1 / (w - ζ)) ∈ {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0} := by
    have h_reciprocal_in_S_ζ : (S.card : ℂ)⁻¹ * (S.map (fun z => 1 / (w - z))).sum ∈
        {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0} := by
      have h_reciprocal_in_S_ζ :
          Convex ℝ {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0} := by
        rw [show {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0} =
            Metric.closedBall ((starRingEnd ℂ α) / A) (r / A) by
          ext
          simp [Complex.normSq]
          rw [dist_eq_norm, Complex.norm_def]
          simp +decide [Complex.normSq, Complex.div_re, Complex.div_im]
          ring_nf
          norm_num [hA_pos.le]
          rw [Real.sqrt_le_left] <;> ring_nf <;> norm_num [hA_pos.le, hA_pos.ne']
          · field_simp
            constructor <;> intro <;> nlinarith [Complex.normSq_apply α]
          · positivity]
        exact convex_closedBall ((starRingEnd ℂ α) / A) (r / A)
      have h_reciprocal_in_S_ζ : ∀ (t : Finset ℂ) (wt : ℂ → ℝ) (zpt : ℂ → ℂ),
          (∀ i ∈ t, 0 ≤ wt i) → (∑ i ∈ t, wt i = 1) →
          (∀ i ∈ t, zpt i ∈ {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0}) →
          (∑ i ∈ t, wt i • zpt i) ∈
            {u : ℂ | A * Complex.normSq u - 2 * (α * u).re + 1 ≤ 0} := by
        intros t wt zpt hwt hsum hzpt;
        convert h_reciprocal_in_S_ζ.sum_mem _ _ _ <;> aesop;
      convert h_reciprocal_in_S_ζ ( S.toFinset ) ( fun i => ( S.count i : ℝ ) / S.card )
        ( fun i => 1 / ( w - i ) ) _ _ _ using 1 <;> norm_num;
      · simp +decide [ div_eq_inv_mul, Finset.sum_multiset_map_count ];
        simp +decide only [Finset.mul_sum _ _ _, mul_assoc];
      · exact fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
      · rw [ ← Finset.sum_div, div_eq_iff ] <;> norm_cast <;>
          simp_all +decide [ Finset.sum_multiset_count ];
      · intro z hz; specialize h_reciprocal_in_S z hz; aesop;
    convert h_reciprocal_in_S_ζ using 1;
    rw [ ← hζ, inv_mul_eq_div, div_eq_mul_inv ] ; ring ; aesop;
  by_cases h : w - ζ = 0 <;> simp_all +decide [ div_eq_mul_inv ];
  · norm_num [ ← hζ ] at *;
  · simp_all +decide [ Complex.normSq, Complex.norm_def, dist_eq_norm ];
    simp +zetaDelta at *;
    rw [ Real.sqrt_le_left hr ];
    norm_num [ Complex.normSq ] at *;
    nlinarith [ inv_pos.mpr ( show 0 < ( w.re - ζ.re ) * ( w.re - ζ.re )
        + ( w.im - ζ.im ) * ( w.im - ζ.im ) from not_le.mp fun h' => h <| by
          refine Complex.ext ?_ ?_ <;> norm_num <;> nlinarith ),
      mul_inv_cancel₀ ( show ( w.re - ζ.re ) * ( w.re - ζ.re )
        + ( w.im - ζ.im ) * ( w.im - ζ.im ) ≠ 0 from fun h' => h <| by
          refine Complex.ext ?_ ?_ <;> norm_num <;> nlinarith ) ]

/-
The polar derivative of a binomial lift is, up to the nonzero factor `n`, the
binomial lift of the polar shift.
-/
set_option maxHeartbeats 1200000 in
-- The coefficient comparison below expands a large binomial-sum identity.
theorem polarDeriv_binomialLift {n : Nat} (hn : 1 ≤ n) (ζ : ℂ) (f : ℂ[X]) :
    polarDeriv n ζ (binomialLift n f)
      = C (n : ℂ) * binomialLift (n - 1) (polarShift ζ f) := by
  refine Polynomial.ext fun k => ?_
  rcases k with ( _ | k ) <;>
    simp_all +decide;
  · unfold polarDeriv binomialLift polarShift;
    simp +decide [ Polynomial.coeff_derivative, Polynomial.coeff_C, Polynomial.coeff_X,
      mul_comm ] ;
    rcases n <;> simp_all +decide [ Polynomial.coeff_monomial ];
    ring;
  · by_cases hk : k + 1 ≤ n <;> simp_all +decide [ polarDeriv, binomialLift ];
    · simp +decide [ Polynomial.coeff_derivative, Polynomial.coeff_monomial, sub_mul,
        mul_assoc, Finset.sum_range_succ ];
      split_ifs <;>
        simp_all +decide [ mul_add, add_mul, mul_comm, mul_left_comm ];
      any_goals lia;
      · rcases n with _ | n
        · simp_all
        · simp_all +decide [Nat.choose_succ_succ, add_mul, mul_add, mul_left_comm]
          have h_choose_k := Nat.add_one_mul_choose_eq n k
          have h_choose_succ := Nat.add_one_mul_choose_eq n (k + 1)
          have hChooseK :
              ((n + 1 : ℕ) : ℂ) * (n.choose k : ℂ) =
                ((k + 1 : ℕ) : ℂ) *
                  ((n.choose k : ℂ) + (n.choose (k + 1) : ℂ)) := by
            exact_mod_cast (by
              simpa [Nat.choose_succ_succ, mul_comm] using h_choose_k)
          have hChooseSucc :
              ((n + 1 : ℕ) : ℂ) * (n.choose (k + 1) : ℂ) =
                ((k + 1 + 1 : ℕ) : ℂ) *
                  ((n.choose (k + 1) : ℂ) + (n.choose (k + 1 + 1) : ℂ)) := by
            exact_mod_cast (by
              simpa [Nat.choose_succ_succ, mul_comm] using h_choose_succ)
          rw [show k + 1 = 1 + k by lia]
          rw [show 1 + k + 1 = 2 + k by lia]
          simp only [Nat.add_comm, Nat.add_left_comm] at *
          push_cast at hChooseK hChooseSucc ⊢
          ring_nf at hChooseK hChooseSucc ⊢
          linear_combination (f.coeff (1 + k)) * hChooseK +
            (-(ζ * f.coeff (2 + k))) * hChooseSucc
      · ring;
    · simp +decide [ Polynomial.coeff_monomial, Finset.sum_range_succ', mul_assoc,
        sub_mul, Finset.mul_sum _ _ _ ];
      grind

/-- **Laguerre's theorem** (closed-disk case): if all zeros of `A` (of degree
`n`) lie in the closed disk and the pole `ζ` lies outside it, then all zeros of
the polar derivative lie in the closed disk. -/
theorem polarDeriv_rootsIn {n : Nat} {c : ℂ} {r : ℝ} (hr : 0 ≤ r) {ζ : ℂ}
    {A : ℂ[X]} (hn : 1 ≤ n) (hA : A.natDegree = n)
    (hAroots : A.RootsIn (Metric.closedBall c r))
    (hζ : ζ ∉ Metric.closedBall c r) :
    (polarDeriv n ζ A).RootsIn (Metric.closedBall c r) := by
  intro w hw0
  by_contra hwmem
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  have hAw : eval w A ≠ 0 := fun h => hwmem (hAroots w h)
  have hstar : (n : ℂ) * eval w A + (ζ - w) * eval w (derivative A) = 0 := by
    have h := hw0
    simp only [IsRoot, polarDeriv, eval_add, eval_mul, eval_sub, eval_C, eval_X] at h
    linear_combination h
  have hwζ : w - ζ ≠ 0 := by
    intro h
    apply hAw
    have hzw : ζ - w = 0 := by linear_combination -h
    rw [hzw, zero_mul, add_zero] at hstar
    exact (mul_eq_zero.mp hstar).resolve_left hn0
  have hsplit : A.Splits := IsAlgClosed.splits A
  have hcard : A.roots.card = n := (splits_iff_card_roots.mp hsplit).trans hA
  have hlog : eval w (derivative A) / eval w A
      = (A.roots.map (fun z => 1 / (w - z))).sum :=
    hsplit.eval_derivative_div_eval_of_ne_zero hAw
  have hdiv : eval w (derivative A) / eval w A = (n : ℂ) / (w - ζ) := by
    rw [div_eq_div_iff hAw hwζ]
    linear_combination -hstar
  have hζeq : (A.roots.card : ℂ) / (w - ζ)
      = (A.roots.map (fun z => 1 / (w - z))).sum := by
    rw [hcard, ← hdiv, hlog]
  have hmem : ζ ∈ Metric.closedBall c r := by
    refine mem_closedBall_of_recip_avg hr A.roots ?_ hwmem ?_ hζeq
    · rw [← Multiset.card_pos, hcard]; exact hn
    · exact fun z hz => hAroots z (isRoot_of_mem_roots hz)
  exact hζ hmem

/-
The barycenter (average) of a nonempty multiset of points of a closed disk
lies in the disk.
-/
theorem multiset_avg_mem_closedBall {c : ℂ} {r : ℝ} (S : Multiset ℂ) (hS : S ≠ 0)
    (hz : ∀ z ∈ S, z ∈ Metric.closedBall c r) :
    S.sum / (S.card : ℂ) ∈ Metric.closedBall c r := by
  have h_convex : ∀ (s : Finset ℂ) (w : ℂ → ℝ), (∀ z ∈ s, 0 ≤ w z) →
      (∑ z ∈ s, w z = 1) → (∀ z ∈ s, z ∈ Metric.closedBall c r) →
      (∑ z ∈ s, w z • z) ∈ Metric.closedBall c r := by
    intros s w hw_nonneg hw_sum hw_mem
    have h_convex : Convex ℝ (Metric.closedBall c r) := by
      exact convex_closedBall c r;
    convert h_convex.sum_mem _ _ _ <;> aesop;
  convert h_convex ( S.toFinset ) ( fun z => ( S.count z : ℝ ) / S.card ) _ _ _ using 1;
  · simp +decide [ div_eq_inv_mul ];
    simp +decide [ ← Finset.mul_sum _ _ _, mul_assoc, Finset.sum_multiset_count ];
  · exact fun z hz => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
  · rw [ ← Finset.sum_div, div_eq_iff ] <;> norm_cast <;>
      simp_all +decide;
  · grind

/-
The polar derivative drops the degree by exactly one when the pole lies
outside a disk containing all zeros of `A`.
-/
theorem polarDeriv_natDegree {n : Nat} {c : ℂ} {r : ℝ} {ζ : ℂ}
    {A : ℂ[X]} (hn : 1 ≤ n) (hA : A.natDegree = n)
    (hAroots : A.RootsIn (Metric.closedBall c r))
    (hζ : ζ ∉ Metric.closedBall c r) :
    (polarDeriv n ζ A).natDegree = n - 1 := by
  refine le_antisymm ?_ ?_
  · rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
    unfold polarDeriv; simp_all +decide;
    intro m hm;
    rcases m with ( _ | m ) <;>
      simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_derivative,
        sub_mul ] ;
    cases hm.eq_or_lt <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
    ring;
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    have h_coeff : (polarDeriv n ζ A).coeff (n - 1)
        = A.coeff n * ((n : ℂ) * ζ - Multiset.sum A.roots) := by
      have h_coeff : (polarDeriv n ζ A).coeff (n - 1)
          = ((n : ℂ) - (n - 1)) * A.coeff (n - 1) + ζ * (n : ℂ) * A.coeff n := by
        unfold polarDeriv;
        simp +decide [ Polynomial.coeff_derivative, mul_assoc, sub_mul ] ;
        rcases n with ( _ | _ | n ) <;>
          simp_all +decide [ Polynomial.coeff_derivative, mul_comm ];
        ring;
      have h_vieta : A.coeff (n - 1)
          = A.leadingCoeff * (-1) ^ (n - (n - 1)) * Multiset.esymm A.roots (n - (n - 1)) := by
        convert Polynomial.coeff_eq_esymm_roots_of_card _ _ using 1;
        all_goals norm_num [ hA ];
        exact inferInstance;
        convert Polynomial.splits_iff_card_roots.mp ( IsAlgClosed.splits A ) using 1;
        all_goals norm_num [ hA ];
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ Multiset.esymm ];
      · simp_all +decide [ Multiset.powersetCard_one, mul_sub ] ; ring;
        rw [ Polynomial.leadingCoeff, hA ] ; ring;
      · simp_all +decide [ Multiset.powersetCard_one, Polynomial.leadingCoeff ] ; ring;
    simp_all +decide [ sub_eq_iff_eq_add ];
    refine ⟨ ?_, ?_ ⟩
    · rw [ ← hA, Polynomial.coeff_natDegree ] ; aesop;
    · intro h;
      have h_avg : A.roots.sum / (A.roots.card : ℂ) ∈ Metric.closedBall c r := by
        apply multiset_avg_mem_closedBall;
        · intro H; simp_all +decide;
          replace H := congr_arg Multiset.toFinset H;
          rw [ Finset.ext_iff ] at H;
          specialize H ( Classical.choose ( Complex.exists_root <|
            show A.degree > 0 from Polynomial.natDegree_pos_iff_degree_pos.mp <| by linarith ) ) ;
          have := Classical.choose_spec ( Complex.exists_root <|
            show A.degree > 0 from Polynomial.natDegree_pos_iff_degree_pos.mp <| by linarith ) ;
          aesop;
        · exact fun z hz => hAroots z <| Polynomial.isRoot_of_mem_roots hz;
      rw [ ← h, mul_div_assoc ] at h_avg;
      rw [ show A.roots.card = n by
        rw [ ← hA, Polynomial.natDegree_eq_of_degree_eq_some
          ( Polynomial.degree_eq_natDegree <| by aesop ) ] ;
        exact Polynomial.splits_iff_card_roots.mp <| IsAlgClosed.splits _ ] at h_avg ;
      simp_all +decide [ mul_div_cancel₀, ne_of_gt ( zero_lt_one.trans_le hn ) ];
      linarith

/-
The apolar pairing rewritten so that the binomial weights are absorbed into
`binomialLift n g`: `apolarPairing n f g = ∑ (-1)^k f.coeff k * (binomialLift n g).coeff (n-k)`.
-/
theorem apolarPairing_eq_sum_binomialLift (n : Nat) (f g : ℂ[X]) :
    apolarPairing n f g
      = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * f.coeff k * (binomialLift n g).coeff (n - k) := by
  -- By definition of `binomialLift`, rewrite the coefficient of `binomialLift n g`
  -- at position `n - k`.
  have h_coeff : ∀ k ∈ Finset.range (n + 1),
      (binomialLift n g).coeff (n - k) = (Nat.choose n (n - k) : ℂ) * g.coeff (n - k) := by
    simp +decide [ binomialLift ];
    simp +decide [ Polynomial.coeff_monomial ];
  exact Finset.sum_congr rfl fun x hx => by
    rw [ h_coeff x hx, Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ) ] ; ring;

/-
Apolarity is preserved by polar-shifting one lift and deflating the other by
a root: the algebraic engine of Grace's theorem.
-/
set_option maxHeartbeats 1200000 in
-- The deflation identity expands two binomial-lift sums before cancellation.
theorem apolarPairing_deflation {n : Nat} (hn : 1 ≤ n) {ζ : ℂ} {f g g' : ℂ[X]}
    (hdefl : (X - C ζ) * binomialLift (n - 1) g' = binomialLift n g) :
    apolarPairing (n - 1) (polarShift ζ f) g' = apolarPairing n f g := by
  convert ( congr_arg
    ( fun x : ℂ[X] => apolarPairing ( n - 1 ) ( polarShift ζ f ) g' ) hdefl ) using 1;
  obtain ⟨ m, rfl ⟩ := Nat.exists_eq_add_of_le hn;
  rw [ apolarPairing_eq_sum_binomialLift, apolarPairing_eq_sum_binomialLift ];
  simp +decide [ ← hdefl, Finset.sum_range_succ', mul_assoc, mul_left_comm, mul_comm,
    mul_sub ];
  rw [ add_comm 1 m, Finset.sum_range_succ ] ;
  norm_num [ Polynomial.coeff_X, mul_assoc, mul_left_comm, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, pow_succ' ] ;
  ring;
  rw [ add_comm 1 m, Finset.sum_range_succ' ] ;
  norm_num [ Polynomial.coeff_X, mul_assoc, mul_left_comm, mul_comm, Finset.sum_range_succ ] ;
  ring;
  simp +decide [ add_comm 1, add_comm 2, mul_assoc, mul_left_comm ] ;
  ring;
  rw [ show ( binomialLift m g' ).coeff ( 1 + m ) = 0 from _ ] ; ring;
  · rw [ Finset.sum_congr rfl fun x hx => by
        rw [ show m - x = m - ( 1 + x ) + 1 by
          rw [ tsub_add_eq_add_tsub ( by linarith [ Finset.mem_range.mp hx ] ) ] ;
          simp +decide [ add_comm ] ] ] ;
      norm_num [ Polynomial.coeff_X, mul_assoc, mul_left_comm, Finset.sum_add_distrib,
        Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, pow_succ' ] ;
      ring;
  · rw [ add_comm, Polynomial.coeff_eq_zero_of_natDegree_lt ];
    exact Nat.lt_succ_of_le ( natDegree_binomialLift_le _ _ )

/-
Degree-induction core of Grace's theorem.
-/
private theorem grace_aux {c : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    ∀ (n : Nat) (f g : ℂ[X]),
      (binomialLift n f).natDegree = n → (binomialLift n g).natDegree = n →
      AreApolar n f g → (binomialLift n f).RootsIn (Metric.closedBall c r) →
      (binomialLift n g).HasRootIn (Metric.closedBall c r) := by
  -- Apply induction on $n$.
  intro n
  induction' n using Nat.strong_induction_on with n ih;
  intro f g hf hg hap hroots
  by_cases hn : n = 0;
  · by_cases h : g.coeff 0 = 0 <;> simp_all +decide;
    · refine ⟨ c, ?_, ?_ ⟩ <;> simp_all +decide [ binomialLift ];
    · have h_contra : f.coeff 0 = 0 := by
        unfold AreApolar at hap; simp_all +decide [ apolarPairing ] ;
      contrapose! hroots;
      unfold RootsIn; simp_all +decide [ binomialLift ] ;
      rcases exists_nat_gt r with ⟨ n, hn ⟩ ;
      exact ⟨ c + n, by simpa [ abs_of_nonneg hr ] using hn ⟩;
  · obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, (binomialLift n g).IsRoot ζ := by
      exact Complex.exists_root ( show Polynomial.degree ( binomialLift n g ) > 0 from
        Polynomial.natDegree_pos_iff_degree_pos.mp ( by rw [ hg ] ; positivity ) );
    by_cases hζ' : ζ ∈ Metric.closedBall c r;
    · exact ⟨ ζ, hζ, hζ' ⟩;
    · -- Let `f' := polarShift ζ f`; then `polarDeriv n ζ A` equals
      -- `C (n : ℂ) * binomialLift (n - 1) f'` (`polarDeriv_binomialLift`).
      set f' := polarShift ζ f
      have hf' : (binomialLift (n - 1) f').natDegree = n - 1 := by
        have hf' : (polarDeriv n ζ (binomialLift n f)).natDegree = n - 1 := by
          apply polarDeriv_natDegree;
          exact Nat.pos_of_ne_zero hn;
          exacts [ hf, hroots, hζ' ];
        rw [ polarDeriv_binomialLift ( Nat.pos_of_ne_zero hn ) ζ f ] at hf';
        rwa [ Polynomial.natDegree_C_mul ] at hf' ; aesop
      have hf'_roots : (binomialLift (n - 1) f').RootsIn (Metric.closedBall c r) := by
        have := polarDeriv_rootsIn hr ( Nat.pos_of_ne_zero hn ) hf hroots hζ';
        have := polarDeriv_binomialLift ( Nat.pos_of_ne_zero hn ) ζ f;
        simp_all +decide [ RootsIn ] ;
        assumption;
      -- Let `B₁ := B /ₘ (X - C ζ)`.  Since `B.IsRoot ζ` we have
      -- `(X - C ζ) * B₁ = B` (`mul_divByMonic_eq_iff_isRoot`).
      obtain ⟨g', hg'⟩ :
          ∃ g' : ℂ[X], (X - C ζ) * binomialLift (n - 1) g' = binomialLift n g := by
        obtain ⟨g', hg'⟩ : ∃ g' : ℂ[X], binomialLift n g = (X - C ζ) * g' := by
          exact Polynomial.dvd_iff_isRoot.mpr hζ;
        have hg'_deg : g'.natDegree = n - 1 := by
          rw [ hg', Polynomial.natDegree_mul' ] at hg <;> aesop;
        obtain ⟨ g'', hg'' ⟩ := exists_binomialLift_eq g' ( by linarith ) ; use g''; aesop;
      -- Apolarity: `apolarPairing (n-1) f' g' = apolarPairing n f g = 0`
      -- (`apolarPairing_deflation hn hdefl`, then `hap`); so `AreApolar (n-1) f' g'`.
      have hap' : AreApolar (n - 1) f' g' := by
        convert apolarPairing_deflation ( Nat.pos_of_ne_zero hn ) hg' using 1;
        rw [ hap ];
        rfl;
      -- Apply the induction hypothesis to `f'` and `g'`.
      obtain ⟨w, hw⟩ :
          ∃ w : ℂ, (binomialLift (n - 1) g').IsRoot w ∧ w ∈ Metric.closedBall c r := by
        apply ih (n - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hn) (by linarith)) f' g' hf' (by
        replace hg' := congr_arg Polynomial.natDegree hg';
        rw [ Polynomial.natDegree_mul' ] at hg' <;> norm_num at * ; lia;
        intro H
        simp_all +decide) hap' hf'_roots;
      exact ⟨ w, by replace hg' := congr_arg ( Polynomial.eval w ) hg'; aesop ⟩

/-- **Grace's apolarity theorem** (closed-disk case), phrased for the binomial
lifts.  If `0 ≤ r`, the degree-`n` binomial lifts of `f` and `g` are apolar, and
all zeros of `binomialLift n f` lie in the closed disk `closedBall c r`, then
`binomialLift n g` has a zero in that disk.

Note: the hypothesis `0 ≤ r` was added to the original issue statement; without
it the claim is false for `n = 0` and an empty ball (see the section note). -/
theorem grace_apolarity_closedBall {n : Nat} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (Metric.closedBall c r)) :
    (binomialLift n g).HasRootIn (Metric.closedBall c r) :=
  grace_aux hr n f g hf hg hap hroots

/-- Root-transfer corollary in the form most convenient for Schur-Szego
composition: from Grace's theorem, if `binomialLift n f` has all its zeros in a
closed disk and `f`, `g` are apolar, then some `z` in that disk is a zero of
`binomialLift n g`, equivalently `g` is apolar to `coApolarPoint n z`. -/
theorem exists_coApolarPoint_apolar_of_grace {n : Nat} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (Metric.closedBall c r)) :
    ∃ z, z ∈ Metric.closedBall c r ∧ AreApolar n g (coApolarPoint n z) := by
  obtain ⟨z, hzroot, hzmem⟩ := grace_apolarity_closedBall hr hf hg hap hroots
  exact ⟨z, hzmem, (areApolar_coApolarPoint_iff_isRoot n g z).2 hzroot⟩

end RealRooted
