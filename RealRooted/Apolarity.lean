import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Complex.Basic
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

The full proof requires the theory of circular regions, which is not yet
available in this development.  We record the closed-disk case as the remaining
classical boundary; the preceding algebraic declarations are sorry-free.
-/

/-- **Grace's apolarity theorem** (closed-disk case), phrased for the binomial
lifts.  If the degree-`n` binomial lifts of `f` and `g` are apolar and all zeros
of `binomialLift n f` lie in the closed disk `closedBall c r`, then
`binomialLift n g` has a zero in that disk. -/
theorem grace_apolarity_closedBall {n : Nat} {c : ℂ} {r : ℝ} {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (Metric.closedBall c r)) :
    (binomialLift n g).HasRootIn (Metric.closedBall c r) := by
  sorry

/-- Root-transfer corollary in the form most convenient for Schur-Szego
composition: from Grace's theorem, if `binomialLift n f` has all its zeros in a
closed disk and `f`, `g` are apolar, then some `z` in that disk is a zero of
`binomialLift n g`, equivalently `g` is apolar to `coApolarPoint n z`. -/
theorem exists_coApolarPoint_apolar_of_grace {n : Nat} {c : ℂ} {r : ℝ}
    {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (Metric.closedBall c r)) :
    ∃ z, z ∈ Metric.closedBall c r ∧ AreApolar n g (coApolarPoint n z) := by
  obtain ⟨z, hzroot, hzmem⟩ := grace_apolarity_closedBall hf hg hap hroots
  exact ⟨z, hzmem, (areApolar_coApolarPoint_iff_isRoot n g z).2 hzroot⟩

end RealRooted
