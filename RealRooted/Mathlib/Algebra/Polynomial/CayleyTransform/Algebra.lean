import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Algebraic formulas for the finite-degree Cayley transform

Root-factor, injectivity, and binomial-basis formulas over the complex numbers.
-/

open Polynomial

noncomputable section

namespace Polynomial

/-- Root-factor form of the Cayley homogenization. -/
theorem cayleyTransform_eq_rootFactorProduct
    {K : Type*} [Field K] {p : K[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n) :
    cayleyTransform n p =
      C p.leadingCoeff *
        (p.roots.map (fun r => (1 + C r) * X - C r)).prod := by
  have hcard : p.roots.card = n := by
    rw [← hp.natDegree_eq_card_roots, hdeg]
  have hhom := congrArg (fun q : K[X] => q.homogenize n)
    hp.eq_prod_roots
  rw [Polynomial.homogenize_C_mul, ← hcard,
    Polynomial.homogenize_rootFactorProduct] at hhom
  have hhom' : p.homogenize n =
      MvPolynomial.C p.leadingCoeff *
        (p.roots.map (fun r ↦
          MvPolynomial.X 0 - MvPolynomial.C r * MvPolynomial.X 1)).prod := by simp_all
  rw [cayleyTransform, hhom']
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_mul,
    MvPolynomial.algHom_C, algebraMap_eq, mul_eq_mul_left_iff, map_eq_zero,
    leadingCoeff_eq_zero]
  left
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r hr
  simp
  ring

/-- Root-factor form in an ambient degree box.  The extra power records the
roots at infinity introduced when `natDegree p < n`. -/
theorem cayleyTransform_eq_rootFactorProduct_mul
    {K : Type*} [Field K] {p : K[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree ≤ n) :
    cayleyTransform n p =
      C p.leadingCoeff *
          (p.roots.map (fun r => (1 + C r) * X - C r)).prod *
        (1 - X) ^ (n - p.natDegree) := by
  rw [cayleyTransform,
    homogenize_eq_homogenize_natDegree_mul_X_one_pow hdeg, map_mul,
    map_pow]
  have hx1 : MvPolynomial.aeval
      (![(X : K[X]), (1 - X : K[X])] : Fin 2 → K[X])
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) =
        (1 - X : K[X]) := by simp
  rw [hx1]
  change cayleyTransform p.natDegree p * (1 - X) ^ (n - p.natDegree) = _
  rw [cayleyTransform_eq_rootFactorProduct hp rfl]

theorem cayleyTransform_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K]
    {p : K[X]} {n : ℕ} (hp0 : p ≠ 0) (hdeg : p.natDegree ≤ n) :
    cayleyTransform n p ≠ 0 := by
  rw [cayleyTransform_eq_rootFactorProduct_mul
    (IsAlgClosed.splits p) hdeg]
  apply mul_ne_zero
  · apply mul_ne_zero
    · simp_all
    · apply Multiset.prod_ne_zero
      intro hf
      rcases Multiset.mem_map.mp hf with ⟨r, _, hr⟩
      have hzero : (1 + C r) * X - C r = 0 := by assumption
      have hcoeff0 := congrArg (fun q : K[X] ↦ q.coeff 0) hzero
      have hcoeff1 := congrArg (fun q : K[X] ↦ q.coeff 1) hzero
      simp at hcoeff0 hcoeff1
      simp_all
  · apply pow_ne_zero
    intro hzero
    have hcoeff := congrArg (fun q : K[X] ↦ q.coeff 1) hzero
    simp [coeff_one, coeff_X] at hcoeff

/-- The Cayley substitution is injective on every finite degree box. -/
theorem cayleyTransform_injective_on_natDegree_le (n : ℕ)
    {K : Type*} [Field K] [IsAlgClosed K]
    {p q : K[X]} (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n)
    (heq : cayleyTransform n p = cayleyTransform n q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hsub
  apply cayleyTransform_ne_zero hsub
    ((natDegree_sub_le p q).trans (max_le hpdeg hqdeg))
  rw [cayleyTransform_sub, heq, sub_self]

lemma homogenize_one_add_X_pow {K : Type*} [Field K] (m : ℕ) :
    ((1 + X : K[X]) ^ m).homogenize m =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hdeg : ((1 + X : K[X]) ^ m).natDegree ≤ m := by
        rw [show (1 + X : K[X]) = X + C 1 by simp [add_comm],
          natDegree_pow_X_add_C]
      have hmul := Polynomial.homogenize_mul
        ((1 + X : K[X]) ^ m) (1 + X) (m := m) (n := 1)
        hdeg (by compute_degree!)
      rw [pow_succ, hmul, ih]
      simp [Polynomial.homogenize_add]
      ring

/-- A degree-`n` Bernstein/binomial basis element becomes a monomial under
the Cayley transform. -/
theorem cayleyTransform_binomialBasisRaw
    {K : Type*} [Field K] {n k : ℕ} (hk : k ≤ n) :
    cayleyTransform n (X ^ k * (1 + X) ^ (n - k) : K[X]) = X ^ k := by
  have hmul := Polynomial.homogenize_mul (X ^ k : K[X])
    ((1 + X) ^ (n - k)) (m := k) (n := n - k)
    (by simp) (by
      rw [show (1 + X : K[X]) = X + C 1 by simp [add_comm],
        natDegree_pow_X_add_C])
  rw [Nat.add_sub_of_le hk] at hmul
  rw [cayleyTransform, hmul, Polynomial.homogenize_X_pow le_rfl,
    homogenize_one_add_X_pow]
  simp

lemma homogenize_one_add_two_X_pow
    {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    ((1 + C 2 * X : K[X]) ^ n).homogenize n =
      (MvPolynomial.X 1 + MvPolynomial.C 2 * MvPolynomial.X 0) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hdeg : ((1 + C 2 * X : K[X]) ^ n).natDegree ≤ n := by
        compute_degree!
      have hmul := Polynomial.homogenize_mul
        ((1 + C 2 * X : K[X]) ^ n) (1 + C 2 * X)
        (m := n) (n := 1) hdeg (by compute_degree!)
      rw [pow_succ, hmul, ih]
      simp [Polynomial.homogenize_add, Polynomial.homogenize_C_mul]
      ring

theorem cayleyTransform_twoPascal
    {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    cayleyTransform n ((1 + C 2 * X : K[X]) ^ n) = (1 + X) ^ n := by
  rw [cayleyTransform, homogenize_one_add_two_X_pow]
  simp
  congr 1
  simp [map_ofNat]
  ring

end Polynomial
