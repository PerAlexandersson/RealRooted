/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.ComputeDegree
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic.Ring

/-!
# Finite-degree Möbius transform of a polynomial

The transform

`mobiusTransform n a b c d p = (c X + d)^n p((a X + b) / (c X + d))`

is defined through homogeneous evaluation, so no rational-function side conditions are needed.
We prove linearity, the expansion in the basis `(a X + b)^k (c X + d)^(n - k)`, the product formula
for split polynomials, the composition law (which is the matrix product), and nonvanishing when
`a d - b c` is a unit.  The Cayley transform `(1 - X)^n p(X / (1 - X))` is the case
`(a, b, c, d) = (1, 0, -1, 1)`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The degree-`n` Möbius transform `(c X + d)^n * p ((a X + b) / (c X + d))`, computed without
division by substituting `a X + b` and `c X + d` into the degree-`n` homogenization of `p`. -/
def mobiusTransform (n : ℕ) (a b c d : R) (p : R[X]) : R[X] :=
  MvPolynomial.aeval ![C a * X + C b, C c * X + C d] (p.homogenize n)

variable (n : ℕ) (a b c d : R)

/-- The Möbius transform of `0` is `0`. -/
@[simp] theorem mobiusTransform_zero :
    mobiusTransform n a b c d (0 : R[X]) = 0 := by
  simp [mobiusTransform]

/-- The Möbius transform is additive. -/
theorem mobiusTransform_add (p q : R[X]) :
    mobiusTransform n a b c d (p + q) =
      mobiusTransform n a b c d p + mobiusTransform n a b c d q := by
  simp [mobiusTransform, Polynomial.homogenize_add]

/-- The Möbius transform commutes with subtraction. -/
theorem mobiusTransform_sub (p q : R[X]) :
    mobiusTransform n a b c d (p - q) =
      mobiusTransform n a b c d p - mobiusTransform n a b c d q := by
  simp [mobiusTransform, Polynomial.homogenize_sub]

/-- The Möbius transform commutes with negation. -/
theorem mobiusTransform_neg (p : R[X]) :
    mobiusTransform n a b c d (-p) = -mobiusTransform n a b c d p := by
  simp [mobiusTransform, Polynomial.homogenize_neg]

/-- The Möbius transform commutes with multiplication by a constant. -/
theorem mobiusTransform_C_mul (r : R) (p : R[X]) :
    mobiusTransform n a b c d (C r * p) = C r * mobiusTransform n a b c d p := by
  simp [mobiusTransform, Polynomial.homogenize_C_mul]

/-- The Möbius transform commutes with finite sums. -/
theorem mobiusTransform_finset_sum {ι : Type*} (s : Finset ι) (p : ι → R[X]) :
    mobiusTransform n a b c d (∑ i ∈ s, p i) = ∑ i ∈ s, mobiusTransform n a b c d (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, mobiusTransform_add]

/-- The Möbius transform as an `R`-linear map on polynomials. -/
def mobiusTransformLinearMap : R[X] →ₗ[R] R[X] where
  toFun := mobiusTransform n a b c d
  map_add' := mobiusTransform_add n a b c d
  map_smul' r p := by simp [smul_eq_C_mul, mobiusTransform_C_mul]

/-- Evaluation of `mobiusTransformLinearMap`. -/
@[simp] theorem mobiusTransformLinearMap_apply (p : R[X]) :
    mobiusTransformLinearMap n a b c d p = mobiusTransform n a b c d p := rfl

/-- A polynomial of degree at most `n` has Möbius transform
`∑ k, a_k (a X + b)^k (c X + d)^(n - k)`. -/
theorem mobiusTransform_eq_sum {p : R[X]} (hdeg : p.natDegree ≤ n) :
    mobiusTransform n a b c d p =
      ∑ k ∈ Finset.range (n + 1),
        C (p.coeff k) * ((C a * X + C b) ^ k * (C c * X + C d) ^ (n - k)) := by
  rw [mobiusTransform, Polynomial.homogenize_eq_sum_range_C_mul_X_pow hdeg]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- Evaluation of the Möbius transform: for `natDegree p ≤ n` and `c x + d ≠ 0`, the transform at
`x` is `(c x + d)^n * p ((a x + b) / (c x + d))`. -/
theorem eval_mobiusTransform {K : Type*} [Field K] (a b c d : K) {p : K[X]}
    (hp : p.natDegree ≤ n) {x : K} (hx : c * x + d ≠ 0) :
    (mobiusTransform n a b c d p).eval x =
      (c * x + d) ^ n * p.eval ((a * x + b) / (c * x + d)) := by
  rw [mobiusTransform_eq_sum n a b c d hp, eval_finsetSum,
    eval_eq_sum_range' (n := n + 1) (by lia), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  rw [show (c * x + d) ^ n = (c * x + d) ^ (n - k) * (c * x + d) ^ k by
    rw [← pow_add, Nat.sub_add_cancel hk'], div_pow]
  have hxk : (c * x + d) ^ k ≠ 0 := pow_ne_zero _ hx
  rw [mul_comm c x] at hxk ⊢
  field_simp

/-- The transform of the monomial `X^k` in degree `n ≥ k`. -/
theorem mobiusTransform_X_pow {k : ℕ} (hk : k ≤ n) :
    mobiusTransform n a b c d (X ^ k : R[X]) = (C a * X + C b) ^ k * (C c * X + C d) ^ (n - k) := by
  rw [mobiusTransform, Polynomial.homogenize_X_pow hk]
  simp

/-- The transform of a constant in degree `n`. -/
theorem mobiusTransform_C (r : R) :
    mobiusTransform n a b c d (C r : R[X]) = C r * (C c * X + C d) ^ n := by
  simp [mobiusTransform, Polynomial.homogenize_C]

/-- The transform of a product, in the sum of the degree boxes. -/
theorem mobiusTransform_mul {p q : R[X]} {m k : ℕ} (hp : p.natDegree ≤ m)
    (hq : q.natDegree ≤ k) :
    mobiusTransform (m + k) a b c d (p * q) =
      mobiusTransform m a b c d p * mobiusTransform k a b c d q := by
  simp [mobiusTransform, Polynomial.homogenize_mul p q hp hq]

/-- The transform in degree `1` of a linear polynomial `u X + v`. -/
theorem mobiusTransform_one_linear (u v : R) :
    mobiusTransform 1 a b c d (C u * X + C v) =
      C u * (C a * X + C b) + C v * (C c * X + C d) := by
  simp [mobiusTransform, Polynomial.homogenize_add, Polynomial.homogenize_C_mul,
    Polynomial.homogenize_X, Polynomial.homogenize_C]

/-- A power `k` of a linear polynomial has degree at most `k`. -/
private theorem natDegree_linear_pow_le (u v : R) (k : ℕ) :
    ((C u * X + C v) ^ k).natDegree ≤ k := by
  refine (natDegree_pow_le_of_le k (m := 1) (by compute_degree)).trans (by simp)

/-- The transform of a product of powers of two linear forms. -/
theorem mobiusTransform_linear_pow_mul (u v u' v' : R) {k : ℕ} (hk : k ≤ n) :
    mobiusTransform n a b c d ((C u * X + C v) ^ k * (C u' * X + C v') ^ (n - k)) =
      (C u * (C a * X + C b) + C v * (C c * X + C d)) ^ k *
        (C u' * (C a * X + C b) + C v' * (C c * X + C d)) ^ (n - k) := by
  have h := mobiusTransform_mul a b c d (natDegree_linear_pow_le u v k)
    (natDegree_linear_pow_le u' v' (n - k))
  rw [Nat.add_sub_of_le hk] at h
  rw [h]
  have hpow : ∀ (u v : R) (m : ℕ), mobiusTransform m a b c d ((C u * X + C v) ^ m) =
      (C u * (C a * X + C b) + C v * (C c * X + C d)) ^ m := by
    intro u v m
    induction m with
    | zero => simp [mobiusTransform]
    | succ m ih =>
      rw [pow_succ, mobiusTransform_mul a b c d (natDegree_linear_pow_le u v m)
        (by compute_degree), ih, mobiusTransform_one_linear, pow_succ]
  rw [hpow, hpow]

/-- Composition of Möbius transforms is the transform of the matrix product: applying the matrix
`(a', b'; c', d')` first and then `(a, b; c, d)` is the transform of the product
`(a', b'; c', d') * (a, b; c, d)`. -/
theorem mobiusTransform_mobiusTransform (a' b' c' d' : R) {p : R[X]} (hp : p.natDegree ≤ n) :
    mobiusTransform n a b c d (mobiusTransform n a' b' c' d' p) =
      mobiusTransform n (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c)
        (c' * b + d' * d) p := by
  rw [mobiusTransform_eq_sum n a' b' c' d' hp, mobiusTransform_finset_sum,
    mobiusTransform_eq_sum n _ _ _ _ hp]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [mobiusTransform_C_mul, mobiusTransform_linear_pow_mul n a b c d _ _ _ _ hk']
  congr 3 <;> simp only [map_add, map_mul] <;> ring

/-- The transform by the identity matrix fixes polynomials of degree at most `n`. -/
theorem mobiusTransform_one_zero_zero_one {p : R[X]} (hp : p.natDegree ≤ n) :
    mobiusTransform n 1 0 0 1 p = p := by
  rw [mobiusTransform_eq_sum n _ _ _ _ hp]
  simp only [map_one, map_zero, one_mul, zero_mul, zero_add, add_zero, mul_one, one_pow]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow' (n := n + 1) (by lia)]

/-- The transform by a scalar matrix `δ I` multiplies by `δ ^ n`. -/
theorem mobiusTransform_scalar (δ : R) {p : R[X]} (hp : p.natDegree ≤ n) :
    mobiusTransform n δ 0 0 δ p = C δ ^ n * p := by
  rw [mobiusTransform_eq_sum n _ _ _ _ hp]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow' (n := n + 1) (by lia), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have : (C δ) ^ n = C δ ^ k * C δ ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le hk']
  simp only [map_zero, add_zero, zero_mul, zero_add, mul_pow, this]
  ring

/-- The transform of a polynomial of degree at most `n` has degree at most `n`. -/
theorem natDegree_mobiusTransform_le {p : R[X]} (hp : p.natDegree ≤ n) :
    (mobiusTransform n a b c d p).natDegree ≤ n := by
  rw [mobiusTransform_eq_sum n a b c d hp]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
  have h1 := natDegree_linear_pow_le a b k
  have h2 := natDegree_linear_pow_le c d (n - k)
  lia

/-- If `a d - b c` is a unit, the transform of a nonzero polynomial of degree at most `n` is
nonzero. -/
theorem mobiusTransform_ne_zero {p : R[X]} (hp0 : p ≠ 0) (hp : p.natDegree ≤ n)
    (hdet : IsUnit (a * d - b * c)) : mobiusTransform n a b c d p ≠ 0 := by
  intro h
  have h3 : mobiusTransform n d (-b) (-c) a (mobiusTransform n a b c d p) =
      mobiusTransform n (a * d - b * c) 0 0 (a * d - b * c) p := by
    rw [mobiusTransform_mobiusTransform n d (-b) (-c) a a b c d hp]
    congr 5 <;> ring
  rw [h, mobiusTransform_zero, mobiusTransform_scalar n _ hp] at h3
  have hu : IsUnit (C (a * d - b * c) ^ n) := (hdet.map C).pow n
  exact hp0 ((hu.mul_right_eq_zero).1 h3.symm)

/-- The Cayley transform is the Möbius transform with matrix `(1, 0; -1, 1)`. -/
theorem cayleyTransform_eq_mobiusTransform (p : R[X]) :
    cayleyTransform n p = mobiusTransform n 1 0 (-1) 1 p := by
  have : (![X, 1 - X] : Fin 2 → R[X]) = ![C 1 * X + C 0, C (-1) * X + C 1] := by
    funext i; fin_cases i <;> simp [sub_eq_add_neg, add_comm]
  simp only [cayleyTransform, mobiusTransform, this]

/-- Evaluation of the Cayley transform: `(1 - x)^n * p (x / (1 - x))` for `natDegree p ≤ n`. -/
theorem eval_cayleyTransform {K : Type*} [Field K] {p : K[X]} (hp : p.natDegree ≤ n) {x : K}
    (hx : 1 - x ≠ 0) :
    (cayleyTransform n p).eval x = (1 - x) ^ n * p.eval (x / (1 - x)) := by
  have h : -1 * x + 1 = 1 - x := by ring
  rw [cayleyTransform_eq_mobiusTransform, eval_mobiusTransform n 1 0 (-1) 1 hp (by rwa [h]), h,
    one_mul, add_zero]

/-- Root-factor form of the Möbius transform of a split polynomial of exact degree `n`: the root
`r` becomes the linear factor `(a - r c) X + (b - r d)`. -/
theorem mobiusTransform_eq_rootFactorProduct {K : Type*} [Field K] (a b c d : K) {p : K[X]}
    (hp : p.Splits) (hdeg : p.natDegree = n) :
    mobiusTransform n a b c d p =
      C p.leadingCoeff *
        (p.roots.map (fun r => C (a - r * c) * X + C (b - r * d))).prod := by
  have hcard : p.roots.card = n := by
    rw [← hp.natDegree_eq_card_roots, hdeg]
  have h1 : p.homogenize n = MvPolynomial.C p.leadingCoeff *
      (p.roots.map (fun r =>
        MvPolynomial.X 0 - MvPolynomial.C r * MvPolynomial.X 1)).prod := by
    conv_lhs => rw [hp.eq_prod_roots]
    rw [Polynomial.homogenize_C_mul, ← hcard, Polynomial.homogenize_rootFactorProduct]
  rw [mobiusTransform, h1, map_mul, map_multiset_prod, Multiset.map_map]
  congr 1
  · simp
  · refine congrArg Multiset.prod (Multiset.map_congr rfl fun r _ => ?_)
    simp only [Function.comp_apply, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_eq]
    ring

/-- Root-factor form in a degree box `n ≥ natDegree p`: the extra factor `(c X + d)^(n - deg p)`
records the roots at infinity. -/
theorem mobiusTransform_eq_rootFactorProduct_mul {K : Type*} [Field K] (a b c d : K)
    {p : K[X]} (hp : p.Splits) (hdeg : p.natDegree ≤ n) :
    mobiusTransform n a b c d p =
      C p.leadingCoeff * (p.roots.map (fun r => C (a - r * c) * X + C (b - r * d))).prod *
        (C c * X + C d) ^ (n - p.natDegree) := by
  rw [mobiusTransform, homogenize_eq_homogenize_natDegree_mul_X_one_pow hdeg, map_mul, map_pow]
  have hx1 : MvPolynomial.aeval (![C a * X + C b, C c * X + C d] : Fin 2 → K[X])
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = C c * X + C d := by simp
  rw [hx1]
  change mobiusTransform p.natDegree a b c d p * _ = _
  rw [mobiusTransform_eq_rootFactorProduct _ a b c d hp rfl]

/-- The Möbius transform of a split polynomial splits in every degree box containing it. -/
theorem Splits.mobiusTransform {K : Type*} [Field K] (a b c d : K) {p : K[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree ≤ n) : (mobiusTransform n a b c d p).Splits := by
  rw [mobiusTransform_eq_rootFactorProduct_mul n a b c d hp hdeg]
  refine ((Splits.C _).mul (Splits.multisetProd fun f hf => ?_)).mul
    ((Splits.of_natDegree_le_one (by compute_degree)).pow _)
  obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hf
  exact Splits.of_natDegree_le_one (by compute_degree)

/-- Counting the elements of a multiset not satisfying `P`. -/
private theorem sum_map_ite_one {K : Type*} (P : K → Prop) [DecidablePred P] (m : Multiset K) :
    (m.map fun r => if P r then 0 else 1).sum = Multiset.card m - Multiset.card (m.filter P) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons r m ih =>
    have hle : Multiset.card (m.filter P) ≤ Multiset.card m :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    by_cases hr : P r
    · simp [hr, ih]
    · simp [hr, ih]; lia

open scoped Classical in
/-- If `a d - b c ≠ 0`, the transform of a nonzero split polynomial of exact degree `n` has
degree `n` minus the number of roots `r` of `p` with `a = r c`.  (A root with `a = r c` is sent to
infinity.) -/
theorem natDegree_mobiusTransform_eq {K : Type*} [Field K] (a b c d : K) {p : K[X]}
    (hp : p.Splits) (hp0 : p ≠ 0) (hdeg : p.natDegree = n) (hdet : a * d - b * c ≠ 0) :
    (mobiusTransform n a b c d p).natDegree =
      n - Multiset.card (p.roots.filter fun r => a - r * c = 0) := by
  have hf : ∀ r : K, C (a - r * c) * X + C (b - r * d) ≠ 0 := by
    intro r h
    have h1 : a - r * c = 0 := by simpa using congrArg (fun q => q.coeff 1) h
    have h0 : b - r * d = 0 := by simpa using congrArg (fun q => q.coeff 0) h
    exact hdet (by linear_combination d * h1 - c * h0)
  rw [mobiusTransform_eq_rootFactorProduct n a b c d hp hdeg,
    natDegree_C_mul (leadingCoeff_ne_zero.2 hp0),
    natDegree_multiset_prod _ (fun h0 => by
      obtain ⟨r, _, hr⟩ := Multiset.mem_map.1 h0
      exact hf r hr),
    Multiset.map_map]
  have : ((fun f : K[X] => f.natDegree) ∘ fun r => C (a - r * c) * X + C (b - r * d)) =
      fun r => if a - r * c = 0 then 0 else 1 := by
    funext r
    by_cases h : a - r * c = 0
    · simp only [Function.comp_apply, h, C_0, zero_mul, zero_add, natDegree_C, ite_true]
    · simp only [Function.comp_apply, h, ite_false]
      exact natDegree_linear h
  rw [this, sum_map_ite_one, ← hp.natDegree_eq_card_roots, hdeg]

/-- If `c ≠ 0` and `a d - b c ≠ 0`, the transform of a nonzero split polynomial of exact degree
`n` has degree `n - rootMultiplicity (a / c) p`. -/
theorem natDegree_mobiusTransform_eq_of_ne_zero {K : Type*} [Field K] (a b c d : K) {p : K[X]}
    (hp : p.Splits) (hp0 : p ≠ 0) (hdeg : p.natDegree = n) (hdet : a * d - b * c ≠ 0)
    (hc : c ≠ 0) :
    (mobiusTransform n a b c d p).natDegree = n - p.rootMultiplicity (a / c) := by
  classical
  have hiff : ∀ r : K, a - r * c = 0 ↔ r = a / c := fun r => by
    rw [eq_div_iff hc]
    constructor <;> intro h <;> linear_combination (-1 : K) * h
  rw [natDegree_mobiusTransform_eq n a b c d hp hp0 hdeg hdet, ← count_roots,
    Multiset.count_eq_card_filter_eq]
  congr 2
  exact Multiset.filter_congr fun r _ => by rw [hiff, eq_comm]

/-- If `c = 0` and `a d - b c ≠ 0`, the transform of a nonzero split polynomial of exact degree
`n` has degree `n`. -/
theorem natDegree_mobiusTransform_eq_of_eq_zero {K : Type*} [Field K] (a b d : K) {p : K[X]}
    (hp : p.Splits) (hp0 : p ≠ 0) (hdeg : p.natDegree = n) (hdet : a * d - b * 0 ≠ 0) :
    (mobiusTransform n a b 0 d p).natDegree = n := by
  have ha : a ≠ 0 := by rintro rfl; simp at hdet
  rw [natDegree_mobiusTransform_eq n a b 0 d hp hp0 hdeg hdet]
  simp [ha]

/-- The top coefficient of the transform with matrix `(1, 0; 1, 1)` is the value at `1`:
`(coeff n) ((1 + X)^n p (X / (1 + X))) = p (1)` for `natDegree p ≤ n`. -/
theorem coeff_mobiusTransform_one_zero_one_one {p : R[X]} (hp : p.natDegree ≤ n) :
    (mobiusTransform n 1 0 1 1 p).coeff n = p.eval 1 := by
  rw [mobiusTransform_eq_sum n _ _ _ _ hp, finsetSum_coeff,
    eval_eq_sum_range' (n := n + 1) (by lia)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [map_one, map_zero, one_mul, add_zero, one_pow, mul_one, coeff_C_mul]
  simp [coeff_X_pow_mul', hk', coeff_X_add_one_pow]

/-- The transform with matrix `(1, 0; 1, 1)` undoes the Cayley transform in degree `n`:
`(1 + X)^n * ((1 - X)^n * p (X / (1 - X))) (X / (1 + X)) = p`. -/
theorem mobiusTransform_one_zero_one_one_cayleyTransform {p : R[X]} (hp : p.natDegree ≤ n) :
    mobiusTransform n 1 0 1 1 (cayleyTransform n p) = p := by
  rw [cayleyTransform_eq_mobiusTransform, mobiusTransform_mobiusTransform n 1 0 1 1 1 0 (-1) 1 hp]
  convert mobiusTransform_one_zero_zero_one n hp using 2 <;> ring

/-- The Cayley transform undoes the transform with matrix `(1, 0; 1, 1)` in degree `n`. -/
theorem cayleyTransform_mobiusTransform_one_zero_one_one {p : R[X]} (hp : p.natDegree ≤ n) :
    cayleyTransform n (mobiusTransform n 1 0 1 1 p) = p := by
  rw [cayleyTransform_eq_mobiusTransform, mobiusTransform_mobiusTransform n 1 0 (-1) 1 1 0 1 1 hp]
  convert mobiusTransform_one_zero_zero_one n hp using 2 <;> ring

/-- The Cayley transform of a nonzero split polynomial of exact degree `n` has degree `n` minus
the multiplicity of the root `-1`: the root `-1` is sent to infinity. -/
theorem natDegree_cayleyTransform_eq {K : Type*} [Field K] {p : K[X]} (hp : p.Splits)
    (hp0 : p ≠ 0) (hdeg : p.natDegree = n) :
    (cayleyTransform n p).natDegree = n - p.rootMultiplicity (-1) := by
  rw [cayleyTransform_eq_mobiusTransform,
    natDegree_mobiusTransform_eq_of_ne_zero n 1 0 (-1) 1 hp hp0 hdeg (by simp) (by simp)]
  simp

end Polynomial
