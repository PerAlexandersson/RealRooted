module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Derivative products

For a weight polynomial `w` and a coefficient sequence `c`, the *derivative product* of two real
polynomials `f` and `g` is

`derivProduct w c f g = ∑ k, c k * w ^ k * f ^ (k) * g ^ (k)`,

where `f ^ (k)` denotes the `k`th derivative.  Such products were studied by Brändén, *On linear
transformations preserving the Pólya frequency property*, Theorem 3.11 (for a quadratic or linear
weight and a multiplier sequence `c`).  This file collects the algebra which does not depend on
associativity: bilinearity, commutativity, the unit and `X`-actions, and the exact degree and
leading coefficient when `w` is quadratic.

Poisson products (`w = X`) and the diamond product (`w = X * (X + 1)`) are instances; see
`RealRooted.DerivativeProduct.Associative` for the associative family.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted

noncomputable section

/-- The derivative product `∑ k, c k * w ^ k * f ^ (k) * g ^ (k)` with weight `w` and
coefficients `c`.

The sum is truncated at the degree of the left input.  Terms beyond the degree of either input
vanish, see `derivProduct_eq_sum_range`. -/
def derivProduct (w : ℝ[X]) (c : ℕ → ℝ) (f g : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (f.natDegree + 1),
    C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g

variable {w : ℝ[X]} {c : ℕ → ℝ}

/-- The defining sum for `derivProduct` may be enlarged beyond the degree of its left input. -/
theorem derivProduct_eq_sum_range {f : ℝ[X]} {N : ℕ} (hfN : f.natDegree < N) (g : ℝ[X]) :
    derivProduct w c f g =
      ∑ k ∈ range N, C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g := by
  rw [derivProduct]
  refine Finset.sum_subset (Finset.range_subset_range.mpr ?_) ?_
  · exact Nat.succ_le_iff.mpr hfN
  · intro k hkN hkf
    simp only [Finset.mem_range] at hkN hkf
    have hdeg : f.natDegree < k := by lia
    rw [iterate_derivative_eq_zero hdeg, mul_zero, zero_mul]

/-- Derivative products are symmetric. -/
theorem derivProduct_comm (w : ℝ[X]) (c : ℕ → ℝ) (f g : ℝ[X]) :
    derivProduct w c f g = derivProduct w c g f := by
  rw [derivProduct_eq_sum_range (N := max (f.natDegree + 1) (g.natDegree + 1))
      ((Nat.lt_succ_self f.natDegree).trans_le (le_max_left _ _)),
    derivProduct_eq_sum_range (N := max (f.natDegree + 1) (g.natDegree + 1))
      ((Nat.lt_succ_self g.natDegree).trans_le (le_max_right _ _))]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- `derivProduct` is additive in its right input. -/
theorem derivProduct_add_right (w : ℝ[X]) (c : ℕ → ℝ) (f g h : ℝ[X]) :
    derivProduct w c f (g + h) = derivProduct w c f g + derivProduct w c f h := by
  simp only [derivProduct, iterate_map_add, mul_add, Finset.sum_add_distrib]

/-- `derivProduct` is additive in its left input. -/
theorem derivProduct_add_left (w : ℝ[X]) (c : ℕ → ℝ) (f g h : ℝ[X]) :
    derivProduct w c (f + g) h = derivProduct w c f h + derivProduct w c g h := by
  rw [derivProduct_comm, derivProduct_add_right, derivProduct_comm w c h f,
    derivProduct_comm w c h g]

/-- `derivProduct` commutes with multiplication of its right input by a constant. -/
theorem derivProduct_C_mul_right (w : ℝ[X]) (c : ℕ → ℝ) (a : ℝ) (f g : ℝ[X]) :
    derivProduct w c f (C a * g) = C a * derivProduct w c f g := by
  rw [derivProduct, derivProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [iterate_derivative_C_mul]
  ring

/-- `derivProduct` commutes with multiplication of its left input by a constant. -/
theorem derivProduct_C_mul_left (w : ℝ[X]) (c : ℕ → ℝ) (a : ℝ) (f g : ℝ[X]) :
    derivProduct w c (C a * f) g = C a * derivProduct w c f g := by
  rw [derivProduct_comm, derivProduct_C_mul_right, derivProduct_comm w c g f]

/-- The zero polynomial is a right annihilator. -/
@[simp] theorem derivProduct_zero_right (w : ℝ[X]) (c : ℕ → ℝ) (f : ℝ[X]) :
    derivProduct w c f 0 = 0 := by
  simp only [derivProduct, iterate_map_zero, mul_zero, Finset.sum_const_zero]

/-- The zero polynomial is a left annihilator. -/
@[simp] theorem derivProduct_zero_left (w : ℝ[X]) (c : ℕ → ℝ) (g : ℝ[X]) :
    derivProduct w c 0 g = 0 := by
  rw [derivProduct_comm, derivProduct_zero_right]

/-- Left derivative multiplication as a real-linear map. -/
def derivProductLinearMap (w : ℝ[X]) (c : ℕ → ℝ) (f : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := derivProduct w c f
  map_add' := derivProduct_add_right w c f
  map_smul' a g := by
    rw [smul_eq_C_mul, smul_eq_C_mul, derivProduct_C_mul_right]
    simp only [RingHom.id_apply]

@[simp] theorem derivProductLinearMap_apply (w : ℝ[X]) (c : ℕ → ℝ) (f g : ℝ[X]) :
    derivProductLinearMap w c f g = derivProduct w c f g :=
  rfl

/-- Multiplying by the constant `1` multiplies by `c 0`. -/
theorem derivProduct_one_right (w : ℝ[X]) (c : ℕ → ℝ) (f : ℝ[X]) :
    derivProduct w c f 1 = C (c 0) * f := by
  rw [derivProduct, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro k _
    have hdeg : (1 : ℝ[X]).natDegree < k + 1 := by simp
    rw [iterate_derivative_eq_zero hdeg, mul_zero]

/-- Multiplying by the constant `1` multiplies by `c 0`. -/
theorem derivProduct_one_left (w : ℝ[X]) (c : ℕ → ℝ) (g : ℝ[X]) :
    derivProduct w c 1 g = C (c 0) * g := by
  rw [derivProduct_comm, derivProduct_one_right]

/-- If `c 0 = 1`, the constant `1` is a right unit. -/
theorem derivProduct_one_right_of_zero_eq_one (hc : c 0 = 1) (f : ℝ[X]) :
    derivProduct w c f 1 = f := by
  rw [derivProduct_one_right, hc, map_one, one_mul]

/-- If `c 0 = 1`, the constant `1` is a left unit. -/
theorem derivProduct_one_left_of_zero_eq_one (hc : c 0 = 1) (g : ℝ[X]) :
    derivProduct w c 1 g = g := by
  rw [derivProduct_one_left, hc, map_one, one_mul]

/-- A constant left factor multiplies by `c 0` times the constant. -/
theorem derivProduct_C_left (w : ℝ[X]) (c : ℕ → ℝ) (a : ℝ) (g : ℝ[X]) :
    derivProduct w c (C a) g = C (c 0 * a) * g := by
  rw [show (C a : ℝ[X]) = C a * 1 by rw [mul_one], derivProduct_C_mul_left,
    derivProduct_one_left, ← mul_assoc, ← map_mul, mul_comm a]

/-- The action of `X` from the left: `X ⋆ g = X * g + c 1 * w * g'` when `c 0 = 1`. -/
theorem derivProduct_X_left (hc : c 0 = 1) (g : ℝ[X]) :
    derivProduct w c X g = X * g + C (c 1) * w * derivative g := by
  rw [derivProduct, natDegree_X, Finset.sum_range_succ, Finset.sum_range_one]
  simp [hc]

/-- The action of `X` from the right: `f ⋆ X = X * f + c 1 * w * f'` when `c 0 = 1`. -/
theorem derivProduct_X_right (hc : c 0 = 1) (f : ℝ[X]) :
    derivProduct w c f X = X * f + C (c 1) * w * derivative f := by
  rw [derivProduct_comm, derivProduct_X_left hc]

/-! ## Degree and leading coefficient

For a quadratic weight `w = A * X ^ 2 + B * X + C₀`, every summand of `derivProduct w c f g`
has degree at most `m + n`, where `m` and `n` are the degrees of `f` and `g`, and the coefficient
of `X ^ (m + n)` is `lc f * lc g * ∑ k, c k * A ^ k * m₍k₎ * n₍k₎` with falling factorials
`m₍k₎`.  -/

/-- The factor `∑ k, c k * A ^ k * m₍k₎ * n₍k₎` in the leading coefficient of a derivative
product of polynomials of degrees `m` and `n`, with `A` the coefficient of `X ^ 2` in the
weight. -/
def derivProductLeadingFactor (A : ℝ) (c : ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), c k * A ^ k * ((m.descFactorial k : ℝ) * (n.descFactorial k : ℝ))

private theorem natDegree_term_le (hw : w.natDegree ≤ 2) {f g : ℝ[X]} {k : ℕ}
    (hk : k ≤ f.natDegree) :
    (C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g).natDegree ≤
      f.natDegree + g.natDegree := by
  by_cases hkg : k ≤ g.natDegree
  · have h1 : (C (c k) * w ^ k).natDegree ≤ k * 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le k hw)
    have h := natDegree_mul_le_of_le (natDegree_mul_le_of_le h1 (natDegree_iterate_derivative f k))
      (natDegree_iterate_derivative g k)
    exact h.trans (by lia)
  · have hdeg : g.natDegree < k := by lia
    rw [iterate_derivative_eq_zero hdeg, mul_zero, natDegree_zero]
    exact Nat.zero_le _

private theorem coeff_term (hw : w.natDegree ≤ 2) {f g : ℝ[X]} {k : ℕ}
    (hk : k ≤ f.natDegree) :
    (C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g).coeff
        (f.natDegree + g.natDegree) =
      f.leadingCoeff * g.leadingCoeff *
        (c k * w.coeff 2 ^ k *
          ((f.natDegree.descFactorial k : ℝ) * (g.natDegree.descFactorial k : ℝ))) := by
  by_cases hkg : k ≤ g.natDegree
  · have h1 : (C (c k) * w ^ k).natDegree ≤ k * 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le k hw)
    have h2 := natDegree_iterate_derivative f k
    have h3 := natDegree_iterate_derivative g k
    have hF : ((derivative^[k]) f).coeff (f.natDegree - k) =
        (f.natDegree.descFactorial k : ℝ) * f.leadingCoeff := by
      rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    have hG : ((derivative^[k]) g).coeff (g.natDegree - k) =
        (g.natDegree.descFactorial k : ℝ) * g.leadingCoeff := by
      rw [coeff_iterate_derivative, Nat.sub_add_cancel hkg, nsmul_eq_mul, coeff_natDegree]
    have e : f.natDegree + g.natDegree =
        (k * 2 + (f.natDegree - k)) + (g.natDegree - k) := by lia
    rw [e, coeff_mul_add_eq_of_natDegree_le (natDegree_mul_le_of_le h1 h2) h3,
      coeff_mul_add_eq_of_natDegree_le h1 h2, coeff_C_mul, coeff_pow_of_natDegree_le hw, hF, hG]
    ring
  · have hdeg : g.natDegree < k := by lia
    rw [iterate_derivative_eq_zero hdeg, mul_zero, coeff_zero,
      Nat.descFactorial_eq_zero_iff_lt.mpr hdeg]
    simp

/-- The degree of a derivative product with a quadratic weight is at most the sum of the input
degrees. -/
theorem natDegree_derivProduct_le (hw : w.natDegree ≤ 2) (f g : ℝ[X]) :
    (derivProduct w c f g).natDegree ≤ f.natDegree + g.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact natDegree_term_le hw (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- The coefficient of `X ^ (m + n)` in a derivative product with a quadratic weight. -/
theorem coeff_derivProduct_natDegree_add (hw : w.natDegree ≤ 2) (f g : ℝ[X]) :
    (derivProduct w c f g).coeff (f.natDegree + g.natDegree) =
      f.leadingCoeff * g.leadingCoeff *
        derivProductLeadingFactor (w.coeff 2) c f.natDegree g.natDegree := by
  rw [derivProduct, finsetSum_coeff, derivProductLeadingFactor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  exact coeff_term hw (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- The leading-coefficient factor is at least `1` for nonnegative coefficients with `c 0 = 1`
and a nonnegative `X ^ 2`-coefficient. -/
theorem one_le_derivProductLeadingFactor {A : ℝ} (hA : 0 ≤ A) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) (m n : ℕ) :
    1 ≤ derivProductLeadingFactor A c m n := by
  unfold derivProductLeadingFactor
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun k ↦ c k * A ^ k * ((m.descFactorial k : ℝ) * (n.descFactorial k : ℝ)))
    (fun k _ ↦ mul_nonneg (mul_nonneg (hc k) (pow_nonneg hA k))
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (Finset.mem_range.mpr (Nat.succ_pos m)))
  simp [hc0]

/-- The degree of a derivative product of nonzero polynomials is the sum of their degrees, for a
quadratic weight with nonnegative leading coefficient and nonnegative weights `c k` with
`c 0 = 1`. -/
theorem natDegree_derivProduct (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (derivProduct w c f g).natDegree = f.natDegree + g.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_derivProduct_le hw f g) ?_
  rw [coeff_derivProduct_natDegree_add hw]
  have h := one_le_derivProductLeadingFactor hA hc0 hc f.natDegree g.natDegree
  exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hg))
    (lt_of_lt_of_le one_pos h).ne'

/-- The leading coefficient of a derivative product of nonzero polynomials. -/
theorem leadingCoeff_derivProduct (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (derivProduct w c f g).leadingCoeff =
      f.leadingCoeff * g.leadingCoeff *
        derivProductLeadingFactor (w.coeff 2) c f.natDegree g.natDegree := by
  rw [leadingCoeff, natDegree_derivProduct hw hA hc0 hc hf hg,
    coeff_derivProduct_natDegree_add hw]

/-- The leading coefficient of a derivative product of nonzero polynomials is positive when
those of the factors are. -/
theorem leadingCoeff_derivProduct_pos (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2)
    (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfp : 0 < f.leadingCoeff) (hgp : 0 < g.leadingCoeff) :
    0 < (derivProduct w c f g).leadingCoeff := by
  rw [leadingCoeff_derivProduct hw hA hc0 hc hf hg]
  have h := one_le_derivProductLeadingFactor hA hc0 hc f.natDegree g.natDegree
  exact mul_pos (mul_pos hfp hgp) (lt_of_lt_of_le one_pos h)

/-- A derivative product of nonzero polynomials is nonzero (quadratic weight, nonnegative data). -/
theorem derivProduct_ne_zero (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    derivProduct w c f g ≠ 0 := by
  refine leadingCoeff_ne_zero.mp ?_
  rw [leadingCoeff_derivProduct hw hA hc0 hc hf hg]
  have h := one_le_derivProductLeadingFactor hA hc0 hc f.natDegree g.natDegree
  exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hg))
    (lt_of_lt_of_le one_pos h).ne'

/-- The leading-coefficient factor of `X ⋆ f`, where `f` has degree `n`, is `1 + c 1 * A * n`. -/
theorem derivProductLeadingFactor_one_left (A : ℝ) (c : ℕ → ℝ) (hc : c 0 = 1) (n : ℕ) :
    derivProductLeadingFactor A c 1 n = 1 + c 1 * A * n := by
  unfold derivProductLeadingFactor
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [hc]

end

end RealRooted
