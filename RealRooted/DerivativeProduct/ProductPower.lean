module

public import RealRooted.DerivativeProduct.Associative
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import Mathlib.Tactic

/-!
# Product powers and the sequence map `S_g`

For a derivative product `⋆ = derivProduct w c` and a polynomial `g`, the *product powers* are
`g^{⋆0} = 1` and `g^{⋆(n+1)} = g ⋆ g^{⋆n}` (`derivProductPow`), and the *product-power map* is the
linear map `S_g` with `S_g(X ^ n) = g^{⋆n}` (`derivProductPowMap`).  It is the basis transform of
the orbit `n ↦ L_g ^ n 1` of left multiplication `L_g` by `g`, hence `S_g p = p(L_g) 1`.

Functional calculus: `S_g((X - r) * p) = (g - r) ⋆ S_g p` (`derivProductPowMap_X_sub_C_mul`), so
`S_g(∏ (X - r_i)) = (g - r_1) ⋆ ⋯ ⋆ (g - r_m)`; for an associative product, `S_g` is multiplicative:
`S_g (p * q) = S_g p ⋆ S_g q` (`derivProductPowMap_mul`).
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

variable {w : ℝ[X]} {c : ℕ → ℝ} {g : ℝ[X]}

/-- The product power `g^{⋆n}` for the derivative product `derivProduct w c`, defined by
`g^{⋆0} = 1` and `g^{⋆(n+1)} = g ⋆ g^{⋆n}`. -/
def derivProductPow (w : ℝ[X]) (c : ℕ → ℝ) (g : ℝ[X]) (n : ℕ) : ℝ[X] :=
  (derivProductLinearMap w c g ^ n) 1

@[simp] theorem derivProductPow_zero : derivProductPow w c g 0 = 1 := by
  simp [derivProductPow]

/-- Product powers satisfy `g^{⋆(n+1)} = g ⋆ g^{⋆n}`. -/
theorem derivProductPow_succ (n : ℕ) :
    derivProductPow w c g (n + 1) = derivProduct w c g (derivProductPow w c g n) := by
  simp [derivProductPow, pow_succ', Module.End.mul_apply]

/-- The first product power is `g` itself, when `c 0 = 1`. -/
@[simp] theorem derivProductPow_one (hc0 : c 0 = 1) : derivProductPow w c g 1 = g := by
  rw [derivProductPow_succ, derivProductPow_zero, derivProduct_one_right_of_zero_eq_one hc0]

/-- The product-power map `S_g`: the linear map sending `X ^ n` to `g^{⋆n}`. -/
def derivProductPowMap (w : ℝ[X]) (c : ℕ → ℝ) (g : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  basisTransformₗ (derivProductPow w c g)

@[simp] theorem derivProductPowMap_X_pow (n : ℕ) :
    derivProductPowMap w c g (X ^ n) = derivProductPow w c g n :=
  basisTransform_X_pow _ n

/-- `S_g` is evaluation of the input polynomial at left multiplication by `g`, applied to `1`. -/
theorem derivProductPowMap_eq_aeval (p : ℝ[X]) :
    derivProductPowMap w c g p = aeval (derivProductLinearMap w c g) p 1 :=
  basisTransform_iterate_eq_aeval_apply _ _ _

/-- `S_g` fixes constants. -/
@[simp] theorem derivProductPowMap_C (a : ℝ) : derivProductPowMap w c g (C a) = C a := by
  simp [derivProductPowMap, derivProductPow]

/-- `S_g` sends `1` to `1`. -/
theorem derivProductPowMap_one : derivProductPowMap w c g 1 = 1 := by
  simpa using derivProductPowMap_C (w := w) (c := c) (g := g) 1

/-- Multiplying the source by `X` multiplies the image by `g` under `⋆`. -/
theorem derivProductPowMap_X_mul (p : ℝ[X]) :
    derivProductPowMap w c g (X * p) = derivProduct w c g (derivProductPowMap w c g p) := by
  rw [derivProductPowMap_eq_aeval, derivProductPowMap_eq_aeval, map_mul, aeval_X,
    Module.End.mul_apply, derivProductLinearMap_apply]

/-- **Functional calculus for linear factors.**  Multiplying the source by `X - r` multiplies the
image by `g - r` under `⋆` (for `c 0 = 1`). -/
theorem derivProductPowMap_X_sub_C_mul (hc0 : c 0 = 1) (r : ℝ) (p : ℝ[X]) :
    derivProductPowMap w c g ((X - C r) * p) =
      derivProduct w c (g - C r) (derivProductPowMap w c g p) := by
  have h : g - C r = g + C (-r) := by rw [map_neg, sub_eq_add_neg]
  rw [sub_mul, map_sub, derivProductPowMap_X_mul, h, derivProduct_add_left,
    derivProduct_C_left, hc0, linearMap_C_mul, one_mul, map_neg]
  ring

/-- `S_g` sends the powers of a linear factor `(X - r) ^ n` to the product powers
`(g - r)^{⋆n}` (for `c 0 = 1`). -/
theorem derivProductPowMap_X_sub_C_pow (hc0 : c 0 = 1) (r : ℝ) (n : ℕ) :
    derivProductPowMap w c g ((X - C r) ^ n) = derivProductPow w c (g - C r) n := by
  induction n with
  | zero => simp [derivProductPowMap_one]
  | succ n ih =>
    rw [pow_succ', derivProductPowMap_X_sub_C_mul hc0, ih, derivProductPow_succ]

/-! ### Associative products -/

section Associative

variable (hc0 : c 0 = 1) (hassoc : ∀ f g h : ℝ[X], derivProduct w c (derivProduct w c f g) h =
  derivProduct w c f (derivProduct w c g h))
include hc0 hassoc

/-- For an associative product, the iterates of left multiplication by `g` are left
multiplication by the product powers. -/
theorem iterate_derivProductLinearMap_apply (n : ℕ) (h : ℝ[X]) :
    ((derivProductLinearMap w c g) ^ n) h = derivProduct w c (derivProductPow w c g n) h := by
  induction n with
  | zero => simp [derivProduct_one_left_of_zero_eq_one hc0]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, derivProductPow_succ, hassoc]
    rfl

/-- For an associative product, evaluating a polynomial `p` at left multiplication by `g` is left
multiplication by `S_g p`. -/
theorem aeval_derivProductLinearMap_apply (p h : ℝ[X]) :
    aeval (derivProductLinearMap w c g) p h = derivProduct w c (derivProductPowMap w c g p) h := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq, map_add, derivProduct_add_left]
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      iterate_derivProductLinearMap_apply hc0 hassoc]
    simp [derivProductPowMap, derivProduct_C_mul_left, smul_eq_C_mul]

/-- For an associative product, `S_g` is multiplicative: `S_g (p * q) = S_g p ⋆ S_g q`. -/
theorem derivProductPowMap_mul (p q : ℝ[X]) :
    derivProductPowMap w c g (p * q) =
      derivProduct w c (derivProductPowMap w c g p) (derivProductPowMap w c g q) := by
  rw [derivProductPowMap_eq_aeval, map_mul, Module.End.mul_apply,
    ← derivProductPowMap_eq_aeval q,
    aeval_derivProductLinearMap_apply hc0 hassoc]

/-- For an associative product, the product powers add: `g^{⋆(m+n)} = g^{⋆m} ⋆ g^{⋆n}`. -/
theorem derivProductPow_add (m n : ℕ) :
    derivProductPow w c g (m + n) = derivProduct w c (derivProductPow w c g m)
      (derivProductPow w c g n) := by
  rw [← derivProductPowMap_X_pow, ← derivProductPowMap_X_pow, ← derivProductPowMap_X_pow,
    pow_add, derivProductPowMap_mul hc0 hassoc]

end Associative

/-! ### Degrees of product powers -/

section Degree

variable (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k)
include hw hA hc0 hc

/-- Product powers of a nonzero polynomial are nonzero. -/
theorem derivProductPow_ne_zero (hg : g ≠ 0) (n : ℕ) : derivProductPow w c g n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [derivProductPow_succ]; exact derivProduct_ne_zero hw hA hc0 hc hg ih

/-- The product power `g^{⋆n}` of a nonzero polynomial has degree `n * deg g`. -/
theorem natDegree_derivProductPow (hg : g ≠ 0) (n : ℕ) :
    (derivProductPow w c g n).natDegree = n * g.natDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivProductPow_succ, natDegree_derivProduct hw hA hc0 hc hg
      (derivProductPow_ne_zero hw hA hc0 hc hg n), ih]
    ring

end Degree

/-- For a weight with vanishing `X ^ 2`-coefficient, the leading-coefficient factor is `1`
whenever `c 0 = 1`. -/
theorem derivProductLeadingFactor_zero_left (hc0 : c 0 = 1) (m n : ℕ) :
    derivProductLeadingFactor 0 c m n = 1 := by
  rw [derivProductLeadingFactor, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [hc0]
  · intro k _
    simp

/-- For a weight with vanishing `X ^ 2`-coefficient, the product power `g^{⋆n}` has leading
coefficient `lc(g) ^ n`. -/
theorem leadingCoeff_derivProductPow (hw : w.natDegree ≤ 2) (hA : w.coeff 2 = 0) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) (hg : g ≠ 0) (n : ℕ) :
    (derivProductPow w c g n).leadingCoeff = g.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivProductPow_succ, leadingCoeff_derivProduct hw hA.ge hc0 hc hg
      (derivProductPow_ne_zero hw hA.ge hc0 hc hg n), hA, derivProductLeadingFactor_zero_left hc0,
      ih, mul_one, pow_succ']

end

end RealRooted
