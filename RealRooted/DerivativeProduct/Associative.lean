module

public import RealRooted.DerivativeProduct.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# Associative derivative products

A derivative product `f ⋆ g = ∑ k, c k * w ^ k * f ^ (k) * g ^ (k)` with a quadratic weight
`w = A * X ^ 2 + B * X + C₀` is associative when `A ≥ 0` and
`c k = a ^ k / (k! * ∏ j < k, (1 + a * A * j))` (the classification of associative products
is formulated as issue #2369; here we prove sufficiency).

The proof follows the cyclic-vector argument: the *associator identity*

`(X ⋆ f) ⋆ g = X ⋆ (f ⋆ g)`

holds exactly when `(j + 1) * (1 + a * A * j) * c (j + 1) = a * c j` for all `j`, and the
polynomials `X ⋆ (X ⋆ ... ⋆ 1)` have exact degree `n` and positive leading coefficient, hence
span all polynomials.

The two families used later are `assocProduct` (general weight) and `betaProduct`, the diamond
family `f *_β g = ∑ k, (X * (X + 1)) ^ k / (k! * (β)_k) * f ^ (k) * g ^ (k)` of Brändén,
*On linear transformations preserving the Pólya frequency property*, with
`β = 1` the diamond product.  An affine substitution reduces `assocProduct` with a weight
having two distinct real roots and positive leading coefficient to `betaProduct`.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted

noncomputable section

variable {w : ℝ[X]} {c : ℕ → ℝ}

/-! ## The associator identity -/

private theorem derivative_derivative_of_natDegree_le_two (hw : w.natDegree ≤ 2) :
    derivative (derivative w) = C (2 * w.coeff 2) := by
  ext n
  rcases n with _ | n
  · rw [coeff_derivative, coeff_derivative, coeff_C_zero]
    change w.coeff 2 * (((1 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 1) = 2 * w.coeff 2
    push_cast
    ring
  · rw [coeff_derivative, coeff_derivative, coeff_C_succ,
      coeff_eq_zero_of_natDegree_lt (show w.natDegree < n + 1 + 1 + 1 by lia), zero_mul,
      zero_mul]

private theorem iterate_derivative_X_mul (f : ℝ[X]) (k : ℕ) :
    (derivative^[k]) (X * f) = X * (derivative^[k]) f + (k : ℝ[X]) * (derivative^[k - 1]) f := by
  rw [mul_comm X f, iterate_derivative_mul_X, nsmul_eq_mul]
  ring

private theorem derivative_coeff_mul_iterate (a : ℝ) (k : ℕ) (f : ℝ[X]) :
    derivative (C ((k : ℝ) * ((k : ℝ) - 1) * a) * (derivative^[k - 1]) f) =
      C ((k : ℝ) * ((k : ℝ) - 1) * a) * (derivative^[k]) f := by
  rcases k with _ | k
  · simp
  · rw [derivative_C_mul, Nat.add_sub_cancel, ← Function.iterate_succ_apply' derivative]

/-- Leibniz rule for `(w * f') ^ (k)` with a weight whose second derivative is constant. -/
private theorem iterate_derivative_mul_derivative (A : ℝ)
    (hw2 : derivative (derivative w) = C (2 * A)) (f : ℝ[X]) (k : ℕ) :
    (derivative^[k]) (w * derivative f) =
      w * (derivative^[k + 1]) f + (k : ℝ[X]) * derivative w * (derivative^[k]) f +
        C ((k : ℝ) * ((k : ℝ) - 1) * A) * (derivative^[k - 1]) f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply' derivative k (w * derivative f), ih, derivative_add,
      derivative_add, derivative_coeff_mul_iterate]
    simp only [derivative_mul, derivative_natCast, hw2, zero_mul, zero_add,
      ← Function.iterate_succ_apply' derivative, Nat.add_sub_cancel]
    push_cast
    simp only [map_mul, map_add, map_sub, map_one, map_natCast, map_ofNat]
    ring

private theorem iterate_derivative_X_mul_add (a A : ℝ)
    (hw2 : derivative (derivative w) = C (2 * A)) (f : ℝ[X]) (k : ℕ) :
    (derivative^[k]) (X * f + C a * w * derivative f) =
      X * (derivative^[k]) f + (k : ℝ[X]) * (derivative^[k - 1]) f +
        C a * (w * (derivative^[k + 1]) f + (k : ℝ[X]) * derivative w * (derivative^[k]) f +
          C ((k : ℝ) * ((k : ℝ) - 1) * A) * (derivative^[k - 1]) f) := by
  rw [mul_assoc (C a) w (derivative f), iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_mul, iterate_derivative_mul_derivative A hw2]

/-- The termwise form of the associator identity: the difference of the two sides is a
telescoping shift between the `f ^ (k - 1) g ^ (k)` and `f ^ (k) g ^ (k + 1)` terms. -/
private theorem associator_term (a A : ℝ) (f g : ℝ[X]) (k : ℕ) :
    C (c k) * w ^ k *
        (X * (derivative^[k]) f + (k : ℝ[X]) * (derivative^[k - 1]) f +
          C a * (w * (derivative^[k + 1]) f + (k : ℝ[X]) * derivative w * (derivative^[k]) f +
            C ((k : ℝ) * ((k : ℝ) - 1) * A) * (derivative^[k - 1]) f)) *
        (derivative^[k]) g =
      (X * (C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g) +
        C a * w * derivative (C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g)) +
      (C (c k * (k : ℝ) * (1 + a * ((k : ℝ) - 1) * A)) * w ^ k * (derivative^[k - 1]) f *
          (derivative^[k]) g -
        C (a * c k) * w ^ (k + 1) * (derivative^[k]) f * (derivative^[k + 1]) g) := by
  have lem : w * w ^ (k - 1) * (k : ℝ[X]) = w ^ k * (k : ℝ[X]) := by
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel]
      ring
  simp only [derivative_mul, derivative_C, derivative_pow, zero_mul, zero_add,
    ← Function.iterate_succ_apply' derivative, map_mul, map_add, map_sub, map_one, map_natCast]
  linear_combination
    (-(C a * C (c k) * derivative w * (derivative^[k]) f * (derivative^[k]) g)) * lem

private theorem sum_range_shift {U V : ℕ → ℝ[X]} (M : ℕ) (hU0 : U 0 = 0) (hVM : V M = 0)
    (h : ∀ j, U (j + 1) = V j) :
    ∑ k ∈ range (M + 1), U k = ∑ k ∈ range (M + 1), V k := by
  conv_lhs => rw [Finset.sum_range_succ']
  conv_rhs => rw [Finset.sum_range_succ]
  rw [hU0, hVM, add_zero, add_zero]
  exact Finset.sum_congr rfl fun j _ ↦ h j

private theorem sum_associator_defect (a A : ℝ)
    (hrec : ∀ j : ℕ, ((j : ℝ) + 1) * (1 + a * A * j) * c (j + 1) = a * c j)
    (f g : ℝ[X]) {M : ℕ} (hM : f.natDegree < M) :
    ∑ k ∈ range (M + 1),
        C (c k * (k : ℝ) * (1 + a * ((k : ℝ) - 1) * A)) * w ^ k * (derivative^[k - 1]) f *
          (derivative^[k]) g =
      ∑ k ∈ range (M + 1),
        C (a * c k) * w ^ (k + 1) * (derivative^[k]) f * (derivative^[k + 1]) g := by
  refine sum_range_shift M (by simp) ?_ fun j ↦ ?_
  · rw [iterate_derivative_eq_zero hM, mul_zero, zero_mul]
  · have hcoef : c (j + 1) * ((j + 1 : ℕ) : ℝ) * (1 + a * (((j + 1 : ℕ) : ℝ) - 1) * A) =
        a * c j := by
      push_cast
      linear_combination hrec j
    rw [hcoef, Nat.add_sub_cancel]

private theorem derivProduct_X_left_aux (hw : w.natDegree ≤ 2) (a A : ℝ)
    (hw2 : derivative (derivative w) = C (2 * A))
    (hrec : ∀ j : ℕ, ((j : ℝ) + 1) * (1 + a * A * j) * c (j + 1) = a * c j) (f g : ℝ[X]) :
    derivProduct w c (X * f + C a * w * derivative f) g =
      X * derivProduct w c f g + C a * w * derivative (derivProduct w c f g) := by
  obtain ⟨M, hM⟩ : ∃ M, M = f.natDegree + 2 := ⟨_, rfl⟩
  have hlt : (X * f + C a * w * derivative f).natDegree < M + 1 := by
    have h1 : (X * f).natDegree ≤ 1 + f.natDegree := natDegree_mul_le_of_le natDegree_X_le le_rfl
    have h2 : (C a * w * derivative f).natDegree ≤ 2 + f.natDegree :=
      natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans hw)
        ((natDegree_derivative_le f).trans (Nat.sub_le _ _))
    have h3 := natDegree_add_le_of_degree_le (h1.trans (by lia : 1 + f.natDegree ≤ M))
      (h2.trans (by lia : 2 + f.natDegree ≤ M))
    lia
  have hf : f.natDegree < M + 1 := by lia
  rw [derivProduct_eq_sum_range hlt, derivProduct_eq_sum_range hf, derivative_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  have key : ∀ k ∈ range (M + 1),
      C (c k) * w ^ k * (derivative^[k]) (X * f + C a * w * derivative f) * (derivative^[k]) g =
        (X * (C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g) +
          C a * w * derivative (C (c k) * w ^ k * (derivative^[k]) f * (derivative^[k]) g)) +
        (C (c k * (k : ℝ) * (1 + a * ((k : ℝ) - 1) * A)) * w ^ k * (derivative^[k - 1]) f *
            (derivative^[k]) g -
          C (a * c k) * w ^ (k + 1) * (derivative^[k]) f * (derivative^[k + 1]) g) :=
    fun k _ ↦ by
      rw [iterate_derivative_X_mul_add a A hw2 f k]
      exact associator_term a A f g k
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_associator_defect (M := M) a A hrec f g (by lia), sub_self, add_zero]

/-- The associator identity `(X ⋆ f) ⋆ g = X ⋆ (f ⋆ g)` for a quadratic weight, provided the
coefficients satisfy `(j + 1) * (1 + c 1 * A * j) * c (j + 1) = c 1 * c j`, where `A` is the
coefficient of `X ^ 2` in the weight. -/
theorem derivProduct_assoc_X_left (hw : w.natDegree ≤ 2) (hc0 : c 0 = 1)
    (hrec : ∀ j : ℕ, ((j : ℝ) + 1) * (1 + c 1 * w.coeff 2 * j) * c (j + 1) = c 1 * c j)
    (f g : ℝ[X]) :
    derivProduct w c (derivProduct w c X f) g = derivProduct w c X (derivProduct w c f g) := by
  rw [derivProduct_X_left hc0 f, derivProduct_X_left hc0 (derivProduct w c f g)]
  exact derivProduct_X_left_aux hw (c 1) (w.coeff 2)
    (derivative_derivative_of_natDegree_le_two hw) hrec f g

/-! ## Associativity by the cyclic-vector argument -/

/-- The `n`th iterate of left multiplication by `X`, applied to `1`. -/
private def xPow (w : ℝ[X]) (c : ℕ → ℝ) (n : ℕ) : ℝ[X] := (derivProduct w c X)^[n] 1

private theorem xPow_succ (n : ℕ) :
    xPow w c (n + 1) = derivProduct w c X (xPow w c n) := by
  unfold xPow
  exact Function.iterate_succ_apply' _ _ _

private theorem xPow_spec (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) (n : ℕ) :
    xPow w c n ≠ 0 ∧ (xPow w c n).natDegree = n ∧ 0 < (xPow w c n).leadingCoeff := by
  induction n with
  | zero => simp [xPow]
  | succ n ih =>
    obtain ⟨hne, hdeg, hpos⟩ := ih
    rw [xPow_succ]
    have hX : (X : ℝ[X]) ≠ 0 := X_ne_zero
    refine ⟨derivProduct_ne_zero hw hA hc0 hc hX hne, ?_, ?_⟩
    · rw [natDegree_derivProduct hw hA hc0 hc hX hne, natDegree_X, hdeg]
      lia
    · exact leadingCoeff_derivProduct_pos hw hA hc0 hc hX hne (by simp) hpos

private theorem induction_xPow (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k) {P : ℝ[X] → Prop}
    (hadd : ∀ f g, P f → P g → P (f + g)) (hmul : ∀ (a : ℝ) f, P f → P (C a * f))
    (hx : ∀ n, P (xPow w c n)) (f : ℝ[X]) : P f := by
  have key : ∀ (n : ℕ) (f : ℝ[X]), f.natDegree ≤ n → P f := by
    intro n
    induction n with
    | zero =>
      intro f hf
      have h := hmul (f.coeff 0) _ (hx 0)
      have h1 : xPow w c 0 = 1 := rfl
      rw [h1, mul_one, ← eq_C_of_natDegree_le_zero hf] at h
      exact h
    | succ n ih =>
      intro f hf
      have hxn := hx (n + 1)
      obtain ⟨hne, hdeg, hpos⟩ := xPow_spec hw hA hc0 hc (n + 1)
      generalize xPow w c (n + 1) = p at hxn hne hdeg hpos
      have hp : p.coeff (n + 1) = p.leadingCoeff := by rw [leadingCoeff, hdeg]
      have hf1 : (f - C (f.coeff (n + 1) / p.leadingCoeff) * p).natDegree ≤ n := by
        have h1 : (f - C (f.coeff (n + 1) / p.leadingCoeff) * p).natDegree ≤ n + 1 :=
          (natDegree_sub_le _ _).trans (max_le hf ((natDegree_C_mul_le _ _).trans hdeg.le))
        have h2 : (f - C (f.coeff (n + 1) / p.leadingCoeff) * p).coeff (n + 1) = 0 := by
          have h3 : f.coeff (n + 1) / p.leadingCoeff * p.leadingCoeff = f.coeff (n + 1) :=
            div_mul_cancel₀ _ hpos.ne'
          rw [coeff_sub, coeff_C_mul, hp, h3, sub_self]
        have h4 := natDegree_le_pred h1 h2
        rwa [Nat.add_sub_cancel] at h4
      have hdecomp : f = (f - C (f.coeff (n + 1) / p.leadingCoeff) * p) +
          C (f.coeff (n + 1) / p.leadingCoeff) * p := by ring
      rw [hdecomp]
      exact hadd _ _ (ih _ hf1) (hmul _ _ hxn)
  exact key f.natDegree f le_rfl

/-- Associativity of a derivative product with a quadratic weight of nonnegative leading
coefficient and coefficients `c k ≥ 0`, `c 0 = 1`, satisfying the recurrence
`(j + 1) * (1 + c 1 * A * j) * c (j + 1) = c 1 * c j`. -/
theorem derivProduct_assoc (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1)
    (hc : ∀ k, 0 ≤ c k)
    (hrec : ∀ j : ℕ, ((j : ℝ) + 1) * (1 + c 1 * w.coeff 2 * j) * c (j + 1) = c 1 * c j)
    (f g h : ℝ[X]) :
    derivProduct w c (derivProduct w c f g) h = derivProduct w c f (derivProduct w c g h) := by
  have hX := derivProduct_assoc_X_left hw hc0 hrec
  have hall : ∀ f : ℝ[X], ∀ g h : ℝ[X],
      derivProduct w c (derivProduct w c f g) h = derivProduct w c f (derivProduct w c g h) := by
    intro f
    refine induction_xPow hw hA hc0 hc (P := fun f ↦ ∀ g h : ℝ[X],
      derivProduct w c (derivProduct w c f g) h = derivProduct w c f (derivProduct w c g h))
      ?_ ?_ ?_ f
    · intro f₁ f₂ h₁ h₂ g h
      simp only [derivProduct_add_left, h₁ g h, h₂ g h]
    · intro a f₁ h₁ g h
      simp only [derivProduct_C_mul_left, h₁ g h]
    · intro n
      induction n with
      | zero =>
        intro g h
        have h1 : xPow w c 0 = 1 := rfl
        rw [h1, derivProduct_one_left_of_zero_eq_one hc0, derivProduct_one_left_of_zero_eq_one hc0]
      | succ n ih =>
        intro g h
        rw [xPow_succ, hX (xPow w c n) g, hX (derivProduct w c (xPow w c n) g) h, ih g h,
          ← hX (xPow w c n) (derivProduct w c g h)]
  exact hall f g h

/-! ## The coefficient family `assocCoeff` and the products `assocProduct` -/

/-- The coefficients `a ^ k / (k! * ∏ j < k, (1 + a * A * j))` of an associative derivative
product with weight having `X ^ 2`-coefficient `A`. -/
def assocCoeff (a A : ℝ) (k : ℕ) : ℝ :=
  a ^ k / ((k.factorial : ℝ) * ∏ j ∈ range k, (1 + a * A * j))

@[simp] theorem assocCoeff_zero (a A : ℝ) : assocCoeff a A 0 = 1 := by
  simp [assocCoeff]

@[simp] theorem assocCoeff_one (a A : ℝ) : assocCoeff a A 1 = a := by
  simp [assocCoeff]

/-- The successor recurrence for `assocCoeff`. -/
theorem assocCoeff_succ (a A : ℝ) (k : ℕ) :
    assocCoeff a A (k + 1) = a * assocCoeff a A k / (((k : ℝ) + 1) * (1 + a * A * k)) := by
  unfold assocCoeff
  rw [Finset.prod_range_succ, Nat.factorial_succ, mul_div_assoc', div_div]
  push_cast
  congr 1
  · ring
  · ring

theorem assocCoeff_nonneg {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (k : ℕ) :
    0 ≤ assocCoeff a A k := by
  unfold assocCoeff
  positivity

/-- The coefficients `assocCoeff` satisfy the recurrence of the associator identity. -/
theorem assocCoeff_recurrence {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (j : ℕ) :
    ((j : ℝ) + 1) * (1 + a * A * j) * assocCoeff a A (j + 1) = a * assocCoeff a A j := by
  have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (1 + a * A * j) ≠ 0 := by positivity
  rw [assocCoeff_succ a A j]
  field_simp

/-- The associative derivative product with parameter `a` and weight `w`. -/
def assocProduct (a : ℝ) (w : ℝ[X]) (f g : ℝ[X]) : ℝ[X] :=
  derivProduct w (assocCoeff a (w.coeff 2)) f g

theorem assocProduct_comm (a : ℝ) (w : ℝ[X]) (f g : ℝ[X]) :
    assocProduct a w f g = assocProduct a w g f :=
  derivProduct_comm _ _ f g

/-- Associativity of `assocProduct` for a quadratic weight with nonnegative leading
coefficient. -/
theorem assocProduct_assoc {a : ℝ} {w : ℝ[X]} (ha : 0 ≤ a) (hw : w.natDegree ≤ 2)
    (hA : 0 ≤ w.coeff 2) (f g h : ℝ[X]) :
    assocProduct a w (assocProduct a w f g) h = assocProduct a w f (assocProduct a w g h) := by
  have hc1 : assocCoeff a (w.coeff 2) 1 = a := assocCoeff_one _ _
  refine derivProduct_assoc hw hA (assocCoeff_zero _ _) (assocCoeff_nonneg ha hA) ?_ f g h
  intro j
  rw [hc1]
  exact assocCoeff_recurrence ha hA j

/-! ## The diamond family `betaProduct` -/

/-- The coefficients `1 / (k! * (β)_k)` of the diamond family, with rising Pochhammer symbol
`(β)_k = β (β + 1) ... (β + k - 1)`. -/
def betaCoeff (β : ℝ) (k : ℕ) : ℝ :=
  1 / ((k.factorial : ℝ) * (ascPochhammer ℝ k).eval β)

/-- The diamond family `f *_β g = ∑ k, (X * (X + 1)) ^ k / (k! * (β)_k) * f ^ (k) * g ^ (k)`;
`β = 1` is the diamond product. -/
def betaProduct (β : ℝ) (f g : ℝ[X]) : ℝ[X] :=
  derivProduct (X * (X + 1)) (betaCoeff β) f g

@[simp] theorem betaCoeff_zero (β : ℝ) : betaCoeff β 0 = 1 := by
  simp [betaCoeff]

@[simp] theorem betaCoeff_one (β : ℝ) : betaCoeff β 1 = β⁻¹ := by
  simp [betaCoeff]

/-- The successor recurrence for `betaCoeff`. -/
theorem betaCoeff_succ (β : ℝ) (k : ℕ) :
    betaCoeff β (k + 1) = betaCoeff β k / (((k : ℝ) + 1) * (β + k)) := by
  unfold betaCoeff
  rw [ascPochhammer_succ_eval, Nat.factorial_succ, div_div]
  push_cast
  congr 1
  ring

theorem betaCoeff_nonneg {β : ℝ} (hβ : 0 < β) (k : ℕ) : 0 ≤ betaCoeff β k :=
  div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (ascPochhammer_pos k β hβ).le)

/-- The recurrence of the associator identity for `betaCoeff`. -/
theorem betaCoeff_recurrence {β : ℝ} (hβ : 0 < β) (j : ℕ) :
    ((j : ℝ) + 1) * (1 + betaCoeff β 1 * 1 * j) * betaCoeff β (j + 1) =
      betaCoeff β 1 * betaCoeff β j := by
  have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h2 : β + j ≠ 0 := by positivity
  have h3 : β ≠ 0 := hβ.ne'
  rw [betaCoeff_succ β j, betaCoeff_one]
  field_simp

/-- For `β = 1`, the coefficients are `1 / (k!) ^ 2`. -/
theorem betaCoeff_one_param (k : ℕ) : betaCoeff 1 k = 1 / (k.factorial : ℝ) ^ 2 := by
  unfold betaCoeff
  rw [ascPochhammer_eval_one]
  ring

private theorem natDegree_X_mul_X_add_one_le : (X * (X + 1) : ℝ[X]).natDegree ≤ 2 := by
  compute_degree

private theorem coeff_two_X_mul_X_add_one : (X * (X + 1) : ℝ[X]).coeff 2 = 1 := by
  have h : (X * (X + 1) : ℝ[X]) = X ^ 2 + X := by ring
  rw [h]
  simp [coeff_X_pow, coeff_X]

/-- The diamond product `f ⋄ g = ∑ k, [X (X + 1)] ^ k / (k!) ^ 2 * f ^ (k) * g ^ (k)`. -/
theorem betaProduct_one_eq (f g : ℝ[X]) :
    betaProduct 1 f g =
      derivProduct (X * (X + 1)) (fun k ↦ 1 / (k.factorial : ℝ) ^ 2) f g := by
  have h : betaCoeff 1 = fun k ↦ 1 / (k.factorial : ℝ) ^ 2 := funext betaCoeff_one_param
  rw [betaProduct, h]

theorem betaProduct_comm (β : ℝ) (f g : ℝ[X]) : betaProduct β f g = betaProduct β g f :=
  derivProduct_comm _ _ f g

theorem betaProduct_add_left (β : ℝ) (f g h : ℝ[X]) :
    betaProduct β (f + g) h = betaProduct β f h + betaProduct β g h :=
  derivProduct_add_left _ _ f g h

theorem betaProduct_add_right (β : ℝ) (f g h : ℝ[X]) :
    betaProduct β f (g + h) = betaProduct β f g + betaProduct β f h :=
  derivProduct_add_right _ _ f g h

theorem betaProduct_C_mul_left (β a : ℝ) (f g : ℝ[X]) :
    betaProduct β (C a * f) g = C a * betaProduct β f g :=
  derivProduct_C_mul_left _ _ a f g

theorem betaProduct_C_mul_right (β a : ℝ) (f g : ℝ[X]) :
    betaProduct β f (C a * g) = C a * betaProduct β f g :=
  derivProduct_C_mul_right _ _ a f g

theorem betaProduct_C_left (β a : ℝ) (g : ℝ[X]) : betaProduct β (C a) g = C a * g := by
  rw [betaProduct, derivProduct_C_left, betaCoeff_zero, one_mul]

@[simp] theorem betaProduct_one_left (β : ℝ) (g : ℝ[X]) : betaProduct β 1 g = g :=
  derivProduct_one_left_of_zero_eq_one (betaCoeff_zero β) g

@[simp] theorem betaProduct_one_right (β : ℝ) (f : ℝ[X]) : betaProduct β f 1 = f :=
  derivProduct_one_right_of_zero_eq_one (betaCoeff_zero β) f

/-- The action of `X` on the diamond family: `X *_β g = X * g + β⁻¹ * X * (X + 1) * g'`. -/
theorem betaProduct_X_left (β : ℝ) (g : ℝ[X]) :
    betaProduct β X g = X * g + C β⁻¹ * (X * (X + 1)) * derivative g := by
  rw [betaProduct, derivProduct_X_left (betaCoeff_zero β), betaCoeff_one]

/-- The associator identity `(X *_β f) *_β g = X *_β (f *_β g)` for `β > 0`. -/
theorem betaProduct_assoc_X_left {β : ℝ} (hβ : 0 < β) (f g : ℝ[X]) :
    betaProduct β (betaProduct β X f) g = betaProduct β X (betaProduct β f g) := by
  refine derivProduct_assoc_X_left natDegree_X_mul_X_add_one_le (betaCoeff_zero β) ?_ f g
  intro j
  rw [coeff_two_X_mul_X_add_one]
  exact betaCoeff_recurrence hβ j

/-- Associativity of the diamond family `*_β` for `β > 0` (Brändén, via the cyclic-vector
argument; see also `RealRooted.betaTransform_mul`). -/
theorem betaProduct_assoc {β : ℝ} (hβ : 0 < β) (f g h : ℝ[X]) :
    betaProduct β (betaProduct β f g) h = betaProduct β f (betaProduct β g h) := by
  refine derivProduct_assoc natDegree_X_mul_X_add_one_le
    (by rw [coeff_two_X_mul_X_add_one]; exact zero_le_one) (betaCoeff_zero β)
    (betaCoeff_nonneg hβ) ?_ f g h
  intro j
  rw [coeff_two_X_mul_X_add_one]
  exact betaCoeff_recurrence hβ j

/-! ## Affine normalization -/

private theorem iterate_derivative_comp_affine (b a : ℝ) (p : ℝ[X]) (k : ℕ) :
    (derivative^[k]) (p.comp (C b * X + C a)) =
      C (b ^ k) * ((derivative^[k]) p).comp (C b * X + C a) := by
  have hl : derivative (C b * X + C a : ℝ[X]) = C b := by simp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply' derivative k, ih, derivative_C_mul, derivative_comp, hl,
      Function.iterate_succ_apply' derivative k p, pow_succ, C_mul]
    ring

/-- An affine change of variable transforms a derivative product into the derivative product
of the transformed inputs, with weight `b⁻² * w(b X + a)`. -/
theorem derivProduct_comp_affine (w : ℝ[X]) (c : ℕ → ℝ) {b : ℝ} (hb : b ≠ 0) (a : ℝ)
    (f g : ℝ[X]) :
    (derivProduct w c f g).comp (C b * X + C a) =
      derivProduct (C (b⁻¹ ^ 2) * w.comp (C b * X + C a)) c (f.comp (C b * X + C a))
        (g.comp (C b * X + C a)) := by
  have hdeg : (f.comp (C b * X + C a)).natDegree < f.natDegree + 1 := by
    rw [natDegree_comp, natDegree_linear hb, mul_one]
    exact Nat.lt_succ_self _
  rw [derivProduct_eq_sum_range hdeg, derivProduct, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 : b⁻¹ ^ 2 * b * b = 1 := by field_simp
  have h2 : C ((b⁻¹ ^ 2) ^ k) * C (b ^ k) * C (b ^ k) = 1 := by
    rw [← C_mul, ← C_mul, ← C_1]
    congr 1
    rw [← mul_pow, ← mul_pow, h1, one_pow]
  rw [mul_comp, mul_comp, mul_comp, C_comp, pow_comp, iterate_derivative_comp_affine,
    iterate_derivative_comp_affine, mul_pow, ← C_pow]
  linear_combination
    (-(C (c k) * (w.comp (C b * X + C a)) ^ k * ((derivative^[k]) f).comp (C b * X + C a) *
      ((derivative^[k]) g).comp (C b * X + C a))) * h2

/-- Scaling the weight scales the coefficients geometrically. -/
theorem derivProduct_C_mul_weight (A : ℝ) (w : ℝ[X]) (c : ℕ → ℝ) (f g : ℝ[X]) :
    derivProduct (C A * w) c f g = derivProduct w (fun k ↦ A ^ k * c k) f g := by
  unfold derivProduct
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_pow, ← C_pow, C_mul]
  ring

/-- Reparametrization of `assocCoeff`: `A ^ k * assocCoeff a A k = assocCoeff (a * A) 1 k`. -/
theorem pow_mul_assocCoeff (a A : ℝ) (k : ℕ) :
    A ^ k * assocCoeff a A k = assocCoeff (a * A) 1 k := by
  unfold assocCoeff
  simp only [mul_one, mul_pow]
  ring

/-- The two coefficient families agree: `assocCoeff p 1 k = betaCoeff p⁻¹ k` for `p > 0`. -/
theorem assocCoeff_one_eq_betaCoeff {p : ℝ} (hp : 0 < p) (k : ℕ) :
    assocCoeff p 1 k = betaCoeff p⁻¹ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (1 + p * 1 * k) ≠ 0 := by positivity
    have h3 : p⁻¹ + k ≠ 0 := by positivity
    have h4 : p ≠ 0 := hp.ne'
    rw [assocCoeff_succ p 1 k, betaCoeff_succ p⁻¹ k, ih]
    field_simp

/-- **Affine normalization.** Let `w = A * (X - r) * (X - s)` with `A > 0` and `r ≠ s`, and `a > 0`.
Under the substitution `X ↦ (s - r) * X + s`, which sends the roots `-1, 0` of `X * (X + 1)`
to `r, s`, the product `assocProduct a w` becomes the diamond product `*_β` with
`β = (a * A)⁻¹`. -/
theorem assocProduct_comp_affine {a A r s : ℝ} (ha : 0 < a) (hA : 0 < A) (hrs : r ≠ s)
    (f g : ℝ[X]) :
    (assocProduct a (C A * ((X - C r) * (X - C s))) f g).comp (C (s - r) * X + C s) =
      betaProduct (a * A)⁻¹ (f.comp (C (s - r) * X + C s)) (g.comp (C (s - r) * X + C s)) := by
  have hd : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hcoeff : (C A * ((X - C r) * (X - C s)) : ℝ[X]).coeff 2 = A := by
    have h : (C A * ((X - C r) * (X - C s)) : ℝ[X]) =
        C A * X ^ 2 - C (A * (r + s)) * X + C (A * (r * s)) := by
      simp only [map_mul, map_add]
      ring
    rw [h]
    simp [coeff_X_pow]
  have hw : C ((s - r)⁻¹ ^ 2) * (C A * ((X - C r) * (X - C s))).comp (C (s - r) * X + C s) =
      C A * (X * (X + 1)) := by
    have h1 : C ((s - r)⁻¹ ^ 2) * (C s - C r) ^ 2 = 1 := by
      rw [← C_sub, ← C_pow, ← C_mul, ← C_1]
      congr 1
      field_simp
    simp only [mul_comp, C_comp, sub_comp, X_comp, map_sub]
    linear_combination (C A * X * (X + 1)) * h1
  rw [assocProduct, hcoeff, derivProduct_comp_affine _ _ hd, hw, derivProduct_C_mul_weight,
    betaProduct]
  have hfun : (fun k ↦ A ^ k * assocCoeff a A k) = betaCoeff (a * A)⁻¹ := by
    funext k
    rw [pow_mul_assocCoeff, assocCoeff_one_eq_betaCoeff (mul_pos ha hA)]
  rw [hfun]

end

end RealRooted
