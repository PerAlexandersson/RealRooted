import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Vieta identities from the lowest coefficients

Reciprocal-root power sums and a product factorization in terms of the lowest
coefficients of a real polynomial.
-/

namespace RealRooted.RootVieta

open Polynomial

noncomputable section

def rootProd (s : Multiset ℝ) : ℝ[X] := (s.map (fun ξ => X - C ξ)).prod

@[simp] theorem rootProd_zero : rootProd 0 = 1 := by simp [rootProd]

theorem rootProd_cons (ξ : ℝ) (s : Multiset ℝ) :
    rootProd (ξ ::ₘ s) = (X - C ξ) * rootProd s := by
  simp [rootProd]

theorem coeff_zero_cons (ξ : ℝ) (s : Multiset ℝ) :
    (rootProd (ξ ::ₘ s)).coeff 0 = -ξ * (rootProd s).coeff 0 := by
  rw [rootProd_cons, Polynomial.mul_coeff_zero]
  simp

theorem coeff_one_cons (ξ : ℝ) (s : Multiset ℝ) :
    (rootProd (ξ ::ₘ s)).coeff 1
      = (rootProd s).coeff 0 - ξ * (rootProd s).coeff 1 := by
  rw [rootProd_cons, show (X - C ξ) * rootProd s = X * rootProd s - C ξ * rootProd s by ring]
  rw [coeff_sub, coeff_X_mul, coeff_C_mul]

theorem coeff_two_cons (ξ : ℝ) (s : Multiset ℝ) :
    (rootProd (ξ ::ₘ s)).coeff 2
      = (rootProd s).coeff 1 - ξ * (rootProd s).coeff 2 := by
  rw [rootProd_cons, show (X - C ξ) * rootProd s = X * rootProd s - C ξ * rootProd s by ring]
  rw [coeff_sub, coeff_C_mul]
  congr 1
  exact coeff_X_mul (rootProd s) 1

/-- The constant coefficient is the product of the negated roots. -/
theorem coeff_zero_eq (s : Multiset ℝ) :
    (rootProd s).coeff 0 = (s.map (fun ξ => -ξ)).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih => rw [coeff_zero_cons, ih]; simp

theorem coeff_zero_ne_zero {s : Multiset ℝ} (h : ∀ ξ ∈ s, ξ ≠ 0) :
    (rootProd s).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq]
  refine Multiset.prod_ne_zero ?_
  intro hmem
  rw [Multiset.mem_map] at hmem
  obtain ⟨ξ, hξ, hEq⟩ := hmem
  exact h ξ hξ (neg_eq_zero.mp hEq)

/-- **First Vieta identity.**  `a_1/a_0` is the sum of the `-1/xi`. -/
theorem coeff_one_div (s : Multiset ℝ) (h : ∀ ξ ∈ s, ξ ≠ 0) :
    (rootProd s).coeff 1 / (rootProd s).coeff 0
      = (s.map (fun ξ => -(1 / ξ))).sum := by
  induction s using Multiset.induction with
  | empty => simp [rootProd, Polynomial.coeff_one]
  | cons a t ih =>
      have ha : a ≠ 0 := h a (Multiset.mem_cons_self a t)
      have ht : ∀ ξ ∈ t, ξ ≠ 0 := fun ξ hξ => h ξ (Multiset.mem_cons_of_mem hξ)
      have h0 : (rootProd t).coeff 0 ≠ 0 := coeff_zero_ne_zero ht
      rw [coeff_one_cons, coeff_zero_cons, Multiset.map_cons, Multiset.sum_cons, ← ih ht]
      field_simp
      ring

/-- **Second Vieta identity.**  The power sum of the reciprocal roots, in terms
of the two lowest coefficient ratios.  This is `(sum x)^2 - sum x^2 = 2 e_2`
with `e_2 = a_2/a_0`. -/
theorem sum_sq_eq (s : Multiset ℝ) (h : ∀ ξ ∈ s, ξ ≠ 0) :
    (s.map (fun ξ => -(1 / ξ))).sum ^ 2 - (s.map (fun ξ => (1 / ξ) ^ 2)).sum
      = 2 * ((rootProd s).coeff 2 / (rootProd s).coeff 0) := by
  induction s using Multiset.induction with
  | empty => simp [rootProd, Polynomial.coeff_one]
  | cons a t ih =>
      have ha : a ≠ 0 := h a (Multiset.mem_cons_self a t)
      have ht : ∀ ξ ∈ t, ξ ≠ 0 := fun ξ hξ => h ξ (Multiset.mem_cons_of_mem hξ)
      have h0 : (rootProd t).coeff 0 ≠ 0 := coeff_zero_ne_zero ht
      have hA := coeff_one_div t ht
      have hI := ih ht
      set A := (t.map (fun ξ => -(1 / ξ))).sum with hAdef
      set B := (t.map (fun ξ => (1 / ξ) ^ 2)).sum with hBdef
      have hc1 : (rootProd t).coeff 1 = A * (rootProd t).coeff 0 :=
        (div_eq_iff h0).mp hA
      have hc2 : (rootProd t).coeff 2 = (A ^ 2 - B) * (rootProd t).coeff 0 / 2 := by
        field_simp at hI
        linarith
      rw [coeff_two_cons, coeff_zero_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_cons, Multiset.sum_cons, hc1, hc2]
      field_simp
      rw [hAdef, hBdef]
      simp only [one_div]
      ring

/-! ### Transfer to an arbitrary polynomial with a full set of roots -/

theorem coeff_eq_of_card {p : ℝ[X]} (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    p.coeff k = p.leadingCoeff * (rootProd p.roots).coeff k := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul]
  rfl

theorem coeff_ratio {p : ℝ[X]} (hroots : Multiset.card p.roots = p.natDegree)
    (hlc : p.leadingCoeff ≠ 0) (k : ℕ) :
    p.coeff k / p.coeff 0 = (rootProd p.roots).coeff k / (rootProd p.roots).coeff 0 := by
  rw [coeff_eq_of_card hroots k, coeff_eq_of_card hroots 0]
  exact mul_div_mul_left _ _ hlc

/-- **Vieta, first power sum.**  For a polynomial whose roots are all present and
nonzero, `a_1/a_0` is the sum of the reciprocal root magnitudes `-1/xi`. -/
theorem poly_sum (p : ℝ[X]) (hroots : Multiset.card p.roots = p.natDegree)
    (hlc : p.leadingCoeff ≠ 0) (h : ∀ ξ ∈ p.roots, ξ ≠ 0) :
    p.coeff 1 / p.coeff 0 = (p.roots.map (fun ξ => -(1 / ξ))).sum := by
  rw [coeff_ratio hroots hlc 1]
  exact coeff_one_div p.roots h

/-- **Vieta, second power sum.**  `(sum x)^2 - sum x^2 = 2 a_2/a_0`. -/
theorem poly_sum_sq (p : ℝ[X]) (hroots : Multiset.card p.roots = p.natDegree)
    (hlc : p.leadingCoeff ≠ 0) (h : ∀ ξ ∈ p.roots, ξ ≠ 0) :
    (p.roots.map (fun ξ => -(1 / ξ))).sum ^ 2 - (p.roots.map (fun ξ => (1 / ξ) ^ 2)).sum
      = 2 * (p.coeff 2 / p.coeff 0) := by
  rw [coeff_ratio hroots hlc 2]
  exact sum_sq_eq p.roots h

/-! ### The reciprocal-root factorization -/

theorem X_sub_C_eq {ξ : ℝ} (h : ξ ≠ 0) :
    (X - C ξ : Polynomial ℝ) = C (-ξ) * (1 + C (-(1 / ξ)) * X) := by
  have hmul : (-ξ) * (-(1 / ξ)) = 1 := by field_simp
  rw [mul_add, mul_one, ← mul_assoc, ← C_mul, hmul, map_one, one_mul, C_neg]
  ring

/-- **The reciprocal-root factorization.**  A polynomial with all roots present,
none of them zero, and constant coefficient `1`, is the product of `1 + x_i X`
over the reciprocal root magnitudes. -/
theorem eq_prod_one_add {p : Polynomial ℝ}
    (hcard : Multiset.card p.roots = p.natDegree)
    (hnz : ∀ ξ ∈ p.roots, ξ ≠ 0) (ha0 : p.coeff 0 = 1) :
    p = (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod := by
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hmap : (p.roots.map (fun ξ => X - C ξ)).prod
      = (p.roots.map (fun ξ => C (-ξ))).prod
        * (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod := by
    rw [← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun ξ hξ => ?_))
    exact X_sub_C_eq (hnz ξ hξ)
  have hC : (p.roots.map (fun ξ => C (-ξ))).prod
      = C ((p.roots.map (fun ξ => -ξ)).prod) := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  have hconst : p.leadingCoeff * (p.roots.map (fun ξ => -ξ)).prod = 1 := by
    rw [← coeff_zero_eq, ← coeff_eq_of_card hcard 0]
    exact ha0
  calc p = C p.leadingCoeff * (p.roots.map (fun ξ => X - C ξ)).prod := hfac.symm
    _ = C p.leadingCoeff * (C ((p.roots.map (fun ξ => -ξ)).prod)
          * (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod) := by rw [hmap, hC]
    _ = C (p.leadingCoeff * (p.roots.map (fun ξ => -ξ)).prod)
          * (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod := by
        rw [C_mul]; ring
    _ = (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod := by
        rw [hconst, map_one, one_mul]

end


end RealRooted.RootVieta
