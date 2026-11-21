module

public import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral

/-!
# Recognition of Poisson multiplication

We characterize real-linear operators commuting with `N_c = X (1 + c D)` as
Poisson multiplication by their value at `1`. The argument uses that `1` is cyclic
for `N_c`, and applies even without a finite differential-order assumption.
This formalizes the recognition argument in the unpublished manuscript
*Long OEIS proofs and grouped factors under the Stirling transform* (2026), issue #2134.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted.Poisson

noncomputable section

/-- Left Poisson multiplication commutes with the raising operator `N_c = X (1 + c D)`. -/
theorem starC_raising (c : ℝ) (f p : ℝ[X]) :
    starC c f (X * (p + C c * p.derivative)) =
      X * (starC c f p + C c * (starC c f p).derivative) := by
  rw [← starC_X_right, ← starC_assoc, starC_X_right]

/-- A real-linear map commuting with `N_c` is left Poisson multiplication by its value at `1`.
The identity holds for every real parameter, including zero. -/
theorem eq_starC_of_commutes_raising {c : ℝ} (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hT : ∀ p, T (X * (p + C c * p.derivative)) =
      X * (T p + C c * (T p).derivative)) (p : ℝ[X]) :
    T p = starC c (T 1) p := by
  have hC (a : ℝ) (q : ℝ[X]) : T (C a * q) = C a * T q := by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using T.map_smul a q
  induction p using Polynomial.induction_on with
  | C a =>
      calc
        T (C a) = C a * T 1 := by simpa only [mul_one] using hC a 1
        _ = starC c (T 1) (C a * 1) := by rw [starC_C_mul_right, starC_one_right]
        _ = starC c (T 1) (C a) := by rw [mul_one]
  | add p q hp hq => rw [map_add, hp, hq, starC_add_right]
  | monomial n a ih =>
      have hder : X * (C a * X ^ n).derivative = C (n : ℝ) * (C a * X ^ n) := by
        rw [derivative_C_mul, derivative_X_pow]
        cases n with
        | zero => simp
        | succ n => rw [Nat.add_sub_cancel]; ring
      have hraise : X * (C a * X ^ n + C c * (C a * X ^ n).derivative) =
          C a * X ^ (n + 1) + C (c * n) * (C a * X ^ n) := by
        rw [Polynomial.C_mul]
        linear_combination C c * hder
      have ht := hT (C a * X ^ n)
      rw [hraise, map_add, hC (c * n) (C a * X ^ n), ih] at ht
      have hs := starC_raising c (T 1) (C a * X ^ n)
      rw [hraise, starC_add_right,
        starC_C_mul_right c (c * n) (T 1) (C a * X ^ n)] at hs
      linear_combination ht - hs

/-- Commuting with `N_c` is equivalent to Poisson multiplication by the image of `1`. -/
theorem commutes_raising_iff_eq_starC (c : ℝ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    (∀ p, T (X * (p + C c * p.derivative)) =
      X * (T p + C c * (T p).derivative)) ↔
      ∀ p, T p = starC c (T 1) p := by
  constructor
  · exact eq_starC_of_commutes_raising T
  · intro h p
    calc
      T (X * (p + C c * p.derivative)) =
          starC c (T 1) (X * (p + C c * p.derivative)) := h _
      _ = X * (starC c (T 1) p + C c * (starC c (T 1) p).derivative) :=
        starC_raising c (T 1) p
      _ = X * (T p + C c * (T p).derivative) := by rw [← h p]

/-- For a commuting real-linear operator and a nonnegative parameter, PF preservation
is equivalent to its value at `1` being PF. -/
theorem preservesPF_iff_of_commutes_raising {c : ℝ} (hc : 0 ≤ c)
    (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hT : ∀ p, T (X * (p + C c * p.derivative)) =
      X * (T p + C c * (T p).derivative)) :
    (∀ p, IsPFPolynomial p → IsPFPolynomial (T p)) ↔ IsPFPolynomial (T 1) := by
  constructor
  · intro h
    exact h 1 IsPFPolynomial.one
  · intro h p hp
    rw [eq_starC_of_commutes_raising T hT]
    exact IsPFPolynomial.preservesPF hc h p hp

/-- Polynomial coefficients in a locally finite differential expansion are unique. -/
private theorem differential_coefficients_unique {A B : ℕ → ℝ[X]}
    (h : ∀ p : ℝ[X],
      ∑ j ∈ Finset.range (p.natDegree + 1), A j * (derivative^[j]) p =
        ∑ j ∈ Finset.range (p.natDegree + 1), B j * (derivative^[j]) p) : A = B := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hn := h (X ^ n)
    rw [natDegree_X_pow, Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hsum :
        ∑ j ∈ Finset.range n, A j * (derivative^[j]) (X ^ n) =
          ∑ j ∈ Finset.range n, B j * (derivative^[j]) (X ^ n) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    rw [hsum] at hn
    have htop := add_left_cancel hn
    simp only [iterate_derivative_X_pow_eq_C_mul, Nat.sub_self, pow_zero, mul_one,
      Nat.descFactorial_self] at htop
    exact mul_right_cancel₀ (by simp [Nat.factorial_ne_zero]) htop

/-- The differential coefficients of Poisson multiplication, with the sum truncated at
the input degree. This form includes every zero tail automatically. -/
theorem starC_eq_sum_input_degree (c : ℝ) (f p : ℝ[X]) :
    starC c f p = ∑ j ∈ Finset.range (p.natDegree + 1),
      (C (c ^ j / (j.factorial : ℝ)) * X ^ j * (derivative^[j]) f) *
        (derivative^[j]) p := by
  rw [starC_comm, starC]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A locally finite differential expansion is Poisson multiplication exactly when its
coefficients satisfy the factorial identities. No degree or nonzero assumption is needed. -/
theorem eq_starC_iff_factorial_mul_eq (c : ℝ) (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (A : ℕ → ℝ[X])
    (hA : ∀ p, T p = ∑ j ∈ Finset.range (p.natDegree + 1),
      A j * (derivative^[j]) p) :
    (∀ p, T p = starC c (T 1) p) ↔
      ∀ j, C (j.factorial : ℝ) * A j = C (c ^ j) * X ^ j * (derivative^[j]) (T 1) := by
  have heq (j : ℕ) :
      A j = C (c ^ j / (j.factorial : ℝ)) * X ^ j * (derivative^[j]) (T 1) ↔
        C (j.factorial : ℝ) * A j = C (c ^ j) * X ^ j * (derivative^[j]) (T 1) := by
    have hid : C (j.factorial : ℝ) * C (c ^ j / (j.factorial : ℝ)) = C (c ^ j) := by
      rw [← C_mul]
      congr 1
      field_simp
    constructor
    · intro h
      rw [h]
      simp only [← mul_assoc, hid]
    · intro h
      apply mul_left_cancel₀ (show (C (j.factorial : ℝ) : ℝ[X]) ≠ 0 by simp [Nat.factorial_ne_zero])
      rw [h]
      simp only [← mul_assoc, hid]
  constructor
  · intro h j
    have hab : A = fun j ↦
        C (c ^ j / (j.factorial : ℝ)) * X ^ j * (derivative^[j]) (T 1) :=
      differential_coefficients_unique (fun p ↦ by
        rw [← hA p, h p, starC_eq_sum_input_degree])
    exact (heq j).mp (congrFun hab j)
  · intro h p
    rw [hA, starC_eq_sum_input_degree]
    apply Finset.sum_congr rfl
    intro j _
    rw [(heq j).mpr (h j)]

/-- The three recognition conditions: commutation with `N_c`, the factorial differential
coefficient identities, and Poisson multiplication by the value at `1`. -/
theorem commutes_raising_iff_factorial_mul_eq (c : ℝ) (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (A : ℕ → ℝ[X])
    (hA : ∀ p, T p = ∑ j ∈ Finset.range (p.natDegree + 1),
      A j * (derivative^[j]) p) :
    (∀ p, T (X * (p + C c * p.derivative)) =
      X * (T p + C c * (T p).derivative)) ↔
      ∀ j, C (j.factorial : ℝ) * A j = C (c ^ j) * X ^ j * (derivative^[j]) (T 1) := by
  rw [commutes_raising_iff_eq_starC, eq_starC_iff_factorial_mul_eq c T A hA]

/-- A finite differential expansion with an explicit zero tail can be truncated instead
at the input degree. -/
private theorem sum_mul_iterate_derivative_eq_sum_input_degree
    (A : ℕ → ℝ[X]) (r : ℕ) (hA : ∀ j, r < j → A j = 0) (p : ℝ[X]) :
    ∑ j ∈ Finset.range (r + 1), A j * (derivative^[j]) p =
      ∑ j ∈ Finset.range (p.natDegree + 1), A j * (derivative^[j]) p := by
  by_cases hpr : p.natDegree ≤ r
  · symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
    intro j _ hj
    have hd : p.natDegree < j := by
      simp only [Finset.mem_range, not_lt] at hj
      lia
    rw [iterate_derivative_eq_zero hd, mul_zero]
  · apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
    intro j _ hj
    rw [hA j (by
      simp only [Finset.mem_range, not_lt] at hj
      lia), zero_mul]

/-- Finite differential-coefficient recognition, including every coefficient beyond the
order bound. Here `A 0 = T 1`; the explicit zero tail is part of the finite-order data. -/
theorem commutes_raising_iff_factorial_mul_eq_of_finite
    (c : ℝ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (A : ℕ → ℝ[X]) (r : ℕ)
    (htail : ∀ j, r < j → A j = 0)
    (hA : ∀ p, T p = ∑ j ∈ Finset.range (r + 1), A j * (derivative^[j]) p) :
    (∀ p, T (X * (p + C c * p.derivative)) =
      X * (T p + C c * (T p).derivative)) ↔
      ∀ j, C (j.factorial : ℝ) * A j = C (c ^ j) * X ^ j * (derivative^[j]) (A 0) := by
  have hlocal (p : ℝ[X]) : T p = ∑ j ∈ Finset.range (p.natDegree + 1),
      A j * (derivative^[j]) p := by
    rw [hA, sum_mul_iterate_derivative_eq_sum_input_degree A r htail]
  have h1 : T 1 = A 0 := by simpa using hlocal 1
  rw [← h1]
  exact commutes_raising_iff_factorial_mul_eq c T A hlocal

end

end RealRooted.Poisson
