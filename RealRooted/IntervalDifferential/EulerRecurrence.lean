/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.PowerSeries.Derivative
public import RealRooted.IntervalDifferential.CoefficientNorm
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
import Mathlib.Tactic

/-!
# Euler coefficients and executable tables

The Euler differential equation uniquely determines its normalized coefficients.
Adding kernels convolves rows. Degree and norm bounds accompany an executable
integer table whose entries are factorial-scaled genuine coefficients.
-/

@[expose] public noncomputable section

open Finset

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The normalized coefficient row determined by an Euler kernel. -/
def eulerCoeff (K : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => (((n + 1 : ℕ) : ℚ)⁻¹) •
      ∑ i : Fin (n + 1), K (n + 1 - i.val) * eulerCoeff K i.val
termination_by n => n

@[simp] theorem eulerCoeff_zero (K : ℕ → R) : eulerCoeff K 0 = 1 := by rw [eulerCoeff]

/-- The denominator-cleared Euler recurrence. -/
theorem eulerCoeff_equation (K : ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) • eulerCoeff K n = ∑ i ∈ range n, K (n - i) * eulerCoeff K i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [eulerCoeff, smul_smul, mul_inv_cancel₀ (by positivity : ((m + 1 : ℕ) : ℚ) ≠ 0),
    one_smul, Fin.sum_univ_eq_sum_range (fun i => K (m + 1 - i) * eulerCoeff K i)]

/-- The Euler recurrence with its constant coefficient determines the whole row. -/
theorem eulerCoeff_unique (K a : ℕ → R) (h0 : a 0 = 1)
    (ha : ∀ (n : ℕ), n ≠ 0 → (n : ℚ) • a n = ∑ i ∈ range n, K (n - i) * a i) :
    a = eulerCoeff K := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · simp [hn, h0]
    · have he := ha n hn
      have ht := eulerCoeff_equation K hn
      have hh : ∑ i ∈ range n, K (n - i) * a i =
          ∑ i ∈ range n, K (n - i) * eulerCoeff K i := by
        exact sum_congr rfl (fun i hi => by rw [ih i (mem_range.mp hi)])
      rw [hh, ← ht] at he
      have hi := congrArg (fun x : R => (n : ℚ)⁻¹ • x) he
      simpa only [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn : (n : ℚ) ≠ 0),
        one_smul] using hi

/-- The coefficient row satisfies its formal Euler differential equation. -/
theorem mk_eulerCoeff_equation (K : ℕ → R) (hK : K 0 = 0) :
    X * derivative (mk (eulerCoeff K)) = mk K * mk (eulerCoeff K) := by
  ext n
  rw [coeff_X_mul_derivative, coeff_mk, mul_comm (mk K), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    Nat.sub_self]
  simp only [coeff_mk, hK, mul_zero, add_zero]
  by_cases hn : n = 0
  · simp [hn]
  · have he := eulerCoeff_equation K hn
    simpa [Algebra.smul_def, mul_comm] using he

/-- The normalized solution of an Euler equation has the canonical coefficients. -/
theorem eq_mk_eulerCoeff (K : ℕ → R) (hK : K 0 = 0) (F : PowerSeries R)
    (h0 : constantCoeff F = 1) (hF : X * derivative F = mk K * F) :
    F = mk (eulerCoeff K) := by
  have he := eulerCoeff_unique K (fun n => coeff n F)
    (by simpa only [coeff_zero_eq_constantCoeff] using h0) (by
    intro n hn
    have hh := congrArg (coeff n) hF
    rw [coeff_X_mul_derivative, mul_comm (mk K), coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
      Nat.sub_self] at hh
    simp only [coeff_mk, hK, mul_zero, add_zero] at hh
    simpa [Algebra.smul_def, mul_comm] using hh)
  ext n
  simpa using congrFun he n

/-- Adding two Euler kernels convolves their normalized coefficient rows. -/
theorem eulerCoeff_add (K J : ℕ → R) (hK : K 0 = 0) (hJ : J 0 = 0) (n : ℕ) :
    eulerCoeff (K + J) n =
      ∑ i ∈ range (n + 1), eulerCoeff K i * eulerCoeff J (n - i) := by
  have hprod : mk (eulerCoeff (K + J)) = mk (eulerCoeff K) * mk (eulerCoeff J) := by
    symm
    apply eq_mk_eulerCoeff (K + J) (by simp [hK, hJ])
    · simp
    · have h1 := mk_eulerCoeff_equation K hK
      have h2 := mk_eulerCoeff_equation J hJ
      rw [derivative.leibniz]
      have ha : mk (K + J) = mk K + mk J := by ext; simp
      rw [ha]
      linear_combination mk (eulerCoeff J) * h1 + mk (eulerCoeff K) * h2
  have he := congrArg (coeff n) hprod
  simpa only [coeff_mk, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using he

end PowerSeries

open Polynomial Finset

namespace RealRooted.IntervalDifferential

/-- A size-bounded Euler kernel produces size-bounded polynomial coefficients. -/
theorem natDegree_eulerCoeff_le (K : ℕ → ℚ[X])
    (hK : ∀ i, (K i).natDegree ≤ i) (n : ℕ) :
    (PowerSeries.eulerCoeff K n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [PowerSeries.eulerCoeff, smul_eq_C_mul]
      apply (natDegree_C_mul_le _ _).trans
      apply natDegree_sum_le_of_forall_le
      intro i _
      apply natDegree_mul_le.trans
      have h1 := hK (n + 1 - i.val)
      have h2 := ih i.val i.isLt
      lia

/-- The coefficient norm satisfies the scalar Euler convolution inequality. -/
theorem coefficientNorm_eulerCoeff_equation {r : ℚ} (hr : 0 ≤ r)
    (K : ℕ → ℚ[X]) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) * coefficientNorm r (PowerSeries.eulerCoeff K n) ≤
      ∑ i ∈ range n, coefficientNorm r (K (n - i)) *
        coefficientNorm r (PowerSeries.eulerCoeff K i) := by
  have he := congrArg (coefficientNorm r) (PowerSeries.eulerCoeff_equation K hn)
  rw [smul_eq_C_mul, coefficientNorm_C_mul, abs_of_nonneg (Nat.cast_nonneg n)] at he
  rw [he]
  exact (coefficientNorm_sum_le hr _ _).trans
    (sum_le_sum (fun i _ => coefficientNorm_mul_le hr _ _))

end RealRooted.IntervalDifferential

open Finset Polynomial

namespace RealRooted.IntervalDifferential

/-- Compute one degree-truncated Euler row from the preceding rows. -/
def eulerTableStep (H : ℕ) (support : ℕ → Finset ℕ) (cell : ℕ → ℕ → ℤ) (n : ℕ)
    (previous : Array (Array ℤ)) : Array ℤ :=
  Array.ofFn fun h : Fin (H + 1) =>
    if n < h.val then 0 else if n = 0 then if h.val = 0 then 1 else 0 else
      ∑ i ∈ range n, (((n - 1).factorial / i.factorial : ℕ) : ℤ) *
        ∑ a ∈ (support (n - i)).filter (· ≤ h.val),
        if n - i < a ∨ i < h.val - a then 0 else
        if (previous.getD i #[]).getD (h.val - a) 0 = 0 then 0 else
          cell (n - i) a * (previous.getD i #[]).getD (h.val - a) 0

/-- Memoized factorial-scaled integer rows through the indicated number of rows. -/
def eulerCoefficientTable (H : ℕ) (support : ℕ → Finset ℕ) (cell : ℕ → ℕ → ℤ) : ℕ → Array (Array ℤ)
  | 0 => #[]
  | n + 1 => let previous := eulerCoefficientTable H support cell n
      previous.push (eulerTableStep H support cell n previous)

@[simp] theorem size_eulerCoefficientTable (H : ℕ) (support : ℕ → Finset ℕ)
    (cell : ℕ → ℕ → ℤ) (n : ℕ) :
    (eulerCoefficientTable H support cell n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eulerCoefficientTable, ih]

private theorem getD_push {α : Type*} (xs : Array α) (x d : α) (i : ℕ) :
    (xs.push x).getD i d = if i = xs.size then x else xs.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> rfl

private theorem getD_eulerTableStep (H : ℕ) (support : ℕ → Finset ℕ) (cell : ℕ → ℕ → ℤ) (n : ℕ)
    (previous : Array (Array ℤ)) {h : ℕ} (hh : h ≤ H) :
    (eulerTableStep H support cell n previous).getD h 0 =
      if n < h then 0 else if n = 0 then if h = 0 then 1 else 0 else
        ∑ i ∈ range n, (((n - 1).factorial / i.factorial : ℕ) : ℤ) *
          ∑ a ∈ (support (n - i)).filter (· ≤ h),
          if n - i < a ∨ i < h - a then 0 else
          if (previous.getD i #[]).getD (h - a) 0 = 0 then 0 else
            cell (n - i) a * (previous.getD i #[]).getD (h - a) 0 := by
  simp [eulerTableStep, Array.getD_eq_getD_getElem?,
    show h < H + 1 by lia]

/-- One normalized table transition follows the Euler coefficient equation. -/
private theorem eulerTableStep_correct (H : ℕ) (support : ℕ → Finset ℕ)
    (cell : ℕ → ℕ → ℤ) (K : ℕ → ℚ[X])
    (hcell : ∀ n h, (cell n h : ℚ) = (K n).coeff h)
    (hK : ∀ i, (K i).natDegree ≤ i)
    (hsupport : ∀ i a, a ∉ support i → cell i a = 0) {N h : ℕ} (hh : h ≤ H)
    (ih : ∀ {i h : ℕ}, i < N → h ≤ H →
      ((((eulerCoefficientTable H support cell N).getD i #[]).getD h 0 : ℤ) : ℚ) =
        (i.factorial : ℚ) * (PowerSeries.eulerCoeff K i).coeff h) :
    ((eulerTableStep H support cell N (eulerCoefficientTable H support cell N)).getD h 0 : ℚ) =
      (N.factorial : ℚ) * (PowerSeries.eulerCoeff K N).coeff h := by
  rw [getD_eulerTableStep H support cell N _ hh]
  by_cases hNh : N < h
  · rw [ite_eq_left hNh]
    rw [coeff_eq_zero_of_natDegree_lt
      ((natDegree_eulerCoeff_le K hK N).trans_lt hNh), mul_zero]
    rfl
  · rw [ite_eq_right hNh]
    by_cases hn : N = 0
    · subst N
      rw [ite_eq_left rfl, PowerSeries.eulerCoeff_zero, coeff_one]
      norm_num
    · rw [ite_eq_right hn]
      have he := congrArg (fun p : ℚ[X] => p.coeff h)
        (PowerSeries.eulerCoeff_equation K hn)
      rw [smul_eq_C_mul, coeff_C_mul, finsetSum_coeff] at he
      simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_ite, Int.cast_zero]
      have hs : (∑ j ∈ range N,
          (((N - 1).factorial / j.factorial : ℕ) : ℚ) *
            ∑ a ∈ (support (N - j)).filter (· ≤ h),
              if N - j < a ∨ j < h - a then 0 else
              if ((eulerCoefficientTable H support cell N).getD j #[]).getD (h - a) 0 = 0
                then 0 else
                (cell (N - j) a : ℚ) *
                  (((eulerCoefficientTable H support cell N).getD j #[]).getD (h - a) 0 : ℚ)) =
          ((N - 1).factorial : ℚ) *
            ∑ j ∈ range N, ∑ a ∈ range (h + 1),
              (K (N - j)).coeff a * (PowerSeries.eulerCoeff K j).coeff (h - a) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        have hjN := mem_range.mp hj
        have hf : (((N - 1).factorial / j.factorial : ℕ) : ℚ) * (j.factorial : ℚ) =
            ((N - 1).factorial : ℚ) := by
          exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by lia : j ≤ N - 1))
        have hs : (∑ a ∈ (support (N - j)).filter (· ≤ h),
            (K (N - j)).coeff a * (PowerSeries.eulerCoeff K j).coeff (h - a)) =
            ∑ a ∈ range (h + 1),
              (K (N - j)).coeff a * (PowerSeries.eulerCoeff K j).coeff (h - a) := by
          apply sum_subset (by intro a ha; exact mem_range.mpr (by
            have := (mem_filter.mp ha).2; lia))
          intro a ha hnot
          have hna : a ∉ support (N - j) := by
            intro he
            exact hnot (mem_filter.mpr ⟨he, by have := mem_range.mp ha; lia⟩)
          rw [← hcell, hsupport _ _ hna, Int.cast_zero, zero_mul]
        rw [← hs, mul_sum, mul_sum]
        apply sum_congr rfl
        intro a _
        by_cases hb : N - j < a ∨ j < h - a
        · rw [ite_eq_left hb, mul_zero]
          rcases hb with hb | hb
          · rw [coeff_eq_zero_of_natDegree_lt ((hK _).trans_lt hb), zero_mul, mul_zero]
          · rw [coeff_eq_zero_of_natDegree_lt
              ((natDegree_eulerCoeff_le K hK j).trans_lt hb), mul_zero, mul_zero]
        · rw [ite_eq_right hb]
          by_cases hz : ((eulerCoefficientTable H support cell N).getD j #[]).getD (h - a) 0 = 0
          · rw [ite_eq_left hz, mul_zero]
            have hez := ih (i := j) (h := h - a) hjN ((Nat.sub_le h a).trans hh)
            rw [hz, Int.cast_zero] at hez
            have hp : (PowerSeries.eulerCoeff K j).coeff (h - a) = 0 :=
              (mul_eq_zero.mp hez.symm).resolve_left (by positivity)
            rw [hp, mul_zero, mul_zero]
          · rw [ite_eq_right hz, hcell, ih hjN ((Nat.sub_le _ _).trans hh)]
            linear_combination (K (N - j)).coeff a *
              (PowerSeries.eulerCoeff K j).coeff (h - a) * hf
      rw [hs, ← he]
      have hf : (N.factorial : ℚ) = (N : ℚ) * ((N - 1).factorial : ℚ) := by
        exact_mod_cast (Nat.mul_factorial_pred hn).symm
      rw [hf]
      ring

/-- Every entry of the executable table is the genuine Euler coefficient. -/
theorem eulerCoefficientTable_correct (H : ℕ) (support : ℕ → Finset ℕ)
    (cell : ℕ → ℕ → ℤ) (K : ℕ → ℚ[X])
    (hcell : ∀ n h, (cell n h : ℚ) = (K n).coeff h)
    (hK : ∀ i, (K i).natDegree ≤ i)
    (hsupport : ∀ i a, a ∉ support i → cell i a = 0) {N i h : ℕ} (hi : i < N) (hh : h ≤ H) :
    ((((eulerCoefficientTable H support cell N).getD i #[]).getD h 0 : ℤ) : ℚ) =
      (i.factorial : ℚ) * (PowerSeries.eulerCoeff K i).coeff h := by
  induction N generalizing i h with
  | zero => lia
  | succ N ih =>
    rw [eulerCoefficientTable, getD_push, size_eulerCoefficientTable]
    by_cases hin : i = N
    · subst i
      rw [ite_eq_left rfl]
      exact eulerTableStep_correct H support cell K hcell hK hsupport hh ih
    · rw [ite_eq_right hin]
      exact ih (by lia) hh

end RealRooted.IntervalDifferential
