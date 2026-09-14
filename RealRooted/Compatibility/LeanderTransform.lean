import RealRooted.Compatibility.Basic

/-!
# The diagonal-omitting Leander transform

This module defines the finite `0/1/X` transform from Leander's compatibility
theorem and records its coefficientwise algebra. Compatibility preservation is
proved in downstream modules.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The diagonal-omitting Leander transform
`L(f)_k = X * ∑_{h < k} f_h + ∑_{k < h} f_h`. -/
def leanderTransform {n : ℕ} (f : Fin n → ℝ[X]) (k : Fin n) : ℝ[X] :=
  ∑ h : Fin n, if h < k then X * f h else if k < h then f h else 0

@[simp]
theorem leanderTransform_one (f : Fin 1 → ℝ[X]) (k : Fin 1) :
    leanderTransform f k = 0 := by
  have hk : k = 0 := Fin.eq_zero k
  subst k
  simp [leanderTransform, Fin.eq_zero]

@[simp]
theorem leanderTransform_two_zero (f : Fin 2 → ℝ[X]) :
    leanderTransform f 0 = f 1 := by
  simp [leanderTransform, Fin.sum_univ_two]

@[simp]
theorem leanderTransform_two_one (f : Fin 2 → ℝ[X]) :
    leanderTransform f 1 = X * f 0 := by
  simp [leanderTransform, Fin.sum_univ_two]

/-- Exact five-region expansion used for compatibility between two transform
outputs. -/
theorem C_mul_leanderTransform_add_C_mul_leanderTransform {n : ℕ}
    (f : Fin n → ℝ[X]) {i j : Fin n} (hij : i ≤ j) (a b : ℝ) :
    C a * leanderTransform f i + C b * leanderTransform f j =
      ∑ h : Fin n,
        if h < i then X * (C a + C b) * f h
        else if h = i then if i < j then C b * X * f h else 0
        else if h < j then (C a + C b * X) * f h
        else if h = j then if i < j then C a * f h else 0
        else (C a + C b) * f h := by
  rw [leanderTransform, leanderTransform, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro h
  by_cases hhi : h < i
  · have hhj : h < j := lt_of_lt_of_le hhi hij
    simp [hhi, hhj]
    ring
  · by_cases hEqI : h = i
    · subst h
      by_cases hijlt : i < j
      · simp [hijlt]
        ring
      · have hEq : i = j := le_antisymm hij (le_of_not_gt hijlt)
        subst j
        simp
    · have ih : i < h :=
        lt_of_le_of_ne (le_of_not_gt hhi) (Ne.symm hEqI)
      by_cases hhj : h < j
      · simp [hhi, hEqI, ih, hhj]
        ring
      · by_cases hEqJ : h = j
        · subst h
          have hijlt : i < j := ih
          have hji : ¬j < i := not_lt_of_ge hijlt.le
          simp [hji, hijlt, hEqI]
        · have jh : j < h :=
            lt_of_le_of_ne (le_of_not_gt hhj) (Ne.symm hEqJ)
          simp [hhi, hEqI, ih, hhj, hEqJ, jh]
          ring

/-- Exact five-region expansion used for compatibility of an `X`-multiple of
one transform output with another output. -/
theorem C_mul_X_mul_leanderTransform_add_C_mul_leanderTransform {n : ℕ}
    (f : Fin n → ℝ[X]) {i j : Fin n} (hij : i ≤ j) (a b : ℝ) :
    C a * (X * leanderTransform f i) + C b * leanderTransform f j =
      ∑ h : Fin n,
        if h < i then X * (C a * X + C b) * f h
        else if h = i then if i < j then C b * X * f h else 0
        else if h < j then X * (C a + C b) * f h
        else if h = j then if i < j then C a * X * f h else 0
        else (C a * X + C b) * f h := by
  rw [leanderTransform, leanderTransform, ← mul_assoc, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro h
  by_cases hhi : h < i
  · have hhj : h < j := lt_of_lt_of_le hhi hij
    simp [hhi, hhj]
    ring
  · by_cases hEqI : h = i
    · subst h
      by_cases hijlt : i < j
      · simp [hijlt]
        ring
      · have hEq : i = j := le_antisymm hij (le_of_not_gt hijlt)
        subst j
        simp
    · have ih : i < h :=
        lt_of_le_of_ne (le_of_not_gt hhi) (Ne.symm hEqI)
      by_cases hhj : h < j
      · simp [hhi, hEqI, ih, hhj]
        ring
      · by_cases hEqJ : h = j
        · subst h
          have hijlt : i < j := ih
          have hji : ¬j < i := not_lt_of_ge hijlt.le
          simp [hji, hijlt, hEqI]
        · have jh : j < h :=
            lt_of_le_of_ne (le_of_not_gt hhj) (Ne.symm hEqJ)
          simp [hhi, hEqI, ih, hhj, hEqJ, jh]
          ring

end RealRooted
