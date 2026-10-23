/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.SeriesBasic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Formal `√(1-s²)`, `1/√(1-s²)`, `arcsin`, and substitution of `sin`

All series are formal power series over `ℝ`. Adapted from Aristotle's centered-disk proof,
`RequestProject/FormalArcsin.lean` (2026-10-23).
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

local notation "D" => (PowerSeries.derivative (R := ℝ))

/-! ### Small coefficient helpers -/

lemma coeff_one_sub_X_sq_mul (g : ℝ⟦X⟧) (m : ℕ) :
    coeff m ((1 - X ^ 2) * g) = coeff m g - (if 2 ≤ m then coeff (m - 2) g else 0) := by
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul']

lemma coeff_X_mul' (g : ℝ⟦X⟧) (m : ℕ) :
    coeff m (X * g) = if 1 ≤ m then coeff (m - 1) g else 0 := by
  rw [← pow_one (X : ℝ⟦X⟧), coeff_X_pow_mul']

/-- Uniqueness for the linear ODE `(1 - X²) u' = c X u`. -/
lemma ode_unique (u v : ℝ⟦X⟧) (c : ℝ)
    (hu : (1 - X ^ 2) * D u = C c * X * u) (hv : (1 - X ^ 2) * D v = C c * X * v)
    (h0 : constantCoeff u = constantCoeff v) : u = v := by
  set w := u - v with hw
  have hwode : (1 - X ^ 2) * D w = C c * X * w := by
    rw [hw, map_sub, mul_sub, hu, hv, mul_sub]
  suffices h : ∀ n, coeff n w = 0 by
    have : w = 0 := by ext n; rw [h n, map_zero]
    exact sub_eq_zero.mp this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | m
  · rw [coeff_zero_eq_constantCoeff_apply, hw, map_sub, h0, sub_self]
  · have := congrArg (coeff 0) hwode
    rw [coeff_one_sub_X_sq_mul, mul_assoc, coeff_C_mul, coeff_X_mul', coeff_derivative] at this
    simpa using this
  · have := congrArg (coeff (m + 1)) hwode
    rw [coeff_one_sub_X_sq_mul, mul_assoc, coeff_C_mul, coeff_X_mul', coeff_derivative] at this
    have hm := ih m (by lia)
    rcases m with _ | m
    · simp [hm] at this
      have h2 : (1 : ℝ) + 1 ≠ 0 := by norm_num
      simpa [h2] using this
    · simp only [show 2 ≤ m + 1 + 1 by lia, ite_true, show 1 ≤ m + 1 + 1 by lia,
        show m + 1 + 1 - 2 = m by lia, show m + 1 + 1 - 1 = m + 1 by lia,
        coeff_derivative, hm] at this
      have hne : ((m + 1 + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      simp only [zero_mul, sub_zero, mul_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by push_cast at hne ⊢; exact hne)

/-! ### Formal derivatives of `sin` and `cos` -/

lemma derivative_sinS : D sinS = cosS := by
  ext n
  rw [coeff_derivative, coeff_sinS, coeff_cosS]
  by_cases hn : Even n
  · have : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using hn
    rw [ite_eq_right this, ite_eq_left hn]
    have hd : (n + 1) / 2 = n / 2 := by obtain ⟨r, rfl⟩ := hn; lia
    rw [hd, Nat.factorial_succ]
    push_cast
    field_simp
  · have : Even (n + 1) := by simpa [Nat.even_add_one] using hn
    rw [ite_eq_left this, ite_eq_right hn]; ring

lemma derivative_cosS : D cosS = -sinS := by
  ext n
  rw [coeff_derivative, coeff_cosS, map_neg, coeff_sinS]
  by_cases hn : Even n
  · have : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using hn
    rw [ite_eq_right this, ite_eq_left hn]; ring
  · have : Even (n + 1) := by simpa [Nat.even_add_one] using hn
    rw [ite_eq_left this, ite_eq_right hn]
    have hd : (n + 1) / 2 = n / 2 + 1 := by
      rw [Nat.not_even_iff_odd] at hn; obtain ⟨r, rfl⟩ := hn; lia
    rw [hd, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

lemma sq_deriv (g : ℝ⟦X⟧) : D (g ^ 2) = 2 * g * D g := by
  rw [derivative_pow]; simp

lemma sinS_sq_add_cosS_sq : sinS ^ 2 + cosS ^ 2 = 1 := by
  apply derivative.ext
  · rw [map_add, sq_deriv, sq_deriv, derivative_sinS, derivative_cosS]
    simp only [Derivation.map_one_eq_zero]
    ring
  · rw [map_add, map_pow, map_pow, constantCoeff_sinS, constantCoeff_cosS, map_one]; norm_num

/-! ### `q = √(1 - s²)` -/

/-- Coefficients of `√(1 - s²)`. -/
noncomputable def qc : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (n + 2) => ((n : ℝ) - 1) / (n + 2) * qc n

/-- The formal series `q(s) = √(1 - s²)`. -/
noncomputable def qS : ℝ⟦X⟧ := mk qc

lemma constantCoeff_qS : constantCoeff qS = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, qS, coeff_mk]; rfl

lemma qS_ode : (1 - X ^ 2) * D qS = C (-1 : ℝ) * X * qS := by
  ext m
  rw [coeff_one_sub_X_sq_mul, mul_assoc, coeff_C_mul, coeff_X_mul', coeff_derivative]
  rcases m with _ | _ | n
  · simp [qS, qc]
  · simp [qS, qc]; norm_num
  · simp only [show 2 ≤ n + 1 + 1 by lia, ite_true, show 1 ≤ n + 1 + 1 by lia,
      show n + 1 + 1 - 2 = n by lia, show n + 1 + 1 - 1 = n + 1 by lia, coeff_derivative,
      qS, coeff_mk]
    rw [show n + 1 + 1 + 1 = (n + 1) + 2 by ring, qc]
    push_cast
    field_simp
    ring

lemma qS_sq : qS ^ 2 = 1 - X ^ 2 := by
  apply ode_unique _ _ (-2)
  · rw [sq_deriv]
    have := qS_ode
    rw [map_neg, map_one] at this
    rw [map_neg, map_ofNat]
    linear_combination (2 * qS) * this
  · rw [map_sub, sq_deriv, derivative_X, Derivation.map_one_eq_zero, map_neg, map_ofNat]
    ring
  · rw [map_pow, constantCoeff_qS, map_sub, map_one, map_pow, constantCoeff_X]; norm_num

/-- `1/q`. -/
noncomputable def invqS : ℝ⟦X⟧ := qS⁻¹

lemma qS_mul_invqS : qS * invqS = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_qS]; norm_num)

lemma constantCoeff_invqS : constantCoeff invqS = 1 := by
  have := congrArg constantCoeff qS_mul_invqS
  rw [map_mul, constantCoeff_qS, one_mul, map_one] at this
  exact this

lemma invqS_ode : (1 - X ^ 2) * D invqS = C (1 : ℝ) * X * invqS := by
  rw [invqS, derivative_inv']
  have h := qS_ode
  have h1 : qS⁻¹ * qS = 1 := by rw [mul_comm]; exact qS_mul_invqS
  calc (1 - X ^ 2) * (-qS⁻¹ ^ 2 * D qS) = -qS⁻¹ ^ 2 * ((1 - X ^ 2) * D qS) := by ring
    _ = C (1 : ℝ) * X * qS⁻¹ := by
      rw [h, map_one, show (C (-1 : ℝ) : ℝ⟦X⟧) = -1 by simp]
      linear_combination (X * qS⁻¹) * h1

/-! ### `f = arcsin` -/

/-- Coefficients of `arcsin`. -/
noncomputable def fc : ℕ → ℝ
  | 0 => 0
  | (n + 1) => coeff n invqS / (n + 1)

/-- The formal series `f(s) = arcsin s`. -/
noncomputable def fS : ℝ⟦X⟧ := mk fc

lemma constantCoeff_fS : constantCoeff fS = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, fS, coeff_mk]; rfl

lemma derivative_fS : D fS = invqS := by
  ext n
  rw [coeff_derivative, fS, coeff_mk, fc]
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-! ### Substitution of `sin` -/

lemma hasSubst_of_cc_zero {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) : HasSubst b :=
  HasSubst.of_constantCoeff_zero' hb

lemma coeff_pow_eq_zero_of_lt {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) {i j : ℕ} (h : i < j) :
    coeff i (b ^ j) = 0 := by
  obtain ⟨b', rfl⟩ := X_dvd_iff.mpr hb
  rw [mul_pow, coeff_X_pow_mul', ite_eq_right (by lia)]

/-- Finite formula for coefficients of a substitution. -/
lemma coeff_subst_eq_sum {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) (g : ℝ⟦X⟧) {i M : ℕ}
    (hi : i ≤ M) :
    coeff i (g.subst b) = ∑ j ∈ Finset.range (M + 1), coeff j g * coeff i (b ^ j) := by
  rw [coeff_subst' (hasSubst_of_cc_zero hb)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (M + 1))]
  · simp [smul_eq_mul]
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    apply hj
    rw [coeff_pow_eq_zero_of_lt hb (by lia), smul_zero]

lemma constantCoeff_subst_eq {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) (g : ℝ⟦X⟧) :
    constantCoeff (g.subst b) = constantCoeff g := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum hb g (le_refl 0)]
  simp

/-- Coefficients of `C * g(b)`. -/
lemma coeff_mul_subst {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) (P g : ℝ⟦X⟧) (m : ℕ) :
    coeff m (P * g.subst b) = ∑ j ∈ Finset.range (m + 1), coeff j g * coeff m (P * b ^ j) := by
  rw [coeff_mul]
  have : ∀ p ∈ Finset.antidiagonal m, coeff p.1 P * coeff p.2 (g.subst b) =
      ∑ j ∈ Finset.range (m + 1), coeff j g * (coeff p.1 P * coeff p.2 (b ^ j)) := by
    intro p hp
    rw [coeff_subst_eq_sum hb g (M := m) (by
      have := Finset.mem_antidiagonal.mp hp; lia), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, coeff_mul]

lemma subst_one' (b : ℝ⟦X⟧) (hb : constantCoeff b = 0) : (1 : ℝ⟦X⟧).subst b = 1 := by
  rw [← coe_substAlgHom (hasSubst_of_cc_zero hb), map_one]

lemma subst_X' (b : ℝ⟦X⟧) (hb : constantCoeff b = 0) : (X : ℝ⟦X⟧).subst b = b :=
  subst_X (hasSubst_of_cc_zero hb)

lemma subst_sub' (b : ℝ⟦X⟧) (hb : constantCoeff b = 0) (f g : ℝ⟦X⟧) :
    (f - g).subst b = f.subst b - g.subst b := by
  rw [← coe_substAlgHom (hasSubst_of_cc_zero hb), map_sub]

lemma subst_C' (b : ℝ⟦X⟧) (hb : constantCoeff b = 0) (r : ℝ) : (C r).subst b = C r := by
  rw [← coe_substAlgHom (hasSubst_of_cc_zero hb)]
  have : (C r : ℝ⟦X⟧) = algebraMap ℝ ℝ⟦X⟧ r := rfl
  rw [this, AlgHom.commutes]

/-- Square roots with equal nonzero constant term coincide. -/
lemma eq_of_sq_eq {u v : ℝ⟦X⟧} (h : u ^ 2 = v ^ 2) (hc : constantCoeff u = constantCoeff v)
    (hc0 : constantCoeff u ≠ 0) : u = v := by
  have h1 : (u - v) * (u + v) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exfalso
    have := congrArg constantCoeff h2
    rw [map_add, map_zero, ← hc] at this
    exact hc0 (by linarith)

lemma qS_subst_sinS : qS.subst sinS = cosS := by
  have hs := constantCoeff_sinS
  apply eq_of_sq_eq
  · rw [← subst_pow (hasSubst_of_cc_zero hs), qS_sq, subst_sub' _ hs, subst_one' _ hs,
      subst_pow (hasSubst_of_cc_zero hs), subst_X' _ hs]
    linear_combination -sinS_sq_add_cosS_sq
  · rw [constantCoeff_subst_eq hs, constantCoeff_qS, constantCoeff_cosS]
  · rw [constantCoeff_subst_eq hs, constantCoeff_qS]; norm_num

lemma invqS_subst_sinS : invqS.subst sinS = secS := by
  have hs := constantCoeff_sinS
  have h1 : invqS.subst sinS * cosS = 1 := by
    rw [← qS_subst_sinS, ← subst_mul (hasSubst_of_cc_zero hs), mul_comm, qS_mul_invqS,
      subst_one' _ hs]
  have h2 : secS * cosS = 1 := by rw [mul_comm]; exact cosS_mul_secS
  have hcos : cosS ≠ 0 := by
    intro h0; have := constantCoeff_cosS; rw [h0, map_zero] at this; exact zero_ne_one this
  exact mul_right_cancel₀ hcos (h1.trans h2.symm)

lemma fS_subst_sinS : fS.subst sinS = X := by
  have hs := constantCoeff_sinS
  apply derivative.ext
  · rw [derivative_subst (R := ℝ) (hasSubst_of_cc_zero hs), derivative_fS, invqS_subst_sinS,
      derivative_sinS, derivative_X, mul_comm, cosS_mul_secS]
  · rw [constantCoeff_subst_eq hs, constantCoeff_fS, constantCoeff_X]

end RealRooted.CenteredEulerian
