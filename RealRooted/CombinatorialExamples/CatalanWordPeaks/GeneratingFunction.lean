/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import RealRooted.Mathlib.RingTheory.PowerSeries.LagrangeInversion
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Lagrange inversion for the Catalan strict-peak coefficient formula

We use the auxiliary equation `V = z ((1+V)^2 + s V (1+V))` over `ℝ[s]`.
Specializing `s = (t-1)z` gives the desired quadratic equation for `1+V`.
The inversion coefficient is exactly the shifted binomial formula, with
length `n = m+i`. This route does not introduce a Catalan word model.

The scaled discriminant argument is adapted from ProgramComputer.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

The general fixed-point and inversion theorems are reused from
`RealRooted.Mathlib.RingTheory.PowerSeries.LagrangeInversion`.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.GeneratingFunction

open PowerSeries

/-- The polynomial kernel `(1+z)^2 + s z (1+z)` in Lagrange inversion. -/
def lagrangeKernel : PowerSeries (Polynomial ℝ) :=
  (1 + X) ^ 2 + C Polynomial.X * X * (1 + X)

/-- The auxiliary fixed point and its exact Lagrange coefficient identity. -/
theorem exists_series : ∃ V : PowerSeries (Polynomial ℝ),
    constantCoeff V = 0 ∧
      V = X * ((1 + V) ^ 2 + C Polynomial.X * V * (1 + V)) ∧
      ∀ m : ℕ, (m + 1 : Polynomial ℝ) * coeff (m + 1) V = coeff m (lagrangeKernel ^ (m + 1)) := by
  let c : PowerSeries (Polynomial ℝ) := C Polynomial.X
  let T : PowerSeries (Polynomial ℝ) → PowerSeries (Polynomial ℝ) :=
    fun V ↦ X * ((1 + V) ^ 2 + c * V * (1 + V))
  obtain ⟨V, hV0, hTV⟩ := exists_constantCoeff_eq_zero_apply_eq_self T
    (by intro a _; simp only [T, map_mul, constantCoeff_X, zero_mul])
    (by
      intro a b j _ _ hab
      have heq : T a - T b = (a - b) * X * (2 + a + b + c * (1 + a + b)) := by
        simp only [T]
        ring
      rw [heq, pow_succ]
      exact dvd_mul_of_dvd_left (mul_dvd_mul hab (dvd_refl X)) _)
  have hV : HasSubst V := HasSubst.of_constantCoeff_zero' hV0
  let σ := substAlgHom (R := Polynomial ℝ) hV
  have hσX : σ X = V := substAlgHom_X hV
  have hσc : σ c = c := by
    rw [coe_substAlgHom]
    exact subst_C _
  have hσφ : σ lagrangeKernel = (1 + V) ^ 2 + c * V * (1 + V) := by
    change σ ((1 + X) ^ 2 + c * X * (1 + X)) = _
    simp only [map_add, map_pow, map_mul, map_one, hσX, hσc]
  have hVX : V = X * σ lagrangeKernel := by
    rw [hσφ]
    exact hTV.symm
  obtain ⟨ρ, hρ⟩ : ∃ ρ : PowerSeries (Polynomial ℝ), ρ * lagrangeKernel = 1 := by
    have hu : IsUnit lagrangeKernel := by
      rw [isUnit_iff_constantCoeff]
      simp only [lagrangeKernel, map_add, map_pow, map_mul, constantCoeff_one,
        constantCoeff_X, add_zero, one_pow, mul_zero, zero_mul]
      exact isUnit_one
    obtain ⟨u, hu⟩ := hu
    exact ⟨↑u⁻¹, by rw [← hu]; simp⟩
  have hsubst : subst V (X * ρ) = X := by
    rw [← coe_substAlgHom hV, map_mul, hσX]
    calc
      V * σ ρ = X * (σ ρ * σ lagrangeKernel) := by rw [hVX]; ring
      _ = X := by rw [← map_mul, hρ, map_one, mul_one]
  refine ⟨V, hV0, hTV.symm, ?_⟩
  intro m
  have h := succ_mul_coeff_succ_subst ρ lagrangeKernel V X hρ hV0 hsubst m
  simpa only [subst_X hV, derivative_X, one_mul, Nat.cast_add, Nat.cast_one] using h

private lemma kernel_pow (p : ℕ) :
    lagrangeKernel ^ p = ∑ j ∈ Finset.range (p + 1),
      C (Polynomial.X ^ j * (p.choose j : Polynomial ℝ)) *
        X ^ j * (1 + X) ^ (2 * p - j) := by
  rw [lagrangeKernel, add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j ≤ p := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have he : j + 2 * (p - j) = 2 * p - j := by lia
  rw [← he]
  simp only [mul_pow, pow_mul, pow_add, map_mul, map_pow, map_natCast]
  ring

private lemma coeff_one_add_X_pow (a r : ℕ) :
    coeff r ((1 + X : PowerSeries (Polynomial ℝ)) ^ a) = (a.choose r : Polynomial ℝ) := by
  have h : (1 + X : PowerSeries (Polynomial ℝ)) ^ a =
      (((1 + Polynomial.X : Polynomial (Polynomial ℝ)) ^ a :
        Polynomial (Polynomial ℝ)) : PowerSeries (Polynomial ℝ)) := by
    simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- Both coefficients of the Lagrange kernel are ordinary binomial coefficients. -/
theorem coeff_coeff_kernel_pow (p m k : ℕ) :
    (coeff m (lagrangeKernel ^ p)).coeff k =
      if k ≤ m then (p.choose k : ℝ) * ((2 * p - k).choose (m - k) : ℝ) else 0 := by
  classical
  rw [kernel_pow, map_sum, Polynomial.finsetSum_coeff]
  have hterm : ∀ j ∈ Finset.range (p + 1),
      (coeff m (C (Polynomial.X ^ j * (p.choose j : Polynomial ℝ)) *
        X ^ j * (1 + X) ^ (2 * p - j))).coeff k =
      if k = j then
        if k ≤ m then (p.choose k : ℝ) * ((2 * p - k).choose (m - k) : ℝ) else 0
      else 0 := by
    intro j _
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    by_cases hj : j ≤ m
    · rw [ite_eq_left hj, coeff_one_add_X_pow]
      have he : Polynomial.X ^ j * (p.choose j : Polynomial ℝ) *
          ((2 * p - j).choose (m - j) : Polynomial ℝ) =
          Polynomial.C ((p.choose j : ℝ) * ((2 * p - j).choose (m - j) : ℝ)) *
            Polynomial.X ^ j := by
        simp only [map_mul, map_natCast]
        ring
      rw [he, Polynomial.coeff_C_mul_X_pow]
      by_cases hkj : k = j
      · subst k
        simp only [ite_true, ite_eq_left hj]
      · simp only [ite_eq_right hkj]
    · rw [ite_eq_right hj, mul_zero, Polynomial.coeff_zero]
      by_cases hkj : k = j
      · subst k
        simp only [ite_true, ite_eq_right hj]
      · simp only [ite_eq_right hkj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hk hkm
  · rfl
  · rfl
  · rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by lia : p < k), Nat.cast_zero, zero_mul]
  · rfl

/-- The auxiliary solution has the closed binomial coefficients needed for diagonalization. -/
theorem exists_series_coefficients : ∃ V : PowerSeries (Polynomial ℝ),
    constantCoeff V = 0 ∧
      V = X * ((1 + V) ^ 2 + C Polynomial.X * V * (1 + V)) ∧
      ∀ m k : ℕ, (coeff (m + 1) V).coeff k =
        if k ≤ m then
          ((m + 1).choose k : ℝ) * ((2 * (m + 1) - k).choose (m - k) : ℝ) /
            (m + 1 : ℕ) else 0 := by
  obtain ⟨V, h0, heq, hc⟩ := exists_series
  refine ⟨V, h0, heq, fun m k ↦ ?_⟩
  have h := congrArg (fun q : Polynomial ℝ ↦ q.coeff k) (hc m)
  rw [← Nat.cast_one, ← Nat.cast_add, Polynomial.coeff_natCast_mul,
    coeff_coeff_kernel_pow] at h
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  split_ifs at h ⊢ with hk
  · apply (eq_div_iff hm).mpr
    simpa only [mul_comm] using h
  · exact (mul_eq_zero.mp h).resolve_left hm

end RealRooted.CatalanWordPeaks.GeneratingFunction

namespace RealRooted.CatalanWordPeaks.GeneratingFunction

open PowerSeries Finset

/-- Translate a natural antidiagonal sum by fixed lower bounds on its coordinates. -/
theorem sum_antidiagonal_shift {A : Type*} [AddCommMonoid A] (F : ℕ → ℕ → A)
    (n k₁ k₂ : ℕ) :
    ∑ p ∈ antidiagonal n, (if k₁ ≤ p.1 ∧ k₂ ≤ p.2 then F (p.1 - k₁) (p.2 - k₂) else 0) =
      if k₁ + k₂ ≤ n then ∑ q ∈ antidiagonal (n - (k₁ + k₂)), F q.1 q.2 else 0 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  split_ifs with h
  · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    obtain ⟨m, rfl⟩ : ∃ m, n = k₁ + m + k₂ := ⟨n - k₁ - k₂, by lia⟩
    rw [show k₁ + m + k₂ - (k₁ + k₂) = m by lia, Nat.succ_eq_add_one,
      Nat.succ_eq_add_one, show k₁ + m + k₂ + 1 = k₁ + ((m + 1) + k₂) by lia,
      sum_range_add, sum_range_add]
    rw [sum_eq_zero (fun a ha ↦ by rw [mem_range] at ha; rw [ite_eq_right (by lia)]), zero_add]
    rw [sum_eq_zero (s := range k₂)
      (fun a ha ↦ by rw [mem_range] at ha; rw [ite_eq_right (by lia)]), add_zero]
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    rw [ite_eq_left (by lia)]
    congr 1 <;> lia
  · exact sum_eq_zero (fun a ha ↦ by rw [mem_range] at ha; rw [ite_eq_right (by lia)])

variable {A : Type*} [CommRing A]

/-- The specialization `s ↦ sz` of a power series with coefficients in `A[s]`. -/
def diagonal (f : PowerSeries (Polynomial A)) : PowerSeries (Polynomial A) :=
  mk fun n ↦ ∑ p ∈ antidiagonal n, Polynomial.monomial p.2 ((coeff p.1 f).coeff p.2)

/-- The coefficient of the diagonal specialization shifts the length by the parameter degree. -/
theorem coeff_diagonal (f : PowerSeries (Polynomial A)) (n k : ℕ) :
    (coeff n (diagonal f)).coeff k = if k ≤ n then (coeff (n - k) f).coeff k else 0 := by
  classical
  rw [diagonal, coeff_mk, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
  split_ifs with h
  · rw [sum_eq_single (n - k, k)]
    · simp
    · rintro ⟨a, b⟩ hab hne
      rw [HasAntidiagonal.mem_antidiagonal] at hab
      rw [ite_eq_right]
      exact fun hb ↦ hne (Prod.ext (by lia) hb)
    · exact fun hn ↦ (hn (HasAntidiagonal.mem_antidiagonal.mpr (by lia))).elim
  · apply sum_eq_zero
    rintro ⟨a, b⟩ hab
    rw [HasAntidiagonal.mem_antidiagonal] at hab
    rw [ite_eq_right (by lia)]

private lemma diagonal_add (f g : PowerSeries (Polynomial A)) :
    diagonal (f + g) = diagonal f + diagonal g := by
  ext n k
  simp only [map_add, Polynomial.coeff_add, coeff_diagonal]
  split_ifs <;> simp

private lemma diagonal_mul (f g : PowerSeries (Polynomial A)) :
    diagonal (f * g) = diagonal f * diagonal g := by
  classical
  ext n k
  rw [coeff_diagonal]
  conv_rhs => rw [coeff_mul, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul, coeff_diagonal]
  rw [sum_comm (s := antidiagonal n)]
  have h : ∀ x ∈ antidiagonal k, (∑ p ∈ antidiagonal n,
      (if x.1 ≤ p.1 then (coeff (p.1 - x.1) f).coeff x.1 else 0) *
      (if x.2 ≤ p.2 then (coeff (p.2 - x.2) g).coeff x.2 else 0)) =
      if k ≤ n then ∑ q ∈ antidiagonal (n - k),
        (coeff q.1 f).coeff x.1 * (coeff q.2 g).coeff x.2 else 0 := by
    intro x hx
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    rw [← hx, ← sum_antidiagonal_shift
      (fun i j ↦ (coeff i f).coeff x.1 * (coeff j g).coeff x.2)]
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp_all
  rw [sum_congr rfl h]
  split_ifs with hkn
  · rw [coeff_mul, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_mul]
    rw [sum_comm]
  · simp

private lemma diagonal_one : diagonal (1 : PowerSeries (Polynomial A)) = 1 := by
  ext n k
  rw [coeff_diagonal]
  by_cases hn : n = 0
  · subst n
    rcases k with _ | k <;> simp [Polynomial.coeff_one]
  · conv_rhs => rw [coeff_one, ite_eq_right hn, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [coeff_one]
      split_ifs with h0
      · rw [Polynomial.coeff_one, ite_eq_right (by lia)]
      · rw [Polynomial.coeff_zero]
    · rfl

/-- Diagonal specialization respects every polynomial equation in the series. -/
def diagonalHom : PowerSeries (Polynomial A) →+* PowerSeries (Polynomial A) where
  toFun := diagonal
  map_zero' := by ext n k; simp [coeff_diagonal]
  map_one' := by exact diagonal_one
  map_add' := by exact diagonal_add
  map_mul' := by exact diagonal_mul

/-- Diagonal specialization fixes the length variable. -/
theorem diagonalHom_X : diagonalHom (X : PowerSeries (Polynomial A)) = X := by
  ext n k
  rw [show diagonalHom X = diagonal X from rfl, coeff_diagonal]
  by_cases hn : n = 1
  · subst n
    rcases k with _ | _ | k <;> simp [Polynomial.coeff_one]
  · conv_rhs => rw [coeff_X, ite_eq_right hn, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [coeff_X]
      split_ifs with h0
      · rw [Polynomial.coeff_one, ite_eq_right (by lia)]
      · rw [Polynomial.coeff_zero]
    · rfl

/-- The parameter acquires one power of the length variable. -/
theorem diagonalHom_C_X : diagonalHom (C Polynomial.X : PowerSeries (Polynomial A)) =
    C Polynomial.X * X := by
  ext n k
  rw [show diagonalHom (C Polynomial.X) = diagonal (C Polynomial.X) from rfl,
    coeff_diagonal, coeff_C_mul, coeff_X]
  by_cases hn : n = 1
  · subst n
    rcases k with _ | _ | k <;> simp [coeff_C, Polynomial.coeff_X]
  · rw [ite_eq_right hn, mul_zero, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [coeff_C]
      by_cases h0 : n - k = 0
      · rw [ite_eq_left h0, Polynomial.coeff_X, ite_eq_right (by lia)]
      · rw [ite_eq_right h0, Polynomial.coeff_zero]
    · rfl

end RealRooted.CatalanWordPeaks.GeneratingFunction

namespace RealRooted.CatalanWordPeaks.GeneratingFunction

open PowerSeries Finset

/-- The length generating series of the explicitly defined strict-peak rows. -/
def series : PowerSeries (Polynomial ℝ) := mk polynomial

private lemma coeff_diagonal_series {V : PowerSeries (Polynomial ℝ)}
    (h0 : constantCoeff V = 0)
    (hc : ∀ m k : ℕ, (coeff (m + 1) V).coeff k =
      if k ≤ m then
        ((m + 1).choose k : ℝ) * ((2 * (m + 1) - k).choose (m - k) : ℝ) /
          (m + 1 : ℕ) else 0)
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (coeff n (diagonal V)).coeff k =
      if k ≤ rowDegree n then (shiftedCoefficient n k : ℝ) else 0 := by
  rw [coeff_diagonal]
  by_cases hk : k ≤ rowDegree n
  · have hkn : k ≤ n := by unfold rowDegree at hk; lia
    have hnk : n - k = (n - k - 1) + 1 := by unfold rowDegree at hk; lia
    have hkm : k ≤ n - k - 1 := by unfold rowDegree at hk; lia
    rw [ite_eq_left hkn, ite_eq_left hk, hnk, hc, ite_eq_left hkm,
      shiftedCoefficient_eq]
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    rw [hnk.symm, show 2 * (n - k) - k = 2 * n - 3 * k by lia,
      show n - k - 1 - k = n - 2 * k - 1 by lia]
  · rw [ite_eq_right hk]
    by_cases hkn : k ≤ n
    · rw [ite_eq_left hkn]
      rcases he : n - k with _ | m
      · rw [coeff_zero_eq_constantCoeff_apply, h0, Polynomial.coeff_zero]
      · have hkm : ¬ k ≤ m := by unfold rowDegree at hk; lia
        rw [hc, ite_eq_right hkm]
    · rw [ite_eq_right hkn]

private lemma diagonal_series_eq {V : PowerSeries (Polynomial ℝ)}
    (h0 : constantCoeff V = 0)
    (hc : ∀ m k : ℕ, (coeff (m + 1) V).coeff k =
      if k ≤ m then
        ((m + 1).choose k : ℝ) * ((2 * (m + 1) - k).choose (m - k) : ℝ) /
          (m + 1 : ℕ) else 0) :
    map (Polynomial.compRingHom (Polynomial.X - 1)) (1 + diagonal V) = series := by
  apply PowerSeries.ext
  intro n
  rw [coeff_map, series, coeff_mk, map_add, coeff_one]
  by_cases hn : n = 0
  · subst n
    have hz : coeff 0 (diagonal V) = 0 := by
      ext k
      rw [coeff_diagonal]
      rcases k with _ | k
      · simp only [le_refl, ite_true, Nat.sub_zero, coeff_zero_eq_constantCoeff_apply,
          h0, Polynomial.coeff_zero]
      · simp
    simp only [hz, ite_true, add_zero, map_one, polynomial]
  · rw [ite_eq_right hn, zero_add]
    have he : coeff n (diagonal V) = ∑ i ∈ range (rowDegree n + 1),
        Polynomial.C (shiftedCoefficient n i : ℝ) * Polynomial.X ^ i := by
      ext k
      rw [coeff_diagonal_series h0 hc hn, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [sum_ite_eq]
      simp only [mem_range, Nat.lt_succ_iff]
    rw [he, polynomial, ite_eq_right hn, map_sum]
    apply sum_congr rfl
    intro i _
    simp only [map_mul, map_pow, Polynomial.coe_compRingHom_apply, Polynomial.C_comp,
      Polynomial.X_comp]

/-- The row generating function satisfies the published quadratic identity. -/
theorem series_eq :
    series = 1 + C (1 - Polynomial.X) * X ^ 2 * series +
      X * (1 + C (Polynomial.X - 1) * X) * series ^ 2 := by
  obtain ⟨V, h0, hV, hc⟩ := exists_series_coefficients
  have hD := congrArg diagonalHom hV
  simp only [map_mul, map_add, map_pow, map_one, diagonalHom_X, diagonalHom_C_X] at hD
  have hG : 1 + diagonal V =
      1 + X * ((1 + diagonal V) ^ 2 + C Polynomial.X * X * diagonal V * (1 + diagonal V)) := by
    exact congrArg (1 + ·) hD
  have hmap := congrArg (map (Polynomial.compRingHom (Polynomial.X - 1))) hG
  rw [diagonal_series_eq h0 hc] at hmap
  simp only [map_add, map_mul, map_pow, map_one, map_X, map_C,
    Polynomial.coe_compRingHom_apply, Polynomial.X_comp] at hmap
  have hmapD : map (Polynomial.compRingHom (Polynomial.X - 1)) (diagonal V) = series - 1 := by
    have he := diagonal_series_eq h0 hc
    rw [map_add, map_one] at he
    linear_combination he
  rw [hmapD] at hmap
  simp only [map_sub, map_one] at hmap ⊢
  linear_combination hmap

end RealRooted.CatalanWordPeaks.GeneratingFunction

namespace RealRooted.CatalanWordPeaks.GeneratingFunction

open PowerSeries Polynomial

private def specialization (c : ℝ) : PowerSeries (Polynomial ℝ) →+* PowerSeries ℝ :=
  (PowerSeries.rescale c).comp (PowerSeries.map (evalRingHom (1 - (c ^ 2)⁻¹)))

/-- The generating series with coefficients `cⁿ Cₙ(1-c⁻²)`. -/
def scaled (c : ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale c (PowerSeries.map (evalRingHom (1 - (c ^ 2)⁻¹)) series)

/-- The exact coefficients in the scaled analytic parameter. -/
theorem coeff_scaled (c : ℝ) (n : ℕ) :
    PowerSeries.coeff n (scaled c) = c ^ n * (polynomial n).eval (1 - (c ^ 2)⁻¹) := by
  simp [scaled, PowerSeries.coeff_rescale, series]

private lemma specialization_C (c : ℝ) (p : Polynomial ℝ) :
    specialization c (PowerSeries.C p) = PowerSeries.C (p.eval (1 - (c ^ 2)⁻¹)) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0 <;> simp [specialization, PowerSeries.coeff_rescale, PowerSeries.coeff_C, hn]

private lemma specialization_X (c : ℝ) :
    specialization c PowerSeries.X = PowerSeries.C c * PowerSeries.X := by
  simp [specialization]

/-- The quadratic equation after scaling the length variable. -/
theorem scaled_eq (c : ℝ) (hc : c ≠ 0) :
    scaled c = 1 + PowerSeries.X ^ 2 * scaled c +
      PowerSeries.X * (PowerSeries.C c - PowerSeries.X) * scaled c ^ 2 := by
  have h := congrArg (specialization c) series_eq
  simp only [map_add, map_mul, map_pow, map_one, specialization_C, specialization_X,
    eval_sub, eval_one, eval_X] at h
  have hPos : 1 - (1 - (c ^ 2)⁻¹) = (c ^ 2)⁻¹ := by ring
  have hNeg : 1 - (c ^ 2)⁻¹ - 1 = -(c ^ 2)⁻¹ := by ring
  rw [hPos, hNeg, map_neg] at h
  have hcoeff : PowerSeries.C ((c ^ 2)⁻¹) * (PowerSeries.C c) ^ 2 = 1 := by
    rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), map_one]
  have heq : specialization c series = scaled c := rfl
  rw [heq] at h
  linear_combination h + (PowerSeries.X ^ 2 * scaled c * (1 - scaled c)) * hcoeff

/-- The formal square-root branch with constant term one. -/
def discriminantBranch (c : ℝ) : PowerSeries ℝ :=
  1 - PowerSeries.X ^ 2 -
    2 * PowerSeries.X * (PowerSeries.C c - PowerSeries.X) * scaled c

/-- The selected formal square-root branch starts at one. -/
theorem discriminantBranch_constant (c : ℝ) :
    PowerSeries.constantCoeff (discriminantBranch c) = 1 := by
  simp [discriminantBranch]

/-- The scaled generating function gives the exact quartic discriminant. -/
theorem discriminantBranch_square (c : ℝ) (hc : c ≠ 0) :
    discriminantBranch c ^ 2 =
      (1 + PowerSeries.X ^ 2) ^ 2 - 4 * PowerSeries.C c * PowerSeries.X := by
  have h := scaled_eq c hc
  simp only [discriminantBranch]
  linear_combination
    -(4 * PowerSeries.X * (PowerSeries.C c - PowerSeries.X)) * h

end RealRooted.CatalanWordPeaks.GeneratingFunction
