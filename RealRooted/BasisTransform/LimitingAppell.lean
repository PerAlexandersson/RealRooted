module

public import RealRooted.BasisTransform.AppellRigidity

import RealRooted.BasisTransform.AppellTranslationRigidity
import RealRooted.RootContinuity
import RealRooted.Linear
import RealRooted.Hadamard.Newton
import RealRooted.Maclaurin
import RealRooted.Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import RealRooted.Mathlib.Algebra.Polynomial.Expand.Splits
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import RealRooted.Mathlib.RingTheory.Polynomial.Vieta

/-!
# Limiting Appell polynomials of a root-preserving basis map

This file develops the finite limiting polynomial attached to the even
differential coefficients of a degree-triangular polynomial basis.
-/

public section

open Finset Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The square-parameter rescaling of a basis transform used in the limiting
argument, with `r = (m + 1) ^ 2`. -/
def rescaledBasisPower (B : ℕ → ℝ[X]) (N m : ℕ) : ℝ[X] :=
  let s : ℝ := m + 1
  C ((s ^ N)⁻¹) *
    (basisTransform B ((X + C (s ^ 2)) ^ N)).comp
      (C (-(s ^ 2)) + C s * X)

/-- The limiting Appell polynomial determined by the even differential
coefficients `d`. -/
def limitingAppellPolynomial (d : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  ∑ j ∈ range (N / 2 + 1),
    C ((-1 : ℝ) ^ j * (N.descFactorial (2 * j) : ℝ) * d j) * X ^ (N - 2 * j)

private def scaledAppellCoefficient (q : ℝ[X]) (k : ℕ) (t : ℝ) : ℝ[X] :=
  ∑ l ∈ range (k / 2 + 1),
    C (q.coeff l * t ^ (k - 2 * l)) * (C (-1) + C t * X) ^ l

private theorem coeff_affine_pow (t : ℝ) (l i : ℕ) :
    ((C (-1) + C t * X) ^ l : ℝ[X]).coeff i =
      if i ≤ l then (l.choose i : ℝ) * (-1 : ℝ) ^ (l - i) * t ^ i else 0 := by
  rw [add_pow, finsetSum_coeff]
  have hsummand (j : ℕ) :
      (C (-1) ^ j * (C t * X) ^ (l - j) * (l.choose j : ℝ[X])) =
        C ((l.choose j : ℝ) * (-1 : ℝ) ^ j * t ^ (l - j)) * X ^ (l - j) := by
    simp [C_mul, C_pow]
    ring
  by_cases hil : i ≤ l
  · rw [Finset.sum_eq_single (l - i)]
    · rw [hsummand, coeff_C_mul_X_pow]
      simp [hil, Nat.choose_symm hil, Nat.sub_sub_self hil]
    · intro j hj hjli
      rw [hsummand, coeff_C_mul_X_pow, ite_eq_right]
      have hjle : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact fun h => hjli (by lia)
    · simp [hil]
  · rw [ite_eq_right hil]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsummand, coeff_C_mul_X_pow, ite_eq_right]
    intro h
    have := Finset.mem_range.mp hj
    lia

private theorem coeff_scaledAppellCoefficient (q : ℝ[X]) (k i : ℕ) (t : ℝ) :
    (scaledAppellCoefficient q k t).coeff i =
      ∑ l ∈ range (k / 2 + 1),
        if i ≤ l then
          q.coeff l * (l.choose i : ℝ) * (-1 : ℝ) ^ (l - i) *
            t ^ (k - 2 * l + i)
        else 0 := by
  rw [scaledAppellCoefficient, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro l hl
  rw [coeff_C_mul, coeff_affine_pow]
  split_ifs <;> ring

private theorem scaledAppellCoefficient_eq
    {q : ℝ[X]} {k : ℕ} (hq : q.natDegree ≤ k / 2) {s : ℝ} (hs : s ≠ 0) :
    C ((s ^ k)⁻¹) * q.comp (C (-(s ^ 2)) + C s * X) =
      scaledAppellCoefficient q k s⁻¹ := by
  have hqsum := q.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hq)
  conv_lhs => rw [hqsum]
  rw [Polynomial.sum_comp, Finset.mul_sum, scaledAppellCoefficient]
  apply Finset.sum_congr rfl
  intro l hl
  have hlle : 2 * l ≤ k := by
    have := Finset.mem_range.mp hl
    lia
  have haffine :
      C (-(s ^ 2)) + C s * X = C (s ^ 2) * (C (-1) + C s⁻¹ * X) := by
    rw [mul_add, ← C_mul, ← mul_assoc, ← C_mul]
    rw [show s ^ 2 * (-1) = -(s ^ 2) by ring,
      show s ^ 2 * s⁻¹ = s by field_simp]
  rw [mul_comp, C_comp, pow_comp, X_comp, haffine, mul_pow, ← C_pow]
  calc
    _ = C ((s ^ k)⁻¹ * q.coeff l * (s ^ 2) ^ l) *
        (C (-1) + C s⁻¹ * X) ^ l := by
      rw [show C ((s ^ k)⁻¹) *
          (C (q.coeff l) *
            (C ((s ^ 2) ^ l) * (C (-1) + C s⁻¹ * X) ^ l)) =
          (C ((s ^ k)⁻¹) * C (q.coeff l) * C ((s ^ 2) ^ l)) *
            (C (-1) + C s⁻¹ * X) ^ l by ring]
      rw [← C_mul, ← C_mul]
    _ = C (q.coeff l * s⁻¹ ^ (k - 2 * l)) *
        (C (-1) + C s⁻¹ * X) ^ l := by
      congr 2
      rw [show (s ^ 2) ^ l = s ^ (2 * l) by rw [← pow_mul],
        inv_pow_sub₀ hs hlle]
      ring

private theorem tendsto_coeff_scaledAppellCoefficient
    (q : ℝ[X]) (k i : ℕ) {ι : Type*} {f : Filter ι} {t : ι → ℝ}
    (ht : Tendsto t f (nhds 0)) :
    Tendsto (fun a => (scaledAppellCoefficient q k (t a)).coeff i) f
      (nhds ((scaledAppellCoefficient q k 0).coeff i)) := by
  simp only [coeff_scaledAppellCoefficient]
  apply tendsto_finsetSum
  intro l hl
  by_cases hil : i ≤ l
  · simp only [hil, ite_true]
    exact tendsto_const_nhds.mul (ht.pow (k - 2 * l + i))
  · simp only [hil, ite_false]
    exact tendsto_const_nhds

private theorem scaledAppellCoefficient_zero (q : ℝ[X]) (k : ℕ) :
    scaledAppellCoefficient q k 0 =
      if Even k then C ((-1 : ℝ) ^ (k / 2) * q.coeff (k / 2)) else 0 := by
  by_cases hk : Even k
  · obtain ⟨j, hj⟩ := hk
    have hkform : k = 2 * j := by lia
    subst k
    rw [hkform, ite_eq_left (even_two_mul j), scaledAppellCoefficient]
    simp only [show (2 * j) / 2 + 1 = j + 1 by lia]
    rw [Finset.sum_eq_single j]
    · simp only [Nat.sub_self, pow_zero, mul_one, map_zero, zero_mul, add_zero,
        show 2 * j / 2 = j by lia]
      rw [← C_pow, ← C_mul]
      congr 1
      ring
    · intro l hl hlj
      have hlle : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have hlt : l < j := lt_of_le_of_ne hlle hlj
      have hzero : (0 : ℝ) ^ (2 * j - 2 * l) = 0 := zero_pow (by lia)
      rw [hzero]
      simp
    · simp
  · rw [ite_eq_right hk]
    have hkodd := Nat.not_even_iff_odd.mp hk
    obtain ⟨j, rfl⟩ := hkodd
    rw [scaledAppellCoefficient]
    simp only [show (2 * j + 1) / 2 + 1 = j + 1 by lia]
    apply Finset.sum_eq_zero
    intro l hl
    have hlle : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hne : 2 * j + 1 - 2 * l ≠ 0 := by lia
    have hzero : (0 : ℝ) ^ (2 * j + 1 - 2 * l) = 0 := zero_pow hne
    rw [hzero]
    simp

private theorem rescaledBasisPower_eq_sum_scaled
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (N m : ℕ) :
    rescaledBasisPower P N m =
      ∑ k ∈ range (N + 1),
        C (N.descFactorial k : ℝ) *
          (scaledAppellCoefficient (appellCoefficient P k) k ((m + 1 : ℕ) : ℝ)⁻¹ *
            X ^ (N - k)) := by
  let s : ℝ := m + 1
  have hs : s ≠ 0 := by positivity
  have hQdeg := appellCoefficient_natDegree_le hPdeg hPmonic hpres
  have hinputdeg : ((X + C (s ^ 2)) ^ N : ℝ[X]).natDegree ≤ N := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have hexpand := basisTransform_eq_sum_iterate_derivative_of_isAppellExpansion
    (isAppellExpansion_appellCoefficient P) hPdeg hQdeg hinputdeg
  rw [rescaledBasisPower]
  change C ((s ^ N)⁻¹) *
      (basisTransform P ((X + C (s ^ 2)) ^ N)).comp
        (C (-(s ^ 2)) + C s * X) = _
  rw [show (((m + 1 : ℕ) : ℝ)) = s by simp [s]]
  rw [hexpand, Polynomial.sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_comp, iterate_derivative_X_add_pow]
  rw [show N.descFactorial k • (X + C (s ^ 2)) ^ (N - k) =
      C (N.descFactorial k : ℝ) * (X + C (s ^ 2)) ^ (N - k) by
    rw [nsmul_eq_mul, ← C_eq_natCast]]
  rw [mul_comp, C_comp, pow_comp, add_comp, X_comp, C_comp]
  have hcancel :
      C (-(s ^ 2)) + C s * X + C (s ^ 2) = C s * X := by
    calc
      _ = (C (-(s ^ 2)) + C (s ^ 2)) + C s * X := by ring
      _ = _ := by rw [← C_add]; simp
  rw [hcancel, mul_pow, ← C_pow]
  have hscaled := scaledAppellCoefficient_eq (hQdeg k) hs
  have hscalar : (s ^ N)⁻¹ * s ^ (N - k) = (s ^ k)⁻¹ := by
    have hpow : s ^ N = s ^ (N - k) * s ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    rw [hpow]
    field_simp
  calc
    _ = C (N.descFactorial k : ℝ) *
        ((C ((s ^ N)⁻¹) * C (s ^ (N - k))) *
          (appellCoefficient P k).comp (C (-(s ^ 2)) + C s * X) *
            X ^ (N - k)) := by ring
    _ = C (N.descFactorial k : ℝ) *
        ((C ((s ^ k)⁻¹) *
          (appellCoefficient P k).comp (C (-(s ^ 2)) + C s * X)) *
            X ^ (N - k)) := by rw [← C_mul, hscalar]
    _ = _ := by rw [hscaled]

private theorem sum_scaledAppellCoefficient_zero_eq_limiting
    (Q : ℕ → ℝ[X]) (N : ℕ) :
    ∑ k ∈ range (N + 1),
        C (N.descFactorial k : ℝ) *
          (scaledAppellCoefficient (Q k) k 0 * X ^ (N - k)) =
      limitingAppellPolynomial (fun j => (Q (2 * j)).coeff j) N := by
  simp_rw [scaledAppellCoefficient_zero]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  change (∑ k ∈ range (N + 1), if Even k then
      C (N.descFactorial k : ℝ) *
        (C ((-1 : ℝ) ^ (k / 2) * (Q k).coeff (k / 2)) * X ^ (N - k))
      else 0) = _
  rw [← Finset.sum_filter]
  rw [limitingAppellPolynomial]
  symm
  apply Finset.sum_bij (fun j _ => 2 * j)
  · intro j hj
    simp only [mem_filter, mem_range, even_two_mul, and_true]
    have := Finset.mem_range.mp hj
    lia
  · intro i hi j hj hij
    lia
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    obtain ⟨j, hj⟩ := hk.2
    refine ⟨j, Finset.mem_range.mpr ?_, ?_⟩
    · lia
    · lia
  · intro j hj
    simp only [show 2 * j / 2 = j by lia]
    rw [show C (N.descFactorial (2 * j) : ℝ) *
        (C ((-1 : ℝ) ^ j * (Q (2 * j)).coeff j) * X ^ (N - 2 * j)) =
      (C (N.descFactorial (2 * j) : ℝ) *
        C ((-1 : ℝ) ^ j * (Q (2 * j)).coeff j)) * X ^ (N - 2 * j) by ring]
    rw [← C_mul]
    rw [show (-1 : ℝ) ^ j * (N.descFactorial (2 * j) : ℝ) *
        (Q (2 * j)).coeff j =
      (N.descFactorial (2 * j) : ℝ) *
        ((-1 : ℝ) ^ j * (Q (2 * j)).coeff j) by ring]

/-- The coefficient formula defining the limiting Appell polynomial. -/
theorem coeff_limitingAppellPolynomial (d : ℕ → ℝ) (N k : ℕ) :
    (limitingAppellPolynomial d N).coeff k =
      ∑ j ∈ range (N / 2 + 1),
        if N - 2 * j = k then
          (-1 : ℝ) ^ j * (N.descFactorial (2 * j) : ℝ) * d j
        else 0 := by
  rw [limitingAppellPolynomial, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp_all

private theorem tendsto_inv_nat_succ :
    Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
  have heq : (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹) =
      (fun n : ℕ => ((n : ℝ)⁻¹)) ∘ fun n => n + 1 := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [heq]
  exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (Filter.tendsto_add_atTop_nat 1)

/-- The square-parameter rescalings converge coefficientwise to the limiting
Appell polynomial defined by the even top differential coefficients. -/
theorem tendsto_coeff_rescaledBasisPower
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (N i : ℕ) :
    Tendsto (fun m => (rescaledBasisPower P N m).coeff i) atTop
      (nhds ((limitingAppellPolynomial
        (fun j => (appellCoefficient P (2 * j)).coeff j) N).coeff i)) := by
  have hrepr : (fun m => (rescaledBasisPower P N m).coeff i) =
      fun m => (∑ k ∈ range (N + 1),
        C (N.descFactorial k : ℝ) *
          (scaledAppellCoefficient (appellCoefficient P k) k
            (((m + 1 : ℕ) : ℝ))⁻¹ * X ^ (N - k))).coeff i := by
    funext m
    rw [rescaledBasisPower_eq_sum_scaled hPdeg hPmonic hpres]
  rw [hrepr]
  have hsum : Tendsto (fun m => (∑ k ∈ range (N + 1),
      C (N.descFactorial k : ℝ) *
        (scaledAppellCoefficient (appellCoefficient P k) k
          (((m + 1 : ℕ) : ℝ))⁻¹ * X ^ (N - k))).coeff i) atTop
      (nhds ((∑ k ∈ range (N + 1),
        C (N.descFactorial k : ℝ) *
          (scaledAppellCoefficient (appellCoefficient P k) k 0 *
            X ^ (N - k))).coeff i)) := by
    simp only [finsetSum_coeff, coeff_C_mul, coeff_mul_X_pow']
    apply tendsto_finsetSum
    intro k hk
    by_cases hki : N - k ≤ i
    · simp only [hki, ite_true]
      exact tendsto_const_nhds.mul
        (tendsto_coeff_scaledAppellCoefficient _ _ _ tendsto_inv_nat_succ)
    · simp only [hki, ite_false, mul_zero]
      exact tendsto_const_nhds
  rw [sum_scaledAppellCoefficient_zero_eq_limiting] at hsum
  exact hsum

private theorem coeff_zero_appellCoefficient_zero_eq_one
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) :
    (appellCoefficient P 0).coeff 0 = 1 := by
  have hQdeg := appellCoefficient_natDegree_le hPdeg hPmonic hpres
  have hexpand := eq_sum_of_isAppellExpansion_of_natDegree_le
    (isAppellExpansion_appellCoefficient P) hPdeg hQdeg (Nat.le_refl 0)
  have hPzero : P 0 = 1 :=
    eq_one_of_monic_natDegree_zero (hPmonic 0) (hPdeg 0)
  norm_num [Finset.sum_range_succ] at hexpand
  rw [← hexpand, hPzero]
  norm_num

private theorem rescaledBasisPower_splits
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (N m : ℕ) : (rescaledBasisPower P N m).Splits := by
  let s : ℝ := m + 1
  have hs : s ≠ 0 := by positivity
  let G := basisTransform P ((X + C (s ^ 2)) ^ N)
  have hinput : ((X + C (s ^ 2)) ^ N : ℝ[X]).Splits :=
    (Polynomial.Splits.X_add_C (s ^ 2)).pow N
  have hroots : ∀ x ∈ ((X + C (s ^ 2)) ^ N : ℝ[X]).roots, x ≤ 0 := by
    intro x hx
    rw [roots_pow, roots_X_add_C] at hx
    have hx' : x = -(s ^ 2) :=
      Multiset.mem_singleton.mp (Multiset.mem_nsmul.mp hx).2
    rw [hx']
    exact neg_nonpos.mpr (sq_nonneg s)
  have hGs : G.Splits := hpres _ hinput hroots
  have hGm : G.Monic := basisTransform_monic_of_monic hPdeg hPmonic
    ((monic_X_add_C (s ^ 2)).pow N)
  have hshift := isRealRooted_comp_X_add_C hGm.ne_zero hGs (-(s ^ 2))
  have hscale := isRealRooted_comp_C_mul_X hshift.1 hshift.2 hs
  have haffine :
      (X + C (-(s ^ 2))).comp (C s * X) = C (-(s ^ 2)) + C s * X := by
    rw [add_comp, X_comp, C_comp, add_comm]
  rw [rescaledBasisPower]
  change (C ((s ^ N)⁻¹) * G.comp (C (-(s ^ 2)) + C s * X)).Splits
  rw [← haffine, ← comp_assoc]
  exact hscale.2.C_mul _

private theorem rescaledBasisPower_monic
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) (N m : ℕ) :
    (rescaledBasisPower P N m).Monic := by
  let s : ℝ := m + 1
  have hs : s ≠ 0 := by positivity
  let G := basisTransform P ((X + C (s ^ 2)) ^ N)
  let a : ℝ[X] := C (-(s ^ 2)) + C s * X
  have hinputm : ((X + C (s ^ 2)) ^ N : ℝ[X]).Monic :=
    (monic_X_add_C (s ^ 2)).pow N
  have hGm : G.Monic := basisTransform_monic_of_monic hPdeg hPmonic hinputm
  have hGdeg : G.natDegree = N := by
    change (basisTransform P ((X + C (s ^ 2)) ^ N)).natDegree = N
    rw [basisTransform_natDegree_eq hPdeg (fun n => (hPmonic n).ne_zero)
      hinputm.ne_zero, natDegree_pow, natDegree_X_add_C, mul_one]
  have hadeg : a.natDegree = 1 := by
    change (C (-(s ^ 2)) + C s * X).natDegree = 1
    rw [show C (-(s ^ 2)) + C s * X = C s * X + C (-(s ^ 2)) by ring,
      natDegree_linear hs]
  have halead : a.leadingCoeff = s := by
    change (C (-(s ^ 2)) + C s * X).leadingCoeff = s
    rw [show C (-(s ^ 2)) + C s * X = C s * X + C (-(s ^ 2)) by ring,
      leadingCoeff_linear hs]
  apply monic_of_natDegree_le_of_coeff_eq_one N
  · rw [rescaledBasisPower]
    change (C ((s ^ N)⁻¹) * G.comp a).natDegree ≤ N
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_comp, hGdeg, hadeg, mul_one])
  · rw [rescaledBasisPower]
    change (C ((s ^ N)⁻¹) * G.comp a).coeff N = 1
    rw [coeff_C_mul]
    have htop := coeff_comp_degree_mul_degree (p := G) (q := a) (by simp [hadeg])
    rw [hGdeg, hadeg, mul_one, hGm.leadingCoeff, halead] at htop
    rw [htop]
    simpa using inv_mul_cancel₀ (pow_ne_zero N hs)

private theorem rescaledBasisPower_natDegree
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) (N m : ℕ) :
    (rescaledBasisPower P N m).natDegree = N := by
  let s : ℝ := m + 1
  have hs : s ≠ 0 := by positivity
  let a : ℝ[X] := C (-(s ^ 2)) + C s * X
  have hadeg : a.natDegree = 1 := by
    change (C (-(s ^ 2)) + C s * X).natDegree = 1
    rw [show C (-(s ^ 2)) + C s * X = C s * X + C (-(s ^ 2)) by ring,
      natDegree_linear hs]
  have hinputm : ((X + C (s ^ 2)) ^ N : ℝ[X]).Monic :=
    (monic_X_add_C (s ^ 2)).pow N
  rw [rescaledBasisPower]
  change (C ((s ^ N)⁻¹) *
    (basisTransform P ((X + C (s ^ 2)) ^ N)).comp a).natDegree = N
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero N hs)), natDegree_comp,
    basisTransform_natDegree_eq hPdeg (fun n => (hPmonic n).ne_zero)
      hinputm.ne_zero, natDegree_pow, natDegree_X_add_C, hadeg]
  ring

/-- The top coefficient of row `N` is `d₀`. -/
theorem coeff_limitingAppellPolynomial_top (d : ℕ → ℝ) (N : ℕ) :
    (limitingAppellPolynomial d N).coeff N = d 0 := by
  rw [coeff_limitingAppellPolynomial, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [ite_eq_right]
    have hjlt : j < N / 2 + 1 := Finset.mem_range.mp hj
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    lia
  · simp

/-- If `d₀ = 1`, every limiting Appell polynomial is monic. -/
theorem limitingAppellPolynomial_monic {d : ℕ → ℝ} (hd₀ : d 0 = 1) (N : ℕ) :
    (limitingAppellPolynomial d N).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one N
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (by
      rw [natDegree_X_pow]
      exact Nat.sub_le N _)
  · rw [coeff_limitingAppellPolynomial_top, hd₀]

/-- If `d₀ = 1`, row `N` has degree exactly `N`. -/
theorem limitingAppellPolynomial_natDegree {d : ℕ → ℝ} (hd₀ : d 0 = 1) (N : ℕ) :
    (limitingAppellPolynomial d N).natDegree = N := by
  apply Nat.le_antisymm
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (by
      rw [natDegree_X_pow]
      exact Nat.sub_le N _)
  · apply le_natDegree_of_ne_zero
    rw [coeff_limitingAppellPolynomial_top, hd₀]
    norm_num

private theorem derivative_limitingAppellPolynomial_succ_even
    (d : ℕ → ℝ) (m : ℕ) :
    (limitingAppellPolynomial d (m + m + 1)).derivative =
      C (m + m + 1 : ℝ) * limitingAppellPolynomial d (m + m) := by
  rw [limitingAppellPolynomial, limitingAppellPolynomial]
  simp only [map_sum]
  rw [show (m + m + 1) / 2 + 1 = m + 1 by lia,
    show (m + m) / 2 + 1 = m + 1 by lia]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
  have hjle : 2 * j ≤ m + m := by
    have := Finset.mem_range.mp hj
    lia
  have hdf :
      (m + m + 1 - 2 * j) * (m + m + 1).descFactorial (2 * j) =
        (m + m + 1) * (m + m).descFactorial (2 * j) := by
    simpa only [show m + m + 1 = (m + m) + 1 by lia] using
      Nat.succ_descFactorial (m + m) (2 * j)
  have hdfR :
      (m + m + 1 - 2 * j : ℕ) *
          ((m + m + 1).descFactorial (2 * j) : ℝ) =
        (m + m + 1 : ℕ) * ((m + m).descFactorial (2 * j) : ℝ) := by
    exact_mod_cast hdf
  have hscalar :
      (-1 : ℝ) ^ j * ((m + m + 1).descFactorial (2 * j) : ℝ) * d j *
          (m + m + 1 - 2 * j : ℕ) =
        (m + m + 1 : ℕ) *
          ((-1 : ℝ) ^ j * ((m + m).descFactorial (2 * j) : ℝ) * d j) := by
    calc
      _ = ((-1 : ℝ) ^ j * d j) *
          ((m + m + 1 - 2 * j : ℕ) *
            ((m + m + 1).descFactorial (2 * j) : ℝ)) := by ring
      _ = ((-1 : ℝ) ^ j * d j) *
          ((m + m + 1 : ℕ) * ((m + m).descFactorial (2 * j) : ℝ)) := by
        rw [hdfR]
      _ = _ := by ring
  rw [show m + m + 1 - 2 * j - 1 = m + m - 2 * j by lia]
  simp only [← mul_assoc, ← C_mul]
  rw [hscalar]
  push_cast
  ring_nf

private theorem derivative_limitingAppellPolynomial_succ_odd
    (d : ℕ → ℝ) (m : ℕ) :
    (limitingAppellPolynomial d (2 * m + 1 + 1)).derivative =
      C (2 * m + 1 + 1 : ℝ) * limitingAppellPolynomial d (2 * m + 1) := by
  rw [limitingAppellPolynomial, limitingAppellPolynomial]
  simp only [map_sum]
  rw [show (2 * m + 1 + 1) / 2 + 1 = m + 2 by lia,
      show (2 * m + 1) / 2 + 1 = m + 1 by lia,
      Finset.sum_range_succ]
  have hlast :
      (C ((-1 : ℝ) ^ (m + 1) *
            ((2 * m + 1 + 1).descFactorial (2 * (m + 1)) : ℝ) * d (m + 1)) *
          X ^ (2 * m + 1 + 1 - 2 * (m + 1))).derivative = 0 := by
    rw [show 2 * m + 1 + 1 - 2 * (m + 1) = 0 by lia]
    simp
  rw [hlast, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
  have hjle : 2 * j ≤ 2 * m + 1 := by
    have := Finset.mem_range.mp hj
    lia
  have hdf :
      (2 * m + 1 + 1 - 2 * j) *
          (2 * m + 1 + 1).descFactorial (2 * j) =
        (2 * m + 1 + 1) * (2 * m + 1).descFactorial (2 * j) := by
    simpa only [show 2 * m + 1 + 1 = (2 * m + 1) + 1 by lia] using
      Nat.succ_descFactorial (2 * m + 1) (2 * j)
  have hdfR :
      (2 * m + 1 + 1 - 2 * j : ℕ) *
          ((2 * m + 1 + 1).descFactorial (2 * j) : ℝ) =
        (2 * m + 1 + 1 : ℕ) *
          ((2 * m + 1).descFactorial (2 * j) : ℝ) := by
    exact_mod_cast hdf
  have hscalar :
      (-1 : ℝ) ^ j *
            ((2 * m + 1 + 1).descFactorial (2 * j) : ℝ) * d j *
          (2 * m + 1 + 1 - 2 * j : ℕ) =
        (2 * m + 1 + 1 : ℕ) *
          ((-1 : ℝ) ^ j *
            ((2 * m + 1).descFactorial (2 * j) : ℝ) * d j) := by
    calc
      _ = ((-1 : ℝ) ^ j * d j) *
          ((2 * m + 1 + 1 - 2 * j : ℕ) *
            ((2 * m + 1 + 1).descFactorial (2 * j) : ℝ)) := by ring
      _ = ((-1 : ℝ) ^ j * d j) *
          ((2 * m + 1 + 1 : ℕ) *
            ((2 * m + 1).descFactorial (2 * j) : ℝ)) := by
        rw [hdfR]
      _ = _ := by ring
  rw [show 2 * m + 1 + 1 - 2 * j - 1 = 2 * m + 1 - 2 * j by lia]
  simp only [← mul_assoc, ← C_mul]
  rw [hscalar]
  push_cast
  ring_nf

private theorem derivative_limitingAppellPolynomial_succ (d : ℕ → ℝ) (N : ℕ) :
    (limitingAppellPolynomial d (N + 1)).derivative =
      C (N + 1 : ℝ) * limitingAppellPolynomial d N := by
  by_cases hN : Even N
  · obtain ⟨m, rfl⟩ := hN
    simpa only [Nat.cast_add, Nat.cast_one] using
      derivative_limitingAppellPolynomial_succ_even d m
  · have hNodd : Odd N := Nat.not_even_iff_odd.mp hN
    obtain ⟨m, hm⟩ := hNodd
    subst N
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
      derivative_limitingAppellPolynomial_succ_odd d m

/-- The limiting family is Appell: differentiating row `N` gives `N` times
the preceding row. -/
theorem derivative_limitingAppellPolynomial (d : ℕ → ℝ) (N : ℕ) :
    (limitingAppellPolynomial d N).derivative =
      C (N : ℝ) * limitingAppellPolynomial d (N - 1) := by
  cases N with
  | zero => simp [limitingAppellPolynomial]
  | succ N => simpa using derivative_limitingAppellPolynomial_succ d N

/-- The polynomial in the squared variable whose squaring expansion is the
even limiting Appell polynomial. -/
def limitingAppellSquarePolynomial (d : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1),
    C ((-1 : ℝ) ^ j * ((2 * n).descFactorial (2 * j) : ℝ) * d j) * X ^ (n - j)

/-- Coefficients of the polynomial in the squared variable. -/
theorem coeff_limitingAppellSquarePolynomial (d : ℕ → ℝ) (n k : ℕ) :
    (limitingAppellSquarePolynomial d n).coeff k =
      ∑ j ∈ range (n + 1),
        if n - j = k then
          (-1 : ℝ) ^ j * ((2 * n).descFactorial (2 * j) : ℝ) * d j
        else 0 := by
  rw [limitingAppellSquarePolynomial, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp_all

/-- The polynomial in the squared variable has degree at most `n`. -/
theorem limitingAppellSquarePolynomial_natDegree_le (d : ℕ → ℝ) (n : ℕ) :
    (limitingAppellSquarePolynomial d n).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans (by
    rw [natDegree_X_pow]
    exact Nat.sub_le n j)

/-- The top coefficient of the polynomial in the squared variable is `d₀`. -/
theorem coeff_limitingAppellSquarePolynomial_top (d : ℕ → ℝ) (n : ℕ) :
    (limitingAppellSquarePolynomial d n).coeff n = d 0 := by
  rw [coeff_limitingAppellSquarePolynomial, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [ite_eq_right]
    have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    lia
  · simp

/-- If `d₀ = 1`, the polynomial in the squared variable is monic. -/
theorem limitingAppellSquarePolynomial_monic
    {d : ℕ → ℝ} (hd₀ : d 0 = 1) (n : ℕ) :
    (limitingAppellSquarePolynomial d n).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one n
  · exact limitingAppellSquarePolynomial_natDegree_le d n
  · rw [coeff_limitingAppellSquarePolynomial_top, hd₀]

/-- If `d₀ = 1`, the polynomial in the squared variable has degree `n`. -/
theorem limitingAppellSquarePolynomial_natDegree
    {d : ℕ → ℝ} (hd₀ : d 0 = 1) (n : ℕ) :
    (limitingAppellSquarePolynomial d n).natDegree = n := by
  apply Nat.le_antisymm
  · exact limitingAppellSquarePolynomial_natDegree_le d n
  · apply le_natDegree_of_ne_zero
    rw [coeff_limitingAppellSquarePolynomial_top, hd₀]
    norm_num

/-- The next-to-top coefficient of the polynomial in the squared variable. -/
theorem coeff_limitingAppellSquarePolynomial_next
    (d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (limitingAppellSquarePolynomial d n).coeff (n - 1) =
      -((2 * n).descFactorial 2 : ℝ) * d 1 := by
  rw [coeff_limitingAppellSquarePolynomial, Finset.sum_eq_single 1]
  · norm_num
  · intro j hj hj1
    rw [ite_eq_right]
    have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
    lia
  · intro hnot
    exfalso
    exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- The third coefficient from the top of the polynomial in the squared variable. -/
theorem coeff_limitingAppellSquarePolynomial_next_two
    (d : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (limitingAppellSquarePolynomial d n).coeff (n - 2) =
      ((2 * n).descFactorial 4 : ℝ) * d 2 := by
  rw [coeff_limitingAppellSquarePolynomial, Finset.sum_eq_single 2]
  · norm_num
  · intro j hj hj2
    rw [ite_eq_right]
    have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
    lia
  · intro hnot
    exfalso
    exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- Squaring expansion recovers the even limiting Appell polynomial. -/
theorem expand_limitingAppellSquarePolynomial (d : ℕ → ℝ) (n : ℕ) :
    expand ℝ 2 (limitingAppellSquarePolynomial d n) =
      limitingAppellPolynomial d (2 * n) := by
  rw [limitingAppellSquarePolynomial, limitingAppellPolynomial]
  simp only [show 2 * n / 2 + 1 = n + 1 by lia, map_sum, expand_eq_comp_X_pow,
    mul_comp, C_comp, pow_comp, X_comp]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by
    have := Finset.mem_range.mp hj
    lia
  rw [← pow_mul]
  congr 2
  lia

/-- If an even limiting Appell polynomial splits, its polynomial in the
squared variable splits and has only nonnegative roots. -/
theorem limitingAppellSquarePolynomial_splits_and_roots_nonneg
    {d : ℕ → ℝ} {n : ℕ} (h : (limitingAppellPolynomial d (2 * n)).Splits) :
    (limitingAppellSquarePolynomial d n).Splits ∧
      ∀ r ∈ (limitingAppellSquarePolynomial d n).roots, 0 ≤ r := by
  apply Polynomial.splits_and_forall_roots_nonneg_of_splits_expand_two
  rwa [expand_limitingAppellSquarePolynomial]

private theorem coeff_limitingAppellSquarePolynomial_sub
    (d : ℕ → ℝ) {n j : ℕ} (hj : j ≤ n) :
    (limitingAppellSquarePolynomial d n).coeff (n - j) =
      (-1 : ℝ) ^ j * ((2 * n).descFactorial (2 * j) : ℝ) * d j := by
  rw [coeff_limitingAppellSquarePolynomial, Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    rw [ite_eq_right]
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    lia
  · intro hnot
    exfalso
    exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

private theorem esymm_roots_limitingAppellSquarePolynomial
    {d : ℕ → ℝ} (hd₀ : d 0 = 1) {n j : ℕ} (hj : j ≤ n)
    (hsplits : (limitingAppellPolynomial d (2 * n)).Splits) :
    (limitingAppellSquarePolynomial d n).roots.esymm j =
      ((2 * n).descFactorial (2 * j) : ℝ) * d j := by
  let p := limitingAppellSquarePolynomial d n
  have hpmonic : p.Monic := limitingAppellSquarePolynomial_monic hd₀ n
  have hpdeg : p.natDegree = n := limitingAppellSquarePolynomial_natDegree hd₀ n
  have hpsplits : p.Splits :=
    (limitingAppellSquarePolynomial_splits_and_roots_nonneg hsplits).1
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hpsplits
  have hv := leadingCoeff_mul_esymm_roots_eq_coeff_of_card hcard (hpdeg.symm ▸ hj)
  rw [hpmonic.leadingCoeff, one_mul, hpdeg,
    coeff_limitingAppellSquarePolynomial_sub d hj] at hv
  calc
    p.roots.esymm j = (-1 : ℝ) ^ j *
        ((-1 : ℝ) ^ j * ((2 * n).descFactorial (2 * j) : ℝ) * d j) := hv
    _ = ((2 * n).descFactorial (2 * j) : ℝ) * d j := by
      calc
        _ = ((-1 : ℝ) ^ j * (-1) ^ j) *
            ((2 * n).descFactorial (2 * j) : ℝ) * d j := by ring
        _ = _ := by rw [← pow_add]; norm_num

private theorem esymm_div_choose_le_first_pow
    (t : Multiset ℝ) {n j : ℕ} (hn : t.card = n)
    (ht : ∀ x ∈ t, 0 ≤ x) (hj : 0 < j) (hjn : j ≤ n) :
    t.esymm j / (n.choose j : ℝ) ≤
      (t.esymm 1 / (n.choose 1 : ℝ)) ^ j := by
  have hnonneg (k : ℕ) : 0 ≤ t.esymm k / (n.choose k : ℝ) :=
    div_nonneg (Multiset.esymm_nonneg_of_forall_nonneg ht k) (Nat.cast_nonneg _)
  have hroot :
      (t.esymm j / (n.choose j : ℝ)) ^ ((j : ℝ)⁻¹) ≤
        t.esymm 1 / (n.choose 1 : ℝ) := by
    have haux : ∀ k, 0 < k → k ≤ n →
        (t.esymm k / (n.choose k : ℝ)) ^ ((k : ℝ)⁻¹) ≤
          t.esymm 1 / (n.choose 1 : ℝ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          intro hk hkn
          by_cases hkzero : k = 0
          · subst k
            simp
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
            have hstep := Maclaurin.esymm_div_choose_rpow_le t hn ht hkpos (by lia)
            have hind := ih hkpos (by lia)
            have hstep' :
                (t.esymm (k + 1) / (n.choose (k + 1) : ℝ)) ^ (((k + 1 : ℕ) : ℝ)⁻¹) ≤
                  (t.esymm k / (n.choose k : ℝ)) ^ ((k : ℝ)⁻¹) := by
              simpa [one_div, Nat.cast_add, Nat.cast_one] using hstep
            exact hstep'.trans hind
    exact haux j hj hjn
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (hnonneg j) _) hroot j
  rw [Real.rpow_inv_natCast_pow (hnonneg j) (Nat.ne_of_gt hj)] at hpow
  simpa using hpow

private theorem factorial_mul_esymm_le_sum_pow
    (t : Multiset ℝ) (ht : ∀ x ∈ t, 0 ≤ x) (j : ℕ) :
    (j.factorial : ℝ) * t.esymm j ≤ t.sum ^ j := by
  by_cases hj : j = 0
  · subst j
    simp [Multiset.esymm]
  by_cases hjcard : j ≤ t.card
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hmac := esymm_div_choose_le_first_pow t rfl ht hjpos hjcard
    have hesymm_one : t.esymm 1 = t.sum := by
      simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
    rw [Nat.choose_one_right, hesymm_one] at hmac
    have hcardpos : (0 : ℝ) < t.card := by exact_mod_cast hjpos.trans_le hjcard
    have hchoosepos : (0 : ℝ) < t.card.choose j := by
      exact_mod_cast Nat.choose_pos hjcard
    have hsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have hchoose := Nat.choose_le_pow_div (α := ℝ) j t.card
    rw [div_pow] at hmac
    have hmac' : t.esymm j * (t.card : ℝ) ^ j ≤
        t.sum ^ j * (t.card.choose j : ℝ) :=
      (div_le_div_iff₀ hchoosepos (pow_pos hcardpos j)).mp hmac
    have hfactorial : (0 : ℝ) < j.factorial := by positivity
    have hchoose' : (t.card.choose j : ℝ) * j.factorial ≤
        (t.card : ℝ) ^ j := (le_div_iff₀ hfactorial).mp hchoose
    apply le_of_mul_le_mul_right _ (pow_pos hcardpos j)
    calc
      (j.factorial : ℝ) * t.esymm j * (t.card : ℝ) ^ j ≤
          j.factorial * (t.sum ^ j * (t.card.choose j : ℝ)) :=
        by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmac' hfactorial.le
      _ = t.sum ^ j * ((t.card.choose j : ℝ) * j.factorial) := by ring
      _ ≤ t.sum ^ j * (t.card : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hchoose' (pow_nonneg hsum j)
  · have hesymm : t.esymm j = 0 :=
      Multiset.esymm_of_card_lt (lt_of_not_ge hjcard)
    rw [hesymm, mul_zero]
    exact pow_nonneg (Multiset.sum_nonneg ht) j

private theorem limitingAppellCoefficient_finite_factorial_bound
    {d : ℕ → ℝ} (hd₀ : d 0 = 1) {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n)
    (hsplits : (limitingAppellPolynomial d (2 * n)).Splits) :
    (j.factorial : ℝ) * ((2 * n).descFactorial (2 * j) : ℝ) * d j ≤
      (((2 * n).descFactorial 2 : ℝ) * d 1) ^ j := by
  let p := limitingAppellSquarePolynomial d n
  have hroot := limitingAppellSquarePolynomial_splits_and_roots_nonneg hsplits
  have hmac := factorial_mul_esymm_le_sum_pow p.roots hroot.2 j
  have hjcoeff := esymm_roots_limitingAppellSquarePolynomial hd₀ hj hsplits
  have honecoeff := esymm_roots_limitingAppellSquarePolynomial hd₀ hn hsplits
  have hesymm_one : p.roots.esymm 1 = p.roots.sum := by
    simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  rw [hjcoeff, ← hesymm_one, honecoeff] at hmac
  simpa [mul_assoc] using hmac

private theorem tendsto_descFactorial_two_ratio (j : ℕ) :
    Tendsto (fun n : ℕ =>
      (((2 * n).descFactorial 2 : ℝ) ^ j /
        ((2 * n).descFactorial (2 * j) : ℝ))) atTop (nhds 1) := by
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    lia
  have hnum := (Nat.tendsto_descFactorial_div_pow_atTop 2).comp htwo
  have hden := (Nat.tendsto_descFactorial_div_pow_atTop (2 * j)).comp htwo
  have hquotient := (hnum.pow j).div hden (by norm_num)
  have hlim : Tendsto (fun n : ℕ =>
      ((((2 * n).descFactorial 2 : ℝ) / ((2 * n : ℕ) : ℝ) ^ 2) ^ j /
        (((2 * n).descFactorial (2 * j) : ℝ) /
          ((2 * n : ℕ) : ℝ) ^ (2 * j)))) atTop (nhds 1) := by
    change Tendsto (fun n : ℕ =>
      ((((2 * n).descFactorial 2 : ℝ) / ((2 * n : ℕ) : ℝ) ^ 2) ^ j /
        (((2 * n).descFactorial (2 * j) : ℝ) /
          ((2 * n : ℕ) : ℝ) ^ (2 * j)))) atTop (nhds (1 ^ j / 1)) at hquotient
    norm_num at hquotient ⊢
    exact hquotient
  exact hlim.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : ((2 * n : ℕ) : ℝ) ≠ 0 := by positivity
    have hpow : (((2 * n : ℕ) : ℝ) ^ 2) ^ j =
        ((2 * n : ℕ) : ℝ) ^ (2 * j) := by rw [pow_mul]
    rw [div_pow, hpow]
    field_simp)

/-- If every limiting Appell polynomial splits, all its defining coefficients
are nonnegative. -/
theorem limitingAppellCoefficient_nonneg
    {d : ℕ → ℝ} (hd₀ : d 0 = 1)
    (hsplits : ∀ N, (limitingAppellPolynomial d N).Splits) (j : ℕ) :
    0 ≤ d j := by
  have heq := esymm_roots_limitingAppellSquarePolynomial hd₀ (le_refl j)
    (hsplits (2 * j))
  have hroots := limitingAppellSquarePolynomial_splits_and_roots_nonneg
    (hsplits (2 * j))
  have hnonneg := Multiset.esymm_nonneg_of_forall_nonneg hroots.2 j
  rw [heq] at hnonneg
  have hdesc : (0 : ℝ) < (2 * j).descFactorial (2 * j) := by
    exact_mod_cast Nat.descFactorial_pos.mpr le_rfl
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnonneg) hdesc

/-- If every limiting Appell polynomial splits, then
`d_j ≤ d_1 ^ j / j!` for every `j`. -/
theorem limitingAppellCoefficient_le_pow_div_factorial
    {d : ℕ → ℝ} (hd₀ : d 0 = 1)
    (hsplits : ∀ N, (limitingAppellPolynomial d N).Splits) (j : ℕ) :
    d j ≤ d 1 ^ j / (j.factorial : ℝ) := by
  let upper : ℕ → ℝ := fun n =>
    (((2 * n).descFactorial 2 : ℝ) ^ j /
      ((2 * n).descFactorial (2 * j) : ℝ)) *
        (d 1 ^ j / (j.factorial : ℝ))
  have hupper : Tendsto upper atTop (nhds (d 1 ^ j / (j.factorial : ℝ))) := by
    simpa [upper] using
      (tendsto_descFactorial_two_ratio j).mul_const
        (d 1 ^ j / (j.factorial : ℝ))
  apply ge_of_tendsto hupper
  filter_upwards [eventually_ge_atTop (max 1 j)] with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 j) hn
  have hjn : j ≤ n := le_trans (le_max_right 1 j) hn
  have hfinite := limitingAppellCoefficient_finite_factorial_bound hd₀ hn1 hjn
    (hsplits (2 * n))
  have hfactorial : (0 : ℝ) < j.factorial := by positivity
  have hdesc : (0 : ℝ) < (2 * n).descFactorial (2 * j) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by lia)
  have hbound : d j ≤
      ((((2 * n).descFactorial 2 : ℝ) * d 1) ^ j) /
        ((j.factorial : ℝ) * (2 * n).descFactorial (2 * j)) := by
    rw [le_div_iff₀ (mul_pos hfactorial hdesc)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hfinite
  refine hbound.trans_eq ?_
  dsimp only [upper]
  rw [mul_pow]
  field_simp

/-- The complete coefficient bounds forced by splitness of the limiting
Appell family. -/
theorem limitingAppellCoefficient_bounds
    {d : ℕ → ℝ} (hd₀ : d 0 = 1)
    (hsplits : ∀ N, (limitingAppellPolynomial d N).Splits) (j : ℕ) :
    0 ≤ d j ∧ d j ≤ d 1 ^ j / (j.factorial : ℝ) :=
  ⟨limitingAppellCoefficient_nonneg hd₀ hsplits j,
    limitingAppellCoefficient_le_pow_div_factorial hd₀ hsplits j⟩

/-- Newton's first normalized inequality for the squared-variable polynomial. -/
theorem limitingAppellSquarePolynomial_newton_two
    {d : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : (limitingAppellPolynomial d (2 * n)).Splits) :
    (d 0 / (n.choose 0 : ℝ)) *
        (((2 * n).descFactorial 4 : ℝ) * d 2 / (n.choose 2 : ℝ)) ≤
      (-((2 * n).descFactorial 2 : ℝ) * d 1 / (n.choose 1 : ℝ)) ^ 2 := by
  let p := limitingAppellSquarePolynomial d n
  have hpdeg : p.natDegree ≤ n := limitingAppellSquarePolynomial_natDegree_le d n
  have hpsplit : p.Splits :=
    (limitingAppellSquarePolynomial_splits_and_roots_nonneg h).1
  have hrefsplit : (reflect n p).Splits := Polynomial.Splits.reflect hpsplit hpdeg
  have hrefdeg : (reflect n p).natDegree ≤ n :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hpdeg)
  have hnewton := normalized_coeff_left_logConcave_of_splits_natDegree_le
    hrefdeg hrefsplit
  rw [coeff_reflect, coeff_reflect, coeff_reflect, revAt_zero,
    revAt_le (by lia : 1 ≤ n), revAt_le hn] at hnewton
  dsimp only [p] at hnewton
  rw [coeff_limitingAppellSquarePolynomial_top,
    coeff_limitingAppellSquarePolynomial_next d (by lia),
    coeff_limitingAppellSquarePolynomial_next_two d hn] at hnewton
  exact hnewton

/-- The first Newton inequality after cancelling its positive combinatorial
factors. -/
theorem limitingAppellCoefficient_two_finite_bound
    {d : ℕ → ℝ} {n : ℕ} (hd₀ : d 0 = 1) (hn : 2 ≤ n)
    (h : (limitingAppellPolynomial d (2 * n)).Splits) :
    2 * (2 * (n : ℝ) - 3) * d 2 ≤ (2 * (n : ℝ) - 1) * d 1 ^ 2 := by
  have hnewton := limitingAppellSquarePolynomial_newton_two hn h
  norm_num [hd₀, Nat.cast_choose_two, Nat.descFactorial] at hnewton
  have hcast1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia)]
    push_cast
    rfl
  have hcast2 : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by lia)]
    push_cast
    rfl
  have hcast3 : ((2 * n - 3 : ℕ) : ℝ) = 2 * (n : ℝ) - 3 := by
    rw [Nat.cast_sub (by lia)]
    push_cast
    rfl
  rw [hcast1, hcast2, hcast3] at hnewton
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  field_simp [ne_of_gt hn0, ne_of_gt hn1] at hnewton
  have hleft : 0 < 2 * (n : ℝ) - 1 := by linarith
  apply le_of_mul_le_mul_left ?_ hleft
  convert hnewton using 1 <;> ring

/-- If every limiting Appell polynomial splits, then `d₂ ≤ d₁² / 2`. -/
theorem limitingAppellCoefficient_two_le_half_square
    {d : ℕ → ℝ} (hd₀ : d 0 = 1)
    (hsplits : ∀ N, (limitingAppellPolynomial d N).Splits) :
    d 2 ≤ d 1 ^ 2 / 2 := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < 2 * d 2 - d 1 ^ 2 := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt
    ((6 * d 2 - d 1 ^ 2) / (2 * d 2 - d 1 ^ 2))
  have hm' : 6 * d 2 - d 1 ^ 2 < (2 * d 2 - d 1 ^ 2) * m := by
    rw [div_lt_iff₀ hpos] at hm
    linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hfinite := limitingAppellCoefficient_two_finite_bound hd₀
    (show 2 ≤ m + 2 by lia) (hsplits (2 * (m + 2)))
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by
    push_cast
    rfl
  rw [hcast] at hfinite
  nlinarith [mul_nonneg hpos.le hm0]

/-- Splitness of the second limiting row forces `d₁ ≥ 0`. -/
theorem limitingAppellCoefficient_one_nonneg
    {d : ℕ → ℝ} (hd₀ : d 0 = 1) (h : (limitingAppellPolynomial d 2).Splits) :
    0 ≤ d 1 := by
  have hs := limitingAppellSquarePolynomial_splits_and_roots_nonneg
    (d := d) (n := 1) h
  have heq : limitingAppellSquarePolynomial d 1 = X - C (2 * d 1) := by
    rw [limitingAppellSquarePolynomial]
    norm_num [hd₀, Finset.sum_range_succ]
    rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm]
    rfl
  have hne : limitingAppellSquarePolynomial d 1 ≠ 0 := by
    rw [heq]
    exact (monic_X_sub_C (2 * d 1)).ne_zero
  have hroot : 2 * d 1 ∈ (limitingAppellSquarePolynomial d 1).roots := by
    apply (mem_roots hne).mpr
    rw [heq]
    simp
  have := hs.2 (2 * d 1) hroot
  linarith

/-- Coefficientwise limits of monic split degree-`N` polynomials give a split
limiting Appell polynomial. -/
theorem limitingAppellPolynomial_splits_of_coeff_tendsto
    {d : ℕ → ℝ} (hd₀ : d 0 = 1) {N : ℕ} {p : ℕ → ℝ[X]}
    (hpMonic : ∀ m, (p m).Monic)
    (hpDegree : ∀ m, (p m).natDegree = N)
    (hpSplits : ∀ m, (p m).Splits)
    (hcoeff : ∀ i, Tendsto (fun m ↦ (p m).coeff i) atTop
      (nhds ((limitingAppellPolynomial d N).coeff i))) :
    (limitingAppellPolynomial d N).Splits := by
  apply splits_of_monic_of_coeff_tendsto
    (limitingAppellPolynomial_monic hd₀ N) hpMonic
  · intro m
    rw [hpDegree, limitingAppellPolynomial_natDegree hd₀]
  · exact hpSplits
  · exact hcoeff

/-- A root-preserving degree-triangular monic basis has split limiting Appell
polynomials for its canonical even differential coefficients. -/
theorem limitingAppellPolynomial_splits_of_basisTransform
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) (N : ℕ) :
    (limitingAppellPolynomial
      (fun j => (appellCoefficient P (2 * j)).coeff j) N).Splits := by
  apply limitingAppellPolynomial_splits_of_coeff_tendsto
    (d := fun j => (appellCoefficient P (2 * j)).coeff j) (N := N)
    (coeff_zero_appellCoefficient_zero_eq_one hPdeg hPmonic hpres)
    (p := rescaledBasisPower P N)
  · exact rescaledBasisPower_monic hPdeg hPmonic N
  · exact rescaledBasisPower_natDegree hPdeg hPmonic N
  · exact rescaledBasisPower_splits hPdeg hPmonic hpres N
  · exact tendsto_coeff_rescaledBasisPower hPdeg hPmonic hpres N

/-- All even top differential coefficients of a root-preserving monic basis
obey the sharp factorial bounds. -/
theorem coeff_appellCoefficient_even_bounds
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) (j : ℕ) :
    0 ≤ (appellCoefficient P (2 * j)).coeff j ∧
      (appellCoefficient P (2 * j)).coeff j ≤
        (appellCoefficient P 2).coeff 1 ^ j / (j.factorial : ℝ) := by
  apply limitingAppellCoefficient_bounds
    (d := fun k => (appellCoefficient P (2 * k)).coeff k)
    (coeff_zero_appellCoefficient_zero_eq_one hPdeg hPmonic hpres)
  exact limitingAppellPolynomial_splits_of_basisTransform hPdeg hPmonic hpres

/-- Exponential coefficient data attain equality in the second coefficient
bound. -/
theorem limitingAppellCoefficient_two_eq_half_square_of_eq_pow_div_factorial
    {d : ℕ → ℝ} {c : ℝ} (hd : ∀ j, d j = c ^ j / (j.factorial : ℝ)) :
    d 2 = d 1 ^ 2 / 2 := by
  rw [hd 2, hd 1]
  norm_num

private theorem coeff_zero_limitingAppellPolynomial_even
    (d : ℕ → ℝ) (j : ℕ) :
    (limitingAppellPolynomial d (2 * j)).coeff 0 =
      (-1 : ℝ) ^ j * ((2 * j).descFactorial (2 * j) : ℝ) * d j := by
  rw [coeff_limitingAppellPolynomial, Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    rw [ite_eq_right]
    have hk' : k ≤ j := by
      simpa only [show (2 * j) / 2 + 1 = j + 1 by lia, Finset.mem_range,
        Nat.lt_succ_iff] using hk
    lia
  · intro hnot
    exfalso
    apply hnot
    simp only [show (2 * j) / 2 + 1 = j + 1 by lia, Finset.mem_range,
      Nat.lt_succ_iff]
    exact le_rfl

/-- Equality of every limiting polynomial with the Gaussian family is
equivalent to exponential coefficient data. -/
theorem forall_limitingAppellPolynomial_eq_iff_coeff_eq_pow_div_factorial
    (d : ℕ → ℝ) (c : ℝ) :
    (∀ N, limitingAppellPolynomial d N =
      limitingAppellPolynomial (fun j => c ^ j / (j.factorial : ℝ)) N) ↔
      ∀ j, d j = c ^ j / (j.factorial : ℝ) := by
  constructor
  · intro h j
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) (h (2 * j))
    rw [coeff_zero_limitingAppellPolynomial_even,
      coeff_zero_limitingAppellPolynomial_even] at hcoeff
    have hscalar :
        (-1 : ℝ) ^ j * ((2 * j).descFactorial (2 * j) : ℝ) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero _ (by norm_num)
      · exact_mod_cast (Nat.descFactorial_pos.mpr le_rfl).ne'
    apply mul_left_cancel₀ hscalar
    simpa [mul_assoc] using hcoeff
  · intro hd N
    congr 1
    funext j
    exact hd j

end RealRooted
