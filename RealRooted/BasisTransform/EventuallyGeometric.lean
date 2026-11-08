module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Real.Basic
import RealRooted.Derivative.Interlacing
import RealRooted.Mathlib.Algebra.Polynomial.Eval.NatWindow
import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.Interlacing.Multiplicity
import RealRooted.Derivative.RootCounting
import RealRooted.ProductSequence.Factors
import RealRooted.ObreschkoffConverse.DegreeGap

/-!
# Eventually geometric polynomial bases

An eventually geometric sequence of images of monomials is rigid if its
associated linear map preserves real-rootedness.  A nonzero discrepancy in the
finite prefix produces a non-real-rooted shifted power in an explicit window.
-/

public section

open scoped BigOperators
open Polynomial

namespace RealRooted

/-- A multiple root of the derivative of a split real polynomial comes from a
root of the original polynomial with multiplicity one larger. -/
theorem rootMultiplicity_eq_add_one_of_derivative_ge_two
    {p : ℝ[X]} {a : ℝ} (hp : p.Splits)
    (hm : 2 ≤ p.derivative.rootMultiplicity a) :
    p.rootMultiplicity a = p.derivative.rootMultiplicity a + 1 := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp at hm
  have hpd0 : p.derivative ≠ 0 := by
    intro hzero
    rw [hzero] at hm
    simp at hm
  have hpdeg : p.natDegree ≠ 0 := by
    intro hdeg
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hpd0
    simp at hpd0
  have hinterl : RealRooted.StrictInterl p.derivative p :=
    (RealRooted.derivative_interlaces_of_natDegree_ne_zero hp hpdeg).toStrictInterl
  have hroot : p.IsRoot a := by
    apply (rootMultiplicity_pos hp0).mp
    have hb := hinterl.rootMultiplicity_bounds a
    lia
  rw [derivative_rootMultiplicity_of_root hroot]
  have hpos := (rootMultiplicity_pos hp0).mpr hroot
  lia

/-- A multiple root after iterated differentiation comes from a root whose
multiplicity is larger by the number of differentiations. -/
theorem rootMultiplicity_eq_add_of_iterate_derivative_ge_two
    {p : ℝ[X]} {a : ℝ} (hp : p.Splits) (n : ℕ)
    (hm : 2 ≤ ((derivative^[n]) p).rootMultiplicity a) :
    p.rootMultiplicity a = ((derivative^[n]) p).rootMultiplicity a + n := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at hm ⊢
      have hpn : ((derivative^[n]) p).Splits := hp.iterate_derivative n
      have hstep := rootMultiplicity_eq_add_one_of_derivative_ge_two hpn hm
      have hmn : 2 ≤ ((derivative^[n]) p).rootMultiplicity a := by
        rw [hstep]
        lia
      rw [ih hp hmn, hstep]
      lia

noncomputable section

/-- The binomial image of a shifted power under the row family `P`. -/
def binomialShiftImage (P : ℕ → ℝ[X]) (r : ℝ) (N : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (N + 1), C ((N.choose j : ℝ) * r ^ (N - j)) * P j

/-- The discrepancy between a prefix row and the geometric tail through row
`k`. -/
def geometricDiscrepancy (P : ℕ → ℝ[X]) (y : ℝ[X]) (k j : ℕ) : ℝ[X] :=
  y ^ k * P j - P k * y ^ j

/-- The maximum degree of the first `k` geometric discrepancies. -/
def geometricDiscrepancyDegree (P : ℕ → ℝ[X]) (y : ℝ[X]) (k : ℕ) : ℕ :=
  (Finset.range k).sup fun j ↦ (geometricDiscrepancy P y k j).natDegree

/-- Multiplying a shifted-power image by `y ^ k` separates its geometric
tail from the finitely many prefix discrepancies. -/
theorem pow_mul_binomialShiftImage_eq_add_discrepancies
    {P : ℕ → ℝ[X]} {y : ℝ[X]} {k N : ℕ} {r : ℝ}
    (hkN : k ≤ N)
    (htail : ∀ n, k ≤ n → P n = P k * y ^ (n - k)) :
    y ^ k * binomialShiftImage P r N =
      P k * (y + C r) ^ N +
        ∑ j ∈ Finset.range k,
          C ((N.choose j : ℝ) * r ^ (N - j)) *
            geometricDiscrepancy P y k j := by
  have hrange : Finset.range k ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.mpr (by lia)
  have hresidual :
      (∑ j ∈ Finset.range k,
          C ((N.choose j : ℝ) * r ^ (N - j)) *
            geometricDiscrepancy P y k j) =
        ∑ j ∈ Finset.range (N + 1),
          C ((N.choose j : ℝ) * r ^ (N - j)) *
            geometricDiscrepancy P y k j := by
    apply Finset.sum_subset hrange
    intro j hj hjk
    have hkj : k ≤ j := by simpa using hjk
    rw [geometricDiscrepancy, htail j hkj]
    have hp : y ^ k * y ^ (j - k) = y ^ j := by
      rw [← pow_add, Nat.add_sub_of_le hkj]
    have : y ^ k * (P k * y ^ (j - k)) = P k * y ^ j := by
      calc
        y ^ k * (P k * y ^ (j - k)) = P k * (y ^ k * y ^ (j - k)) := by ring
        _ = P k * y ^ j := by rw [hp]
    rw [this, sub_self, mul_zero]
  rw [hresidual, binomialShiftImage, add_pow, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [geometricDiscrepancy, map_mul, map_pow]
  rw [show (N.choose j : ℝ[X]) = C (N.choose j : ℝ) by simp]
  ring

/-- If `k` consecutive polynomial-valued binomial combinations with a
nonzero geometric weight vanish, then all `k` coefficients vanish. -/
theorem eq_zero_of_sum_choose_mul_pow_eq_zero_on_window
    (E : ℕ → ℝ[X]) {r : ℝ} {k N₀ : ℕ}
    (hr : r ≠ 0) (hkN₀ : k ≤ N₀)
    (h : ∀ t < k,
      ∑ j ∈ Finset.range k,
        C (((N₀ + t).choose j : ℝ) * r ^ (N₀ + t - j)) * E j = 0) :
    ∀ j < k, E j = 0 := by
  have hscalar : ∀ m : ℕ, ∀ t < k,
      ∑ j ∈ Finset.range k,
        ((N₀ + t).choose j : ℝ) * ((r⁻¹) ^ j * (E j).coeff m) = 0 := by
    intro m t ht
    have hcoeff := congrArg (Polynomial.lcoeff ℝ m) (h t ht)
    have hcoeff' : ∑ j ∈ Finset.range k,
        ((N₀ + t).choose j : ℝ) * r ^ (N₀ + t - j) * (E j).coeff m = 0 := by
      simpa only [map_sum, map_zero, Polynomial.lcoeff_apply, coeff_C_mul] using hcoeff
    have hrpow : r ^ (N₀ + t) ≠ 0 := pow_ne_zero _ hr
    apply (mul_left_cancel₀ hrpow)
    rw [mul_zero, Finset.mul_sum]
    rw [← hcoeff']
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N₀ + t := by
      have hjk : j < k := Finset.mem_range.mp hj
      lia
    have hpow : r ^ (N₀ + t) * (r⁻¹) ^ j = r ^ (N₀ + t - j) := by
      calc
        r ^ (N₀ + t) * (r⁻¹) ^ j =
            r ^ (N₀ + t - j) * r ^ j * (r⁻¹) ^ j := by
              rw [← pow_add, Nat.sub_add_cancel hjN]
        _ = r ^ (N₀ + t - j) := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]
    calc
      r ^ (N₀ + t) *
          ((N₀ + t).choose j * ((r⁻¹) ^ j * (E j).coeff m)) =
          ((N₀ + t).choose j : ℝ) *
            (r ^ (N₀ + t) * (r⁻¹) ^ j) * (E j).coeff m := by ring
      _ = ((N₀ + t).choose j : ℝ) * r ^ (N₀ + t - j) *
          (E j).coeff m := by rw [hpow]
  intro j hj
  apply Polynomial.ext
  intro m
  have hv := Polynomial.eq_zero_of_sum_choose_eq_zero_on_window
    (fun i ↦ (r⁻¹) ^ i * (E i).coeff m) (hscalar m) j hj
  have hinv : (r⁻¹) ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero hr)
  simpa using (mul_eq_zero.mp hv).resolve_left hinv

/-- A bounded-degree perturbation of a high power of a nonconstant linear
factor cannot split unless the perturbation vanishes. -/
theorem eq_zero_of_add_scaled_linear_pow_splits
    {q c : ℝ[X]} {d z : ℝ} {N D : ℕ}
    (hq : q ≠ 0) (hd : d ≠ 0) (hcdeg : c.natDegree ≤ D)
    (hN : D + 3 ≤ N)
    (hsplit : (q * (C d * (X - C z)) ^ N + c).Splits) : c = 0 := by
  let F := q * (C d * (X - C z)) ^ N + c
  let m := D + 1
  have hmN : m ≤ N := by dsimp [m]; lia
  have hcder : (derivative^[m]) c = 0 := by
    apply iterate_derivative_eq_zero
    dsimp [m]
    lia
  have hlin : X - C z ≠ 0 := by
    intro hzero
    have := congrArg (fun p : ℝ[X] ↦ p.coeff 1) hzero
    simp at this
  have hmain0 : q * (C d * (X - C z)) ^ N ≠ 0 :=
    mul_ne_zero hq (pow_ne_zero N (mul_ne_zero (C_ne_zero.mpr hd) hlin))
  have hmaindeg : (q * (C d * (X - C z)) ^ N).natDegree = q.natDegree + N := by
    rw [natDegree_mul hq
      (pow_ne_zero N (mul_ne_zero (C_ne_zero.mpr hd) hlin))]
    rw [natDegree_pow, natDegree_mul (C_ne_zero.mpr hd) hlin]
    simp
  have hmain_der0 :
      (derivative^[m]) (q * (C d * (X - C z)) ^ N) ≠ 0 := by
    apply iterate_derivative_ne_zero_of_le_natDegree hmain0
    rw [hmaindeg]
    exact hmN.trans (Nat.le_add_left N q.natDegree)
  have hFder :
      (derivative^[m]) F = (derivative^[m]) (q * (C d * (X - C z)) ^ N) := by
    dsimp [F]
    have hadd : ∀ n : ℕ, ∀ p r : ℝ[X],
        (derivative^[n]) (p + r) = (derivative^[n]) p + (derivative^[n]) r := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          intro p r
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            Function.iterate_succ_apply', ih, map_add]
    rw [hadd, hcder, add_zero]
  have hFder0 : (derivative^[m]) F ≠ 0 := hFder.symm ▸ hmain_der0
  have hfactor :
      (X - C z) ^ N ∣ q * (C d * (X - C z)) ^ N := by
    refine ⟨q * C d ^ N, ?_⟩
    rw [mul_pow]
    ring
  have hfactor_der : (X - C z) ^ (N - m) ∣ (derivative^[m]) F := by
    rw [hFder]
    exact pow_sub_dvd_iterate_derivative_of_pow_dvd m hfactor
  have hmult_der : N - m ≤ ((derivative^[m]) F).rootMultiplicity z :=
    (le_rootMultiplicity_iff hFder0).mpr hfactor_der
  have htwo : 2 ≤ ((derivative^[m]) F).rootMultiplicity z := by
    have : 2 ≤ N - m := by dsimp [m]; lia
    exact this.trans hmult_der
  have hmult :=
    rootMultiplicity_eq_add_of_iterate_derivative_ge_two hsplit m htwo
  have hNF : N ≤ F.rootMultiplicity z := by
    rw [hmult]
    lia
  have hF0 : F ≠ 0 := by
    intro hzero
    rw [hzero] at hFder0
    simp at hFder0
  have hfactorF : (X - C z) ^ N ∣ F :=
    (le_rootMultiplicity_iff hF0).mp hNF
  have hfactorc : (X - C z) ^ N ∣ c := by
    dsimp [F] at hfactorF
    convert dvd_add (dvd_neg.mpr hfactor) hfactorF using 1
    ring
  by_contra hc0
  have hdegfactor : ((X - C z) ^ N).natDegree ≤ c.natDegree :=
    natDegree_le_of_dvd hfactorc hc0
  simp at hdegfactor
  lia

/-- Vanishing prefix discrepancies force an eventually geometric row family
to be geometric from its zeroth row onward. -/
theorem eq_mul_pow_of_eventually_geometric_of_discrepancy_eq_zero
    {P : ℕ → ℝ[X]} {y : ℝ[X]} {k : ℕ}
    (hk : k ≠ 0) (hy : y ≠ 0)
    (htail : ∀ n, k ≤ n → P n = P k * y ^ (n - k))
    (hdiscrepancy : ∀ j < k, geometricDiscrepancy P y k j = 0) :
    ∀ n, P n = P 0 * y ^ n := by
  have hkrow : P k = P 0 * y ^ k := by
    have h := hdiscrepancy 0 (Nat.pos_of_ne_zero hk)
    rw [geometricDiscrepancy, pow_zero, mul_one, sub_eq_zero] at h
    simpa [mul_comm] using h.symm
  intro n
  by_cases hn : k ≤ n
  · rw [htail n hn, hkrow]
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hn]
  · have hnk : n < k := by lia
    have h := hdiscrepancy n hnk
    rw [geometricDiscrepancy, hkrow, sub_eq_zero] at h
    apply mul_left_cancel₀ (pow_ne_zero k hy)
    calc
      y ^ k * P n = (P 0 * y ^ k) * y ^ n := h
      _ = y ^ k * (P 0 * y ^ n) := by ring

/-- A linear map whose monomial rows are geometric is multiplication by the
zeroth row followed by polynomial composition. -/
theorem linearMap_eq_mul_comp_of_eq_mul_pow
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (P : ℕ → ℝ[X]) (y : ℝ[X])
    (hT : ∀ n, T (X ^ n) = P n)
    (hP : ∀ n, P n = P 0 * y ^ n) :
    ∀ p, T p = P 0 * p.comp y := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq, add_comp, mul_add]
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, hT, hP]
      simp [pow_comp]

/-- Rigidity of an eventually geometric monomial row family, including the
induced formula for its linear map. -/
theorem linearMap_eq_mul_comp_of_eventually_geometric
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (P : ℕ → ℝ[X])
    {y : ℝ[X]} {k : ℕ} (hT : ∀ n, T (X ^ n) = P n)
    (hk : k ≠ 0) (hy : y ≠ 0)
    (htail : ∀ n, k ≤ n → P n = P k * y ^ (n - k))
    (hdiscrepancy : ∀ j < k, geometricDiscrepancy P y k j = 0) :
    ∀ p, T p = P 0 * p.comp y :=
  linearMap_eq_mul_comp_of_eq_mul_pow T P y hT
    (eq_mul_pow_of_eventually_geometric_of_discrepancy_eq_zero
      hk hy htail hdiscrepancy)

/-- On a nonempty source class containing `1`, multiplication by a fixed
factor preserves split compositions exactly when that factor splits. -/
theorem forall_mem_splits_mul_comp_iff
    (S : Set ℝ[X]) (P₀ y : ℝ[X]) (hone : 1 ∈ S)
    (hcomp : ∀ p ∈ S, (p.comp y).Splits) :
    (∀ p ∈ S, (P₀ * p.comp y).Splits) ↔ P₀.Splits := by
  constructor
  · intro h
    simpa using h 1 hone
  · intro hP₀ p hp
    exact hP₀.mul (hcomp p hp)

/-- A nonzero prefix discrepancy produces a non-split shifted-power image in
the explicit window from `max k (D + 3)` through `k - 1` degrees later. -/
theorem exists_not_splits_binomialShiftImage_of_eventually_geometric
    {P : ℕ → ℝ[X]} {a d r : ℝ} {k : ℕ}
    (hd : d ≠ 0) (hPk : P k ≠ 0)
    (htail : ∀ n, k ≤ n →
      P n = P k * (C a + C d * X) ^ (n - k))
    (hexists : ∃ j < k,
      geometricDiscrepancy P (C a + C d * X) k j ≠ 0)
    (hr : r ≠ 0) :
    let D := geometricDiscrepancyDegree P (C a + C d * X) k
    let N₀ := max k (D + 3)
    ∃ N, N₀ ≤ N ∧ N ≤ N₀ + k - 1 ∧
      ¬(binomialShiftImage P r N).Splits := by
  let y : ℝ[X] := C a + C d * X
  let D := geometricDiscrepancyDegree P y k
  let N₀ := max k (D + 3)
  change ∃ N, N₀ ≤ N ∧ N ≤ N₀ + k - 1 ∧
    ¬(binomialShiftImage P r N).Splits
  by_contra hw
  have hall : ∀ N, N₀ ≤ N → N ≤ N₀ + k - 1 →
      (binomialShiftImage P r N).Splits := by
    intro N hlow hhigh
    by_contra hsplit
    exact hw ⟨N, hlow, hhigh, hsplit⟩
  have hN₀k : k ≤ N₀ := le_max_left _ _
  have hwindow : ∀ t < k,
      ∑ j ∈ Finset.range k,
        C (((N₀ + t).choose j : ℝ) * r ^ (N₀ + t - j)) *
          geometricDiscrepancy P y k j = 0 := by
    intro t ht
    let N := N₀ + t
    let c : ℝ[X] := ∑ j ∈ Finset.range k,
      C ((N.choose j : ℝ) * r ^ (N - j)) *
        geometricDiscrepancy P y k j
    have hNlow : N₀ ≤ N := by dsimp [N]; lia
    have hNhigh : N ≤ N₀ + k - 1 := by dsimp [N]; lia
    have hNge : k ≤ N := hN₀k.trans hNlow
    have himage := hall N hNlow hNhigh
    have hyrepr : y = C d * (X - C (-a / d)) := by
      dsimp [y]
      ext n
      simp [div_eq_mul_inv]
      field_simp
      ring
    have hysplit : y.Splits := by
      rw [hyrepr]
      exact (Polynomial.Splits.C d).mul (Polynomial.Splits.X_sub_C _)
    have hleft : (y ^ k * binomialShiftImage P r N).Splits :=
      (hysplit.pow k).mul himage
    have hidentity := pow_mul_binomialShiftImage_eq_add_discrepancies
      (P := P) (y := y) (r := r) hNge (by
        intro n hn
        simpa [y] using htail n hn)
    have hsum : (P k * (y + C r) ^ N + c).Splits := by
      rw [← hidentity]
      exact hleft
    have haffine : y + C r = C d * (X - C (-(a + r) / d)) := by
      dsimp [y]
      ext n
      simp [div_eq_mul_inv]
      field_simp
      ring
    rw [haffine] at hsum
    have hcdeg : c.natDegree ≤ D := by
      apply natDegree_sum_le_of_forall_le
      intro j hj
      refine (natDegree_C_mul_le _ _).trans ?_
      simpa [D, geometricDiscrepancyDegree] using
        (Finset.le_sup
          (f := fun i ↦ (geometricDiscrepancy P y k i).natDegree) hj)
    have hc0 : c = 0 := eq_zero_of_add_scaled_linear_pow_splits
      hPk hd hcdeg (by dsimp [N, N₀]; lia) hsum
    simpa [c, N] using hc0
  have hallzero := eq_zero_of_sum_choose_mul_pow_eq_zero_on_window
    (fun j ↦ geometricDiscrepancy P y k j) hr hN₀k hwindow
  obtain ⟨j, hj, hj0⟩ := hexists
  exact hj0 (by simpa [y] using hallzero j hj)

/-- The shifted-power image is the value of the linear map determined by the
row family on the corresponding shifted monomial. -/
theorem linearMap_add_C_pow_eq_binomialShiftImage
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (P : ℕ → ℝ[X])
    (hT : ∀ n, T (X ^ n) = P n) (r : ℝ) (N : ℕ) :
    T ((X + C r) ^ N) = binomialShiftImage P r N := by
  rw [add_pow, map_sum, binomialShiftImage]
  apply Finset.sum_congr rfl
  intro j hj
  have hterm : X ^ j * C r ^ (N - j) * (N.choose j : ℝ[X]) =
      ((N.choose j : ℝ) * r ^ (N - j)) • X ^ j := by
    rw [show (N.choose j : ℝ[X]) = C (N.choose j : ℝ) by simp]
    rw [smul_eq_C_mul, map_mul, map_pow]
    ring
  rw [hterm, map_smul, hT, smul_eq_C_mul]

/-- A nonzero discrepancy gives an explicit shifted power whose image under
the row-defined linear map is not split. -/
theorem exists_not_splits_linearMap_shiftedPower_of_eventually_geometric
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {P : ℕ → ℝ[X]} {a d r : ℝ} {k : ℕ}
    (hT : ∀ n, T (X ^ n) = P n)
    (hd : d ≠ 0) (hPk : P k ≠ 0)
    (htail : ∀ n, k ≤ n →
      P n = P k * (C a + C d * X) ^ (n - k))
    (hexists : ∃ j < k,
      geometricDiscrepancy P (C a + C d * X) k j ≠ 0)
    (hr : r ≠ 0) :
    let D := geometricDiscrepancyDegree P (C a + C d * X) k
    let N₀ := max k (D + 3)
    ∃ N, N₀ ≤ N ∧ N ≤ N₀ + k - 1 ∧
      ¬(T ((X + C r) ^ N)).Splits := by
  obtain ⟨N, hlow, hhigh, hN⟩ :=
    exists_not_splits_binomialShiftImage_of_eventually_geometric
      hd hPk htail hexists hr
  refine ⟨N, hlow, hhigh, ?_⟩
  rwa [linearMap_add_C_pow_eq_binomialShiftImage T P hT r N]

end

end RealRooted
