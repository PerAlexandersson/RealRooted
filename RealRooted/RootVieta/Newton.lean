/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.DegreeDropReversal
import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import RealRooted.Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Newton identities and the Hermite--Sylvester criterion

This file combines the evaluated Newton recurrence with Vieta's formulas for
polynomial roots. It gives a high-coefficient recurrence for ordinary roots
and an all-order low-coefficient recurrence for reciprocal roots. It also
defines the Hermite matrix of a real polynomial and proves the
Hermite--Sylvester real-rootedness criterion.
-/

open Polynomial

noncomputable section

namespace RealRooted.RootVieta

variable {K : Type*} [Field K]

/-- The elementary symmetric functions of the reversed roots are the low
coefficient ratios of the original polynomial. This all-index form also covers
indices above the degree, where both sides vanish. -/
theorem reverse_roots_esymm_eq_coeff_div
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) (k : ℕ) :
    p.reverse.roots.esymm k = (-1 : K) ^ k * p.coeff k / p.coeff 0 := by
  by_cases hk : k ≤ p.natDegree
  · have hqsplit : p.reverse.Splits := DegreeDropReversal.splits_reverse hp
    have hqdeg : p.reverse.natDegree = p.natDegree := by
      calc
        p.reverse.natDegree = p.reverse.roots.card :=
          hqsplit.natDegree_eq_card_roots
        _ = p.roots.card := DegreeDropReversal.card_roots_reverse hp h0
        _ = p.natDegree := hp.natDegree_eq_card_roots.symm
    have hqlc : p.reverse.leadingCoeff = p.coeff 0 := by
      rw [Polynomial.reverse_leadingCoeff,
        Polynomial.trailingCoeff_eq_coeff_zero h0]
    have hqcoeff :
        p.reverse.coeff (p.reverse.natDegree - k) = p.coeff k := by
      rw [hqdeg, Polynomial.coeff_reverse,
        Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk]
    have hkq : k ≤ p.reverse.natDegree := by rw [hqdeg]; exact hk
    rw [hqsplit.esymm_roots_eq_coeff_div_leadingCoeff
      (DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne h0) hkq,
      hqcoeff, hqlc]
  · have hkn : p.natDegree < k := Nat.lt_of_not_ge hk
    have hcard : p.reverse.roots.card < k := by
      rw [DegreeDropReversal.card_roots_reverse hp h0,
        ← hp.natDegree_eq_card_roots]
      exact hkn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkn]
    simp only [mul_zero, zero_div]
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty k hcard]

/-- Power sums of the reversed roots are reciprocal-root power sums of the
original polynomial, with multiplicities preserved. -/
theorem reverse_roots_powerSum_eq_sum_inv_pow
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) (k : ℕ) :
    p.reverse.roots.powerSum k =
      (p.roots.map fun r => r⁻¹ ^ k).sum := by
  rw [DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne
    hp h0]
  simp [Multiset.powerSum]

/-- Newton recurrence for root power sums, expressed through the high
coefficients of a split polynomial. -/
theorem leadingCoeff_mul_roots_powerSum
    {p : K[X]} (hp : p.Splits) (hne : p ≠ 0)
    (k : ℕ) (hk : 0 < k) (hkdeg : k ≤ p.natDegree) :
    p.leadingCoeff * p.roots.powerSum k =
      -(k : K) * p.coeff (p.natDegree - k) -
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff (p.natDegree - a.1) * p.roots.powerSum a.2 := by
  have hn := Multiset.powerSum_eq_mul_esymm_sub_sum p.roots k hk
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hsign (n : ℕ) : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hfirst :
      (-1 : K) ^ (k + 1) * (k : K) * p.roots.esymm k =
        (-(k : K) * p.coeff (p.natDegree - k)) / p.leadingCoeff := by
    rw [hp.esymm_roots_eq_coeff_div_leadingCoeff hne hkdeg,
      pow_succ, div_eq_mul_inv]
    calc
      _ = -(((-1 : K) ^ k * (-1 : K) ^ k) *
          ((k : K) * p.coeff (p.natDegree - k) *
            p.leadingCoeff⁻¹)) := by ring
      _ = _ := by rw [hsign]; ring
  have hsummand (i j : ℕ) (hi : i ≤ p.natDegree) :
      (-1 : K) ^ i * p.roots.esymm i * p.roots.powerSum j =
        (p.coeff (p.natDegree - i) * p.roots.powerSum j) /
          p.leadingCoeff := by
    rw [hp.esymm_roots_eq_coeff_div_leadingCoeff hne hi,
      div_eq_mul_inv]
    calc
      _ = ((-1 : K) ^ i * (-1 : K) ^ i) *
          (p.coeff (p.natDegree - i) * p.roots.powerSum j *
            p.leadingCoeff⁻¹) := by ring
      _ = _ := by rw [hsign]; ring
  rw [hfirst] at hn
  have hsum :
      (∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : K) ^ a.1 * p.roots.esymm a.1 *
            p.roots.powerSum a.2) =
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (p.coeff (p.natDegree - a.1) * p.roots.powerSum a.2) /
            p.leadingCoeff := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter] at ha
    apply hsummand
    exact (Set.mem_Ioo.mp ha.2).2.le.trans hkdeg
  rw [hsum, ← Finset.sum_div, ← sub_div] at hn
  have hscaled := (eq_div_iff hlc).mp hn
  calc
    p.leadingCoeff * p.roots.powerSum k =
        p.roots.powerSum k * p.leadingCoeff := mul_comm _ _
    _ = _ := hscaled

/-- Newton recurrence for power sums of the reversed roots, expressed through
the low coefficients of the original polynomial. -/
theorem coeff_zero_mul_reverse_roots_powerSum
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    p.coeff 0 * p.reverse.roots.powerSum k =
      -(k : K) * p.coeff k -
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff a.1 * p.reverse.roots.powerSum a.2 := by
  have hn := Multiset.powerSum_eq_mul_esymm_sub_sum
    p.reverse.roots k hk
  simp_rw [reverse_roots_esymm_eq_coeff_div hp h0] at hn
  have hsign (n : ℕ) : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hfirst :
      (-1 : K) ^ (k + 1) * (k : K) *
          ((-1 : K) ^ k * p.coeff k / p.coeff 0) =
        (-(k : K) * p.coeff k) / p.coeff 0 := by
    rw [pow_succ, div_eq_mul_inv]
    calc
      _ = -(((-1 : K) ^ k * (-1 : K) ^ k) *
          ((k : K) * p.coeff k * (p.coeff 0)⁻¹)) := by ring
      _ = _ := by rw [hsign]; ring
  have hsummand (i j : ℕ) :
      (-1 : K) ^ i *
          ((-1 : K) ^ i * p.coeff i / p.coeff 0) *
          p.reverse.roots.powerSum j =
        (p.coeff i * p.reverse.roots.powerSum j) / p.coeff 0 := by
    rw [div_eq_mul_inv]
    calc
      _ = ((-1 : K) ^ i * (-1 : K) ^ i) *
          (p.coeff i * p.reverse.roots.powerSum j *
            (p.coeff 0)⁻¹) := by ring
      _ = _ := by rw [hsign]; ring
  rw [hfirst] at hn
  simp_rw [hsummand] at hn
  rw [← Finset.sum_div, ← sub_div] at hn
  have hscaled := (eq_div_iff h0).mp hn
  calc
    p.coeff 0 * p.reverse.roots.powerSum k =
        p.reverse.roots.powerSum k * p.coeff 0 := mul_comm _ _
    _ = _ := hscaled

/-- Consumer-facing reciprocal-root form of
`coeff_zero_mul_reverse_roots_powerSum`. -/
theorem coeff_zero_mul_sum_inv_roots_pow
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    p.coeff 0 * (p.roots.map fun r => r⁻¹ ^ k).sum =
      -(k : K) * p.coeff k -
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff a.1 * (p.roots.map fun r => r⁻¹ ^ a.2).sum := by
  simpa only [reverse_roots_powerSum_eq_sum_inv_pow hp h0] using
    coeff_zero_mul_reverse_roots_powerSum hp h0 k hk

end RealRooted.RootVieta

/-! ## Hermite--Sylvester criterion -/

open Matrix

namespace Polynomial

/-- The roots of the complexification of a real polynomial, with multiplicity. -/
def complexRoots (p : ℝ[X]) : Multiset ℂ :=
  (p.map Complex.ofRealHom).roots

/-- The `k`-th power sum of the complex roots of a real polynomial. -/
def complexNewtonSum (p : ℝ[X]) (k : ℕ) : ℂ :=
  (complexRoots p).powerSum k

private lemma map_star_complexification (p : ℝ[X]) :
    (p.map Complex.ofRealHom).map (starRingEnd ℂ) =
      p.map Complex.ofRealHom := by
  ext k
  simp [coeff_map]

private lemma map_star_complexRoots (p : ℝ[X]) :
    (complexRoots p).map (starRingEnd ℂ) = complexRoots p := by
  have h := (IsAlgClosed.splits (p.map Complex.ofRealHom)).roots_map
    (starRingEnd ℂ)
  rw [map_star_complexification] at h
  exact h.symm

private lemma star_complexNewtonSum (p : ℝ[X]) (k : ℕ) :
    star (complexNewtonSum p k) = complexNewtonSum p k := by
  change (starRingEnd ℂ) (complexNewtonSum p k) = complexNewtonSum p k
  rw [complexNewtonSum, Multiset.map_powerSum, map_star_complexRoots]

private lemma complexNewtonSum_im (p : ℝ[X]) (k : ℕ) :
    (complexNewtonSum p k).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_complexNewtonSum p k)

/-- The real Newton sum obtained from the roots of a real polynomial. -/
def newtonSum (p : ℝ[X]) (k : ℕ) : ℝ :=
  (complexNewtonSum p k).re

private lemma ofReal_newtonSum (p : ℝ[X]) (k : ℕ) :
    (newtonSum p k : ℂ) = complexNewtonSum p k := by
  rw [newtonSum, ← Complex.conj_eq_iff_re]
  exact star_complexNewtonSum p k

/-- The elementary symmetric function expressed through the coefficients of a
monic polynomial, extended by zero above the degree. -/
def monicElementaryCoeff (p : ℝ[X]) (k : ℕ) : ℝ :=
  if k ≤ p.natDegree then (-1 : ℝ) ^ k * p.coeff (p.natDegree - k) else 0

private lemma esymm_complexRoots_eq_monicElementaryCoeff {p : ℝ[X]}
    (hp : p.Monic) (k : ℕ) :
    (complexRoots p).esymm k = (monicElementaryCoeff p k : ℂ) := by
  by_cases hk : k ≤ p.natDegree
  · have hqmonic : (p.map Complex.ofRealHom).Monic := hp.map _
    have hqsplit : (p.map Complex.ofRealHom).Splits := IsAlgClosed.splits _
    rw [complexRoots,
      hqsplit.esymm_roots_eq_coeff_div_leadingCoeff hqmonic.ne_zero
        (by simpa [hqmonic.natDegree_map] using hk)]
    simp [monicElementaryCoeff, hk, hp.natDegree_map, hp.leadingCoeff]
  · have hcard : (complexRoots p).card < k := by
      rw [complexRoots, ← (IsAlgClosed.splits
        (p.map Complex.ofRealHom)).natDegree_eq_card_roots,
        hp.natDegree_map]
      exact Nat.lt_of_not_ge hk
    simp [monicElementaryCoeff, hk, Multiset.esymm,
      Multiset.powersetCard_eq_empty k hcard]

/-- Newton's recurrence expressed entirely through the coefficients of a monic
real polynomial. -/
theorem newtonSum_eq_monicElementaryCoeff_sub_sum {p : ℝ[X]}
    (hp : p.Monic) (k : ℕ) (hk : 0 < k) :
    newtonSum p k =
      (-1 : ℝ) ^ (k + 1) * k * monicElementaryCoeff p k -
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℝ) ^ a.1 * monicElementaryCoeff p a.1 * newtonSum p a.2 := by
  have h := Multiset.powerSum_eq_mul_esymm_sub_sum (complexRoots p) k hk
  simp_rw [esymm_complexRoots_eq_monicElementaryCoeff hp] at h
  have hre := congrArg Complex.re h
  have hneg_re (n : ℕ) : ((-1 : ℂ) ^ n).re = (-1 : ℝ) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]
  have hneg_im (n : ℕ) : ((-1 : ℂ) ^ n).im = 0 := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]
  have hpower_im (n : ℕ) : ((complexRoots p).powerSum n).im = 0 :=
    complexNewtonSum_im p n
  simpa [complexNewtonSum, newtonSum, hneg_re, hneg_im, hpower_im] using hre

/-- Exact first-order regression for the coefficient-side Newton recurrence. -/
theorem newtonSum_one_eq_neg_nextCoeff {p : ℝ[X]} (hp : p.Monic)
    (hdeg : 1 ≤ p.natDegree) :
    newtonSum p 1 = -p.coeff (p.natDegree - 1) := by
  have h := newtonSum_eq_monicElementaryCoeff_sub_sum hp 1 (by norm_num)
  have ha : (Finset.HasAntidiagonal.antidiagonal 1).filter
      (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 1) = ∅ := by decide
  rw [ha] at h
  simpa [monicElementaryCoeff, hdeg] using h

/-- Exact second-order regression for the coefficient-side Newton recurrence. -/
theorem newtonSum_two_eq_sq_sub_two_mul_nextCoeff {p : ℝ[X]} (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) :
    newtonSum p 2 = p.coeff (p.natDegree - 1) ^ 2 -
      2 * p.coeff (p.natDegree - 2) := by
  have h := newtonSum_eq_monicElementaryCoeff_sub_sum hp 2 (by norm_num)
  have ha : (Finset.HasAntidiagonal.antidiagonal 2).filter
      (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by decide
  rw [ha] at h
  simp only [Finset.sum_singleton, pow_one] at h
  rw [newtonSum_one_eq_neg_nextCoeff hp (by lia)] at h
  simp [monicElementaryCoeff, show 1 ≤ p.natDegree by lia, hdeg] at h
  nlinarith

private lemma sum_coe_pow {R : Type*} [CommSemiring R] [DecidableEq R]
    (s : Multiset R) (k : ℕ) :
    (∑ x : s.ToType, (x : R) ^ k) = s.powerSum k := by
  classical
  calc
    _ = (((Finset.univ : Finset s.ToType).val.map
        fun x : s.ToType => (x : R) ^ k).sum) := rfl
    _ = (s.map fun x : R => x ^ k).sum :=
      congrArg Multiset.sum (Multiset.map_univ s fun x : R => x ^ k)
    _ = _ := rfl

private lemma newtonSum_eq_roots_powerSum {p : ℝ[X]} (hp : p.Splits) (k : ℕ) :
    newtonSum p k = p.roots.powerSum k := by
  apply Complex.ofReal_injective
  rw [ofReal_newtonSum, complexNewtonSum, complexRoots, hp.roots_map,
    ← Multiset.map_powerSum]
  rfl

/-- The Hermite matrix whose entries are Newton sums of the complex roots. -/
def hermiteMatrix (p : ℝ[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) ℝ :=
  fun i j => newtonSum p (i + j)

/-- The Hermite matrix of a real polynomial is Hermitian. -/
lemma hermiteMatrix_isHermitian (p : ℝ[X]) :
    (hermiteMatrix p).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by simp [hermiteMatrix, add_comm]

/-- A polynomial that splits over the reals has positive-semidefinite Hermite
matrix, with repeated roots represented by repeated Gram-matrix rows. -/
theorem hermiteMatrix_posSemidef_of_splits {p : ℝ[X]} (hp : p.Splits) :
    (hermiteMatrix p).PosSemidef := by
  classical
  let V : Matrix p.roots (Fin p.natDegree) ℝ := fun r j => (r : ℝ) ^ j.val
  have hmatrix : hermiteMatrix p = Vᴴ * V := by
    ext i j
    rw [hermiteMatrix, newtonSum_eq_roots_powerSum hp, Matrix.mul_apply]
    simp_rw [Matrix.conjTranspose_apply]
    simp [V, pow_add, ← sum_coe_pow]
  rw [hmatrix]
  exact posSemidef_conjTranspose_mul_self V

private lemma eval_eq_sum_fin {f : ℂ[X]} {n : ℕ} (hdeg : f.natDegree < n) (z : ℂ) :
    f.eval z = ∑ i : Fin n, f.coeff i * z ^ i.val := by
  rw [f.eval_eq_sum_range' hdeg]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => f.coeff i * z ^ i) n).symm

private lemma ofReal_im_eq_sub_star_div (z : ℂ) :
    (z.im : ℂ) = (z - star z) / (2 * Complex.I) := by
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im]
  ring

private lemma sum_im_coeff_mul_pow {f : ℂ[X]} {n : ℕ}
    (hdeg : f.natDegree < n) (z : ℂ) :
    (∑ i : Fin n, (f.coeff i).im * z ^ i.val : ℂ) =
      (f.eval z - star (f.eval (star z))) / (2 * Complex.I) := by
  rw [eval_eq_sum_fin hdeg z, eval_eq_sum_fin hdeg (star z)]
  change (∑ i : Fin n, (f.coeff i).im * z ^ i.val : ℂ) =
    ((∑ i : Fin n, f.coeff i * z ^ i.val) -
      (starRingEnd ℂ) (∑ i : Fin n, f.coeff i * star z ^ i.val)) /
        (2 * Complex.I)
  rw [map_sum]
  simp only [map_mul, map_pow]
  have hzstar : (starRingEnd ℂ) (star z) = z := star_star z
  rw [hzstar]
  simp_rw [ofReal_im_eq_sub_star_div]
  calc
    _ = ∑ i : Fin n, (f.coeff i * z ^ i.val -
        star (f.coeff i) * z ^ i.val) / (2 * Complex.I) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      simp only [starRingEnd_apply]

private lemma ofReal_dotProduct_hermiteMatrix_mulVec (p : ℝ[X])
    (b : Fin p.natDegree → ℝ) :
    ((b ⬝ᵥ hermiteMatrix p *ᵥ b : ℝ) : ℂ) =
      ∑ r ∈ (complexRoots p).toFinset,
        (complexRoots p).count r *
          (∑ i : Fin p.natDegree, (b i : ℂ) * r ^ i.val) ^ 2 := by
  classical
  change Complex.ofRealHom (b ⬝ᵥ hermiteMatrix p *ᵥ b) = _
  simp only [dotProduct, mulVec, hermiteMatrix]
  simp only [map_sum, map_mul]
  change (∑ i, (b i : ℂ) * ∑ j,
      (newtonSum p (i.val + j.val) : ℂ) * (b j : ℂ)) = _
  simp_rw [ofReal_newtonSum, complexNewtonSum, Multiset.powerSum,
    Finset.sum_multiset_map_count]
  simp_rw [nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ r ∈ (complexRoots p).toFinset, ∑ j,
        (b x : ℂ) * ((complexRoots p).count r * r ^ (x.val + j.val) *
          (b j : ℂ)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ r ∈ (complexRoots p).toFinset, ∑ x, ∑ j,
        (b x : ℂ) * ((complexRoots p).count r * r ^ (x.val + j.val) *
          (b j : ℂ)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_two]
      simp_rw [pow_add, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma lagrange_im_coeff_eval_sq {s : Finset ℂ} {z r : ℂ}
    (hz : z ∈ s) (hr : r ∈ s) (hstar : ∀ w ∈ s, star w ∈ s)
    (hzstar : star z ≠ z) {n : ℕ} (hcard : s.card ≤ n) :
    (∑ i : Fin n, ((Lagrange.basis s id z).coeff i).im * r ^ i.val : ℂ) ^ 2 =
      if r = z ∨ r = star z then -1 / 4 else 0 := by
  classical
  let f : ℂ[X] := Lagrange.basis s id z
  have hinj : Set.InjOn (id : ℂ → ℂ) (↑s : Set ℂ) := Set.injOn_id _
  have hspos : 0 < s.card := Finset.card_pos.mpr ⟨z, hz⟩
  have hdeg : f.natDegree < n := by
    rw [Lagrange.natDegree_basis hinj hz]
    lia
  have heval_one : f.eval z = 1 := by
    dsimp [f]
    exact Lagrange.eval_basis_self (s := s) (v := id) (i := z) hinj hz
  have heval_zero {w : ℂ} (hw : w ∈ s) (hzw : z ≠ w) : f.eval w = 0 := by
    dsimp [f]
    exact Lagrange.eval_basis_of_ne (s := s) (v := id) (i := z) (j := w) hzw hw
  have hconst : ((1 : ℂ) / (2 * Complex.I)) ^ 2 = -1 / 4 := by
    apply Complex.ext <;>
      norm_num [Complex.div_re, Complex.div_im, pow_two, Complex.mul_re,
        Complex.mul_im]
  rw [sum_im_coeff_mul_pow hdeg]
  by_cases hrz : r = z
  · subst r
    rw [heval_one, heval_zero (hstar z hz) (Ne.symm hzstar)]
    simpa only [star_zero, sub_zero, true_or, ite_true] using hconst
  · by_cases hrstar : r = star z
    · subst r
      rw [heval_zero (hstar z hz) (Ne.symm hzstar)]
      have hevalstar : f.eval (star (star z)) = 1 := by
        simpa only [star_star] using heval_one
      rw [hevalstar]
      simp only [star_one, zero_sub, or_true, ite_true]
      convert hconst using 1
      ring
    · have hne : z ≠ star r := by grind [star_star]
      rw [heval_zero hr (Ne.symm hrz), heval_zero (hstar r hr) hne]
      simp only [star_zero, sub_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0),
        hrz, false_or]
      simp only [hrstar, ite_false]

private lemma splits_of_all_roots_real_aux {p : ℝ[X]}
    (hall : ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → z.im = 0) :
    p.Splits := by
  refine Splits.of_splits_map Complex.ofRealHom (IsAlgClosed.splits _) ?_
  intro z hz
  refine ⟨z.re, ?_⟩
  simpa [hall z (isRoot_of_mem_roots hz)] using Complex.re_add_im z

/-- **Hermite--Sylvester criterion.** A monic real polynomial splits over the
reals if and only if its Hermite matrix is positive semidefinite. -/
theorem splits_iff_hermiteMatrix_posSemidef {p : ℝ[X]} (hp : p.Monic) :
    p.Splits ↔ (hermiteMatrix p).PosSemidef := by
  constructor
  · exact hermiteMatrix_posSemidef_of_splits
  · intro hpos
    apply splits_of_all_roots_real_aux
    intro z hz
    by_contra hzreal
    have hzmem : z ∈ complexRoots p := by
      rw [complexRoots, mem_roots (hp.map _).ne_zero]
      exact hz
    have hzfin : z ∈ (complexRoots p).toFinset := Multiset.mem_toFinset.mpr hzmem
    have hzstar : star z ≠ z := by
      intro h
      exact hzreal (Complex.conj_eq_iff_im.mp h)
    have hstar (w : ℂ) (hw : w ∈ (complexRoots p).toFinset) :
        star w ∈ (complexRoots p).toFinset := by
      rw [Multiset.mem_toFinset] at hw ⊢
      simpa only [map_star_complexRoots] using
        (Multiset.mem_map.mpr ⟨w, hw, rfl⟩ : star w ∈
          (complexRoots p).map (starRingEnd ℂ))
    have hcard : (complexRoots p).toFinset.card ≤ p.natDegree := by
      convert Multiset.toFinset_card_le (complexRoots p) using 1
      rw [complexRoots, ← (IsAlgClosed.splits
        (p.map Complex.ofRealHom)).natDegree_eq_card_roots, hp.natDegree_map]
    let f : ℂ[X] := Lagrange.basis (complexRoots p).toFinset id z
    let b : Fin p.natDegree → ℝ := fun i => (f.coeff i).im
    have hb_sq (r : ℂ) (hr : r ∈ (complexRoots p).toFinset) :
        (∑ i : Fin p.natDegree, (b i : ℂ) * r ^ i.val) ^ 2 =
          if r = z ∨ r = star z then -1 / 4 else 0 := by
      dsimp [b, f]
      exact lagrange_im_coeff_eval_sq hzfin hr hstar hzstar hcard
    have hformC' : ((b ⬝ᵥ hermiteMatrix p *ᵥ b : ℝ) : ℂ) =
        ∑ r ∈ (complexRoots p).toFinset,
          ((complexRoots p).count r : ℂ) *
            (if r = z ∨ r = star z then (-1 / 4 : ℂ) else 0) := by
      rw [ofReal_dotProduct_hermiteMatrix_mulVec]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hb_sq r hr]
    have hform : b ⬝ᵥ hermiteMatrix p *ᵥ b =
        ∑ r ∈ (complexRoots p).toFinset,
          if r = z ∨ r = star z then
            -((complexRoots p).count r : ℝ) / 4 else 0 := by
      have h := congrArg Complex.re hformC'
      simp only [Complex.ofReal_re] at h
      rw [h]
      change Complex.reAddGroupHom
        (∑ r ∈ (complexRoots p).toFinset,
          ((complexRoots p).count r : ℂ) *
            (if r = z ∨ r = star z then (-1 / 4 : ℂ) else 0)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs
      · simp [Complex.mul_re]
        ring
      · simp
    have hzcount : 0 < (complexRoots p).count z := Multiset.count_pos.mpr hzmem
    have hrest :
        ∑ r ∈ (complexRoots p).toFinset.erase z,
          (if r = z ∨ r = star z then
            -((complexRoots p).count r : ℝ) / 4 else 0) ≤ 0 := by
      apply Finset.sum_nonpos
      intro r _
      split_ifs
      · exact div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num)
      · exact le_rfl
    have hform_neg : b ⬝ᵥ hermiteMatrix p *ᵥ b < 0 := by
      rw [hform, ← Finset.add_sum_erase _ _ hzfin]
      simp only [true_or, ite_true]
      have hzterm : -((complexRoots p).count z : ℝ) / 4 < 0 := by
        have hzcountR : (0 : ℝ) < (complexRoots p).count z := by
          exact_mod_cast hzcount
        nlinarith
      exact add_neg_of_neg_of_nonpos hzterm hrest
    have hform_nonneg : 0 ≤ b ⬝ᵥ hermiteMatrix p *ᵥ b := by
      simpa using hpos.dotProduct_mulVec_nonneg b
    linarith

end Polynomial
