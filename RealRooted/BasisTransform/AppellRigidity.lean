module

public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer

import RealRooted.LaguerreSamuelson
import RealRooted.Linear
import RealRooted.Mathlib.LinearAlgebra.Matrix.Polynomial.PosDef
import RealRooted.SameDegreeMultiplicityLowerCount

/-!
# Rigidity of root-preserving monic basis transforms

This file develops the differential coefficients of a degree-triangular
polynomial basis and the resulting coefficient diagonals.
-/

public section

open Finset Polynomial

noncomputable section

namespace RealRooted

/-- The image of a repeated-root input, translated so that the repeated input
root is at the origin. -/
def shiftedPowerImage (P : ℕ → ℝ[X]) (k : ℕ) (r : ℝ) : ℝ[X] :=
  (basisTransform P ((X + C r) ^ k)).comp (X - C r)

/-- Unfolding lemma for `shiftedPowerImage`. -/
theorem shiftedPowerImage_eq (P : ℕ → ℝ[X]) (k : ℕ) (r : ℝ) :
    shiftedPowerImage P k r = (basisTransform P ((X + C r) ^ k)).comp (X - C r) := by
  simp only [shiftedPowerImage]

/-- The shifted repeated-root image splits exactly when the untranslated image splits. -/
theorem splits_shiftedPowerImage_iff (P : ℕ → ℝ[X]) (k : ℕ) (r : ℝ) :
    (shiftedPowerImage P k r).Splits ↔ (basisTransform P ((X + C r) ^ k)).Splits := by
  rw [shiftedPowerImage_eq]
  constructor
  · intro h
    have := h.comp_X_add_C r
    simpa [comp_assoc] using this
  · intro h
    simpa [sub_eq_add_neg] using h.comp_X_add_C (-r)

/-- The repeated-root image before translation, as an explicit sum over the basis. -/
theorem basisTransform_add_pow (P : ℕ → ℝ[X]) (k : ℕ) (r : ℝ) :
    basisTransform P ((X + C r) ^ k) =
      ∑ j ∈ range (k + 1),
        C ((k.choose j : ℝ) * r ^ (k - j)) * P j := by
  rw [add_pow, basisTransform_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show X ^ j * C r ^ (k - j) * (k.choose j : ℝ[X]) =
      C ((k.choose j : ℝ) * r ^ (k - j)) * X ^ j by
    simp [C_mul, C_pow]
    ring]
  rw [basisTransform_C_mul_X_pow]

/-- The `k`-th polynomial coefficient in the differential expansion of the
basis transform with basis `P`. -/
def appellCoefficient (P : ℕ → ℝ[X]) (k : ℕ) : ℝ[X] :=
  C ((k.factorial : ℝ)⁻¹) *
    ∑ j ∈ range (k + 1),
      C (k.choose j : ℝ) * ((-X) ^ (k - j) * P j)

/-- Evaluation of the top differential coefficient is the constant term of
the shifted repeated-root image. -/
theorem eval_zero_shiftedPowerImage
    (P : ℕ → ℝ[X]) (k : ℕ) (r : ℝ) :
    (shiftedPowerImage P k r).eval 0 =
      (k.factorial : ℝ) * (appellCoefficient P k).eval (-r) := by
  rw [shiftedPowerImage, eval_comp, basisTransform_add_pow]
  simp [appellCoefficient, eval_finsetSum]
  field_simp

/-- For a monic basis of exact degrees, the shifted repeated-root image is monic. -/
theorem shiftedPowerImage_monic
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) (k : ℕ) (r : ℝ) :
    (shiftedPowerImage P k r).Monic := by
  have hinput : ((X + C r) ^ k : ℝ[X]).Monic := (monic_X_add_C r).pow k
  have himage := basisTransform_monic_of_monic hPdeg hPmonic hinput
  rw [shiftedPowerImage, show X - C r = X + C (-r) by rw [C_neg]; ring]
  exact himage.comp_X_add_C (-r)

/-- For a monic basis of exact degrees, the shifted repeated-root image has degree `k`. -/
theorem shiftedPowerImage_natDegree
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) (k : ℕ) (r : ℝ) :
    (shiftedPowerImage P k r).natDegree = k := by
  let G := basisTransform P ((X + C r) ^ k)
  have hinput : ((X + C r) ^ k : ℝ[X]).Monic := (monic_X_add_C r).pow k
  have hinputdeg : ((X + C r) ^ k : ℝ[X]).natDegree = k := by simp
  have hG_le : G.natDegree ≤ k := by
    exact (basisTransform_natDegree_le_of_natDegree_le
      (fun n => (hPdeg n).le) _).trans_eq hinputdeg
  have hGcoeff : G.coeff k = 1 := by
    simpa only [G, hinputdeg] using
      coeff_basisTransform_natDegree_eq_one_of_monic hPdeg hPmonic hinput
  have hkG : k ≤ G.natDegree := le_natDegree_of_ne_zero (by simp [hGcoeff])
  have hGdeg : G.natDegree = k := Nat.le_antisymm hG_le hkG
  rw [shiftedPowerImage, natDegree_comp, hGdeg, natDegree_X_sub_C, mul_one]

private theorem coeff_basisTransform_add_pow
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (k m : ℕ) (_hm : m ≤ k) (r : ℝ) :
    (basisTransform P ((X + C r) ^ k)).coeff (k - m) =
      ∑ j ∈ Icc (k - m) k,
        (k.choose j : ℝ) * r ^ (k - j) * (P j).coeff (k - m) := by
  rw [basisTransform_add_pow, finsetSum_coeff]
  have hsubset : Icc (k - m) k ⊆ range (k + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hj).2)
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_C_mul]
  · intro j hjrange hjIcc
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjrange)
    have hjm : j < k - m := lt_of_not_ge fun hmj =>
      hjIcc (Finset.mem_Icc.mpr ⟨hmj, hjk⟩)
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt]
    · simp
    · simpa only [hPdeg j] using hjm

private theorem coeff_basisTransform_add_pow_sub_one
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) {k : ℕ} (hk : 1 ≤ k) (r : ℝ) :
    (basisTransform P ((X + C r) ^ k)).coeff (k - 1) =
      (P k).coeff (k - 1) + k * r := by
  rw [coeff_basisTransform_add_pow hPdeg k 1 hk r]
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [← hks, Finset.sum_Icc_succ_top (by lia)]
  simp only [hks]
  rw [Finset.Icc_self, Finset.sum_singleton]
  have hlead : (P (k - 1)).coeff (k - 1) = 1 := by
    simpa only [hPdeg] using (hPmonic (k - 1)).coeff_natDegree
  rw [hlead]
  have hchoose : k.choose (k - 1) = k := by
    rw [Nat.choose_symm (by lia), Nat.choose_one_right]
  rw [hchoose]
  simp only [show k - (k - 1) = 1 by lia]
  simp
  ring

private theorem coeff_basisTransform_add_pow_sub_two
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) {k : ℕ} (hk : 2 ≤ k) (r : ℝ) :
    (basisTransform P ((X + C r) ^ k)).coeff (k - 2) =
      (P k).coeff (k - 2) +
        k * r * (P (k - 1)).coeff (k - 2) +
          (k.choose 2 : ℝ) * r ^ 2 := by
  rw [coeff_basisTransform_add_pow hPdeg k 2 hk r]
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel (by lia)
  have hks' : k - 2 + 1 = k - 1 := by lia
  rw [← hks, Finset.sum_Icc_succ_top (by lia)]
  simp only [hks]
  rw [← hks', Finset.sum_Icc_succ_top (by lia)]
  simp only [hks']
  rw [Finset.Icc_self, Finset.sum_singleton]
  have hlead : (P (k - 2)).coeff (k - 2) = 1 := by
    simpa only [hPdeg] using (hPmonic (k - 2)).coeff_natDegree
  rw [hlead]
  have hchoose : k.choose (k - 1) = k := by
    rw [Nat.choose_symm (by lia), Nat.choose_one_right]
  have hchoose_two : k.choose (k - 2) = k.choose 2 := by
    simpa only [show k - (k - 2) = 2 by lia] using
      (Nat.choose_symm (by lia : k - 2 ≤ k)).symm
  rw [hchoose]
  rw [hchoose_two]
  simp only [show k - (k - 2) = 2 by lia, show k - (k - 1) = 1 by lia]
  norm_num [Nat.choose_self]
  ring

private theorem coeff_taylor_sub_one {G : ℝ[X]} {k : ℕ} (hk : 1 ≤ k)
    (hG : G.natDegree ≤ k) (r : ℝ) :
    (taylor (-r) G).coeff (k - 1) =
      G.coeff (k - 1) - k * r * G.coeff k := by
  rw [coeff_taylor_eq_sum_range_of_natDegree_le G (-r) (k - 1) k hG]
  have hsubset : Icc (k - 1) k ⊆ range (k + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hi).2)
  rw [← Finset.sum_subset hsubset]
  · have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [← hks, Finset.sum_Icc_succ_top (by lia)]
    simp only [hks]
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hchoose : k.choose (k - 1) = k := by
      rw [Nat.choose_symm (by lia), Nat.choose_one_right]
    rw [hchoose]
    simp only [show k - (k - 1) = 1 by lia]
    norm_num
    ring
  · intro i hirange hiIcc
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hirange)
    have hi : i < k - 1 := lt_of_not_ge fun hki =>
      hiIcc (Finset.mem_Icc.mpr ⟨hki, hik⟩)
    rw [Nat.choose_eq_zero_of_lt hi]
    simp

private theorem coeff_taylor_sub_two {G : ℝ[X]} {k : ℕ} (hk : 2 ≤ k)
    (hG : G.natDegree ≤ k) (r : ℝ) :
    (taylor (-r) G).coeff (k - 2) =
      G.coeff (k - 2) - (k - 1) * r * G.coeff (k - 1) +
        (k.choose 2 : ℝ) * r ^ 2 * G.coeff k := by
  rw [coeff_taylor_eq_sum_range_of_natDegree_le G (-r) (k - 2) k hG]
  have hsubset : Icc (k - 2) k ⊆ range (k + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hi).2)
  rw [← Finset.sum_subset hsubset]
  · have hks : k - 1 + 1 = k := Nat.sub_add_cancel (by lia)
    have hks' : k - 2 + 1 = k - 1 := by lia
    rw [← hks, Finset.sum_Icc_succ_top (by lia)]
    simp only [hks]
    rw [← hks', Finset.sum_Icc_succ_top (by lia)]
    simp only [hks']
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hchoose_one : (k - 1).choose (k - 2) = k - 1 := by
      calc
        (k - 1).choose (k - 2) = (k - 1).choose 1 := by
          simpa only [show k - 1 - (k - 2) = 1 by lia] using
            (Nat.choose_symm (by lia : k - 2 ≤ k - 1)).symm
        _ = k - 1 := Nat.choose_one_right (k - 1)
    have hchoose_two : k.choose (k - 2) = k.choose 2 := by
      simpa only [show k - (k - 2) = 2 by lia] using
        (Nat.choose_symm (by lia : k - 2 ≤ k)).symm
    rw [hchoose_one, hchoose_two]
    simp only [show k - 1 - (k - 2) = 1 by lia, show k - (k - 2) = 2 by lia]
    norm_num
    rw [Nat.cast_sub (by lia : 1 ≤ k)]
    ring
  · intro i hirange hiIcc
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hirange)
    have hi : i < k - 2 := lt_of_not_ge fun hki =>
      hiIcc (Finset.mem_Icc.mpr ⟨hki, hik⟩)
    rw [Nat.choose_eq_zero_of_lt hi]
    simp

/-- Translation cancels the parameter from the first lower coefficient of a
repeated-root basis image. -/
theorem coeff_shiftedPowerImage_sub_one
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) {k : ℕ} (hk : 1 ≤ k) (r : ℝ) :
    (shiftedPowerImage P k r).coeff (k - 1) = (P k).coeff (k - 1) := by
  let G := basisTransform P ((X + C r) ^ k)
  have hinput : ((X + C r) ^ k : ℝ[X]).Monic := (monic_X_add_C r).pow k
  have hGmonic : G.Monic := basisTransform_monic_of_monic hPdeg hPmonic hinput
  have hGdeg : G.natDegree = k := by
    have hFdeg := shiftedPowerImage_natDegree hPdeg hPmonic k r
    rw [shiftedPowerImage, natDegree_comp, natDegree_X_sub_C, mul_one] at hFdeg
    exact hFdeg
  have hGtop : G.coeff k = 1 := by
    rw [← hGdeg]
    exact hGmonic.coeff_natDegree
  rw [shiftedPowerImage, show X - C r = X + C (-r) by rw [C_neg]; ring,
    ← taylor_apply]
  change (taylor (-r) G).coeff (k - 1) = _
  rw [coeff_taylor_sub_one hk hGdeg.le r,
    coeff_basisTransform_add_pow_sub_one hPdeg hPmonic hk r, hGtop]
  ring

/-- The second lower coefficient of the shifted repeated-root image is affine
in the repeated-root parameter. -/
theorem coeff_shiftedPowerImage_sub_two
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) {k : ℕ} (hk : 2 ≤ k) (r : ℝ) :
    (shiftedPowerImage P k r).coeff (k - 2) =
      (P k).coeff (k - 2) +
        (k * (P (k - 1)).coeff (k - 2) -
          (k - 1) * (P k).coeff (k - 1)) * r := by
  let G := basisTransform P ((X + C r) ^ k)
  have hinput : ((X + C r) ^ k : ℝ[X]).Monic := (monic_X_add_C r).pow k
  have hGmonic : G.Monic := basisTransform_monic_of_monic hPdeg hPmonic hinput
  have hGdeg : G.natDegree = k := by
    have hFdeg := shiftedPowerImage_natDegree hPdeg hPmonic k r
    rw [shiftedPowerImage, natDegree_comp, natDegree_X_sub_C, mul_one] at hFdeg
    exact hFdeg
  have hGtop : G.coeff k = 1 := by
    rw [← hGdeg]
    exact hGmonic.coeff_natDegree
  rw [shiftedPowerImage, show X - C r = X + C (-r) by rw [C_neg]; ring,
    ← taylor_apply]
  change (taylor (-r) G).coeff (k - 2) = _
  rw [coeff_taylor_sub_two hk hGdeg.le r,
    coeff_basisTransform_add_pow_sub_two hPdeg hPmonic hk r,
    coeff_basisTransform_add_pow_sub_one hPdeg hPmonic (by lia) r,
    hGtop, Nat.cast_choose_two]
  ring

private def binomialTranslate (x : ℝ[X]) (f : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), (n.choose j : ℝ[X]) * (x ^ (n - j) * f j)

private theorem binomialTranslate_succ (x : ℝ[X]) (f : ℕ → ℝ[X]) (n : ℕ) :
    binomialTranslate x f (n + 1) =
      x * binomialTranslate x f n + binomialTranslate x (fun j => f (j + 1)) n := by
  rw [binomialTranslate, show n + 1 + 1 = n + 2 by lia]
  rw [Finset.sum_choose_succ_mul (R := ℝ[X])
    (fun i j => x ^ j * f i) n]
  rw [binomialTranslate, binomialTranslate, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show n + 1 - i = (n - i) + 1 by
      have := Finset.mem_range.mp hi
      lia, pow_succ]
    ring

private theorem binomialTranslate_add (x : ℝ[X]) (f g : ℕ → ℝ[X]) (n : ℕ) :
    binomialTranslate x (fun j => f j + g j) n =
      binomialTranslate x f n + binomialTranslate x g n := by
  simp only [binomialTranslate, mul_add, Finset.sum_add_distrib]

private theorem binomialTranslate_mul_left
    (x c : ℝ[X]) (f : ℕ → ℝ[X]) (n : ℕ) :
    binomialTranslate x (fun j => c * f j) n = c * binomialTranslate x f n := by
  rw [binomialTranslate, binomialTranslate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem binomialTranslate_inverse (x : ℝ[X]) (f : ℕ → ℝ[X]) (n : ℕ) :
    binomialTranslate x (binomialTranslate (-x) f) n = f n := by
  induction n generalizing f with
  | zero => simp [binomialTranslate]
  | succ n ih =>
      rw [binomialTranslate_succ, ih]
      have hshift (j : ℕ) :
          binomialTranslate (-x) f (j + 1) =
            (-x) * binomialTranslate (-x) f j +
              binomialTranslate (-x) (fun i => f (i + 1)) j :=
        binomialTranslate_succ (-x) f j
      simp_rw [hshift]
      rw [binomialTranslate_add, binomialTranslate_mul_left]
      rw [ih f, ih (fun i => f (i + 1))]
      ring

private theorem factorial_mul_appellCoefficient
    (P : ℕ → ℝ[X]) (k : ℕ) :
    C (k.factorial : ℝ) * appellCoefficient P k =
      binomialTranslate (-X) P k := by
  rw [appellCoefficient, binomialTranslate, ← mul_assoc, ← C_mul]
  rw [mul_inv_cancel₀ (by positivity : (k.factorial : ℝ) ≠ 0), C_1, one_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- A sequence `Q` is a differential-coefficient expansion of the monic
basis `P` when every basis element has the displayed locally finite sum. -/
def IsAppellExpansion (P Q : ℕ → ℝ[X]) : Prop :=
  ∀ n, P n =
    ∑ k ∈ range (n + 1),
      C (n.descFactorial k : ℝ) * (X ^ (n - k) * Q k)

/-- The explicit differential coefficients form an Appell expansion of every
polynomial basis. -/
theorem isAppellExpansion_appellCoefficient (P : ℕ → ℝ[X]) :
    IsAppellExpansion P (appellCoefficient P) := by
  intro n
  calc
    P n = binomialTranslate X (binomialTranslate (-X) P) n :=
      (binomialTranslate_inverse X P n).symm
    _ = ∑ k ∈ range (n + 1),
        C (n.descFactorial k : ℝ) *
          (X ^ (n - k) * appellCoefficient P k) := by
      rw [show binomialTranslate X (binomialTranslate (-X) P) n =
          ∑ k ∈ range (n + 1), (n.choose k : ℝ[X]) *
            (X ^ (n - k) * binomialTranslate (-X) P k) by rfl]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← factorial_mul_appellCoefficient]
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, C_mul]
      rw [show (n.choose k : ℝ[X]) = C (n.choose k : ℝ) by rfl]
      ring

/-- Coefficients on a fixed diagonal of an Appell expansion are finite sums
of descending factorials. -/
theorem coeff_eq_sum_descFactorial_of_isAppellExpansion
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    {n j : ℕ} (hj : j ≤ n) :
    (P n).coeff (n - j) =
      ∑ k ∈ Icc j n,
        (n.descFactorial k : ℝ) * (Q k).coeff (k - j) := by
  rw [hPQ n, finsetSum_coeff]
  have hsubset : Icc j n ⊆ range (n + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hk).2)
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro k hk
    have hbounds := Finset.mem_Icc.mp hk
    have hkn := hbounds.2
    rw [coeff_C_mul, coeff_X_pow_mul', ite_eq_left (Nat.sub_le_sub_left hbounds.1 n)]
    congr 1
    have hadd : n - k + (k - j) = n - j :=
      Nat.sub_add_sub_cancel hkn hbounds.1
    exact congrArg (Q k).coeff (Nat.eq_sub_of_add_eq' hadd).symm
  · intro k hkrange hkIcc
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkrange)
    have hkj : k < j := lt_of_not_ge fun hjk =>
      hkIcc (Finset.mem_Icc.mpr ⟨hjk, hkn⟩)
    rw [coeff_C_mul, coeff_X_pow_mul', ite_eq_right (by
      exact not_le.mpr (Nat.sub_lt_sub_left (hkj.trans_le hj) hkj)), mul_zero]

/-- The polynomial in the row index describing diagonal `j`, after terms
outside the degree bound have been removed. -/
def appellDiagonalPolynomial (Q : ℕ → ℝ[X]) (j : ℕ) : ℝ[X] :=
  ∑ k ∈ Icc j (2 * j),
    C ((Q k).coeff (k - j)) * descPochhammer ℝ k

/-- The polynomial describing diagonal `j` has degree at most `2j`. -/
theorem appellDiagonalPolynomial_natDegree_le (Q : ℕ → ℝ[X]) (j : ℕ) :
    (appellDiagonalPolynomial Q j).natDegree ≤ 2 * j := by
  unfold appellDiagonalPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans <| by
    rw [descPochhammer_natDegree]
    exact (Finset.mem_Icc.mp hk).2

private theorem descPochhammer_dvd_of_le {j k : ℕ} (hjk : j ≤ k) :
    descPochhammer ℝ j ∣ descPochhammer ℝ k := by
  induction k with
  | zero => simp_all
  | succ k ih =>
      by_cases hjk' : j ≤ k
      · rw [descPochhammer_succ_right]
        exact dvd_mul_of_dvd_left (ih hjk') _
      · have : j = k + 1 := by lia
        simp [this]

/-- Every diagonal polynomial is divisible by the falling factorial of the
diagonal number. -/
theorem descPochhammer_dvd_appellDiagonalPolynomial
    (Q : ℕ → ℝ[X]) (j : ℕ) :
    descPochhammer ℝ j ∣ appellDiagonalPolynomial Q j := by
  unfold appellDiagonalPolynomial
  apply Finset.dvd_sum
  intro k hk
  exact dvd_mul_of_dvd_right
    (descPochhammer_dvd_of_le (Finset.mem_Icc.mp hk).1) _

/-- Evaluating a diagonal polynomial gives its finite falling-factorial sum. -/
theorem eval_appellDiagonalPolynomial (Q : ℕ → ℝ[X]) (j n : ℕ) :
    (appellDiagonalPolynomial Q j).eval (n : ℝ) =
      ∑ k ∈ Icc j (2 * j),
        (n.descFactorial k : ℝ) * (Q k).coeff (k - j) := by
  rw [appellDiagonalPolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]
  ring

/-- Under the half-degree bound, the coefficient of `X^(n-j)` in `P n`
is the value of the fixed polynomial `appellDiagonalPolynomial Q j`. -/
theorem coeff_eq_eval_appellDiagonalPolynomial
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    (hQ : ∀ k, (Q k).natDegree ≤ k / 2) {n j : ℕ} (hj : j ≤ n) :
    (P n).coeff (n - j) = (appellDiagonalPolynomial Q j).eval (n : ℝ) := by
  rw [coeff_eq_sum_descFactorial_of_isAppellExpansion hPQ hj,
    eval_appellDiagonalPolynomial]
  by_cases hn : n ≤ 2 * j
  · have hsubset : Icc j n ⊆ Icc j (2 * j) := Icc_subset_Icc_right hn
    rw [← Finset.sum_subset hsubset]
    intro k hkbig hksmall
    have hnk : n < k := by
      have hk := Finset.mem_Icc.mp hkbig
      exact lt_of_not_ge fun hkn => hksmall (Finset.mem_Icc.mpr ⟨hk.1, hkn⟩)
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnk, Nat.cast_zero, zero_mul]
  · have htwo : 2 * j ≤ n := by lia
    have hsubset : Icc j (2 * j) ⊆ Icc j n := Icc_subset_Icc_right htwo
    rw [Finset.sum_subset hsubset]
    intro k hkbig hksmall
    have hkj : 2 * j < k := by
      have hk := Finset.mem_Icc.mp hkbig
      exact lt_of_not_ge fun hkle =>
        hksmall (Finset.mem_Icc.mpr ⟨hk.1, hkle⟩)
    have hdeg : (Q k).natDegree < k - j := by
      calc
        (Q k).natDegree ≤ k / 2 := hQ k
        _ < k - j := by lia
    rw [coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]

/-- The coefficient diagonals of an Appell expansion are polynomials of degree
at most `2j`, divisible by the `j`-th falling factorial. -/
theorem exists_diagonalPolynomial_of_isAppellExpansion
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    (hQ : ∀ k, (Q k).natDegree ≤ k / 2) (j : ℕ) :
    ∃ A : ℝ[X], A.natDegree ≤ 2 * j ∧ descPochhammer ℝ j ∣ A ∧
      ∀ n, j ≤ n → (P n).coeff (n - j) = A.eval (n : ℝ) := by
  refine ⟨appellDiagonalPolynomial Q j,
    appellDiagonalPolynomial_natDegree_le Q j,
    descPochhammer_dvd_appellDiagonalPolynomial Q j, ?_⟩
  intro n hn
  exact coeff_eq_eval_appellDiagonalPolynomial hPQ hQ hn

/-- Explicit coefficient formula after the half-degree bound truncates the
locally finite differential expansion. -/
theorem coeff_eq_sum_of_isAppellExpansion
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    (hQ : ∀ k, (Q k).natDegree ≤ k / 2) {n j : ℕ} (hj : j ≤ n) :
    (P n).coeff (n - j) =
      ∑ k ∈ Icc j (2 * j),
        (n.descFactorial k : ℝ) * (Q k).coeff (k - j) := by
  rw [coeff_eq_eval_appellDiagonalPolynomial hPQ hQ hj,
    eval_appellDiagonalPolynomial]

/-- The first lower coefficient of an Appell expansion is affine-quadratic
in the row number. -/
theorem coeff_sub_one_eq_linear_add_choose
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    (hQ : ∀ k, (Q k).natDegree ≤ k / 2) {n : ℕ} (hn : 1 ≤ n) :
    (P n).coeff (n - 1) =
      (Q 1).coeff 0 * n +
        (2 * (Q 2).coeff 1) * (n.choose 2 : ℝ) := by
  rw [coeff_eq_sum_of_isAppellExpansion hPQ hQ hn]
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self,
    Finset.sum_singleton]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  norm_num
  have hchoose : n * (n - 1) = 2 * n.choose 2 := by
    calc
      n * (n - 1) = n.descFactorial 2 := by
        simp [Nat.descFactorial, Nat.mul_comm]
      _ = 2 * n.choose 2 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        norm_num
  have hchooseR : (n : ℝ) * (n - 1 : ℕ) = 2 * (n.choose 2 : ℝ) := by
    exact_mod_cast hchoose
  rw [mul_comm (↑(n - 1) : ℝ) (↑n : ℝ), hchooseR]
  ring

/-- The constant coefficient of the first differential coefficient is the
constant coefficient of `P 1`. -/
theorem coeff_zero_appellCoefficient_one
    {P : ℕ → ℝ[X]} (hPzero : P 0 = 1) :
    (appellCoefficient P 1).coeff 0 = (P 1).coeff 0 := by
  have hQ : appellCoefficient P 1 = P 1 - X := by
    norm_num [appellCoefficient, hPzero, Finset.sum_range_succ]
    ring
  rw [hQ, coeff_sub]
  simp

/-- Twice the linear coefficient of the second differential coefficient is
the first finite difference of the first lower basis coefficients. -/
theorem two_mul_coeff_one_appellCoefficient_two
    {P : ℕ → ℝ[X]} (hPzero : P 0 = 1) :
    2 * (appellCoefficient P 2).coeff 1 =
      (P 2).coeff 1 - 2 * (P 1).coeff 0 := by
  have hQ : appellCoefficient P 2 =
      C (2 : ℝ)⁻¹ * (X ^ 2 - C 2 * (X * P 1) + P 2) := by
    norm_num [appellCoefficient, hPzero, Finset.sum_range_succ]
    rw [show (2 : ℝ[X]) = C 2 by rfl]
    ring
  rw [hQ, coeff_C_mul, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul,
    coeff_X_mul]
  norm_num
  ring

private theorem slope_nonneg_of_affine_nonneg_on_nonneg {A B : ℝ}
    (h : ∀ r : ℝ, 0 ≤ r → 0 ≤ A + B * r) : 0 ≤ B := by
  by_contra hB
  have hBneg : B < 0 := lt_of_not_ge hB
  let r := (|A| + 1) / (-B)
  have hr : 0 ≤ r := by
    dsimp only [r]
    exact div_nonneg (by positivity) (neg_nonneg.mpr hBneg.le)
  have hvalue := h r hr
  have hB0 : B ≠ 0 := ne_of_lt hBneg
  dsimp only [r] at hvalue
  field_simp [hB0] at hvalue
  have hA := le_abs_self A
  linarith

/-- A polynomial whose square on the negative ray is bounded by the `k`-th
power of an affine function has degree at most `k / 2`. -/
theorem natDegree_le_half_of_sq_eval_neg_le_affine_pow
    {q : ℝ[X]} {k : ℕ} {A B : ℝ}
    (hbound : ∀ r : ℝ, 0 ≤ r → (q.eval (-r)) ^ 2 ≤ (A + B * r) ^ k) :
    q.natDegree ≤ k / 2 := by
  let g := q.comp (-(X ^ 2))
  let h := (C A + C B * X ^ 2) ^ k + 1
  have hg_eval (x : ℝ) : g.eval x = q.eval (-(x ^ 2)) := by
    simp [g]
  have hh_eval (x : ℝ) : h.eval x = (A + B * x ^ 2) ^ k + 1 := by
    simp [h]
  have hh_pos (x : ℝ) : 0 < h.eval x := by
    rw [hh_eval]
    nlinarith [hbound (x ^ 2) (sq_nonneg x)]
  have hsq (x : ℝ) : (g.eval x) ^ 2 ≤ (1 : ℝ[X]).eval x * h.eval x := by
    rw [hg_eval, hh_eval]
    simp only [eval_one, one_mul]
    exact (hbound (x ^ 2) (sq_nonneg x)).trans (by linarith)
  have hdegree := Polynomial.two_mul_natDegree_le_of_sq_eval_le_mul_eval
    (f := (1 : ℝ[X])) (g := g) (h := h) (by simp) hh_pos hsq
  have hg_degree : g.natDegree = 2 * q.natDegree := by
    simp [g, natDegree_comp, natDegree_neg, natDegree_pow, mul_comm]
  have hh_degree : h.natDegree ≤ 2 * k := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · calc
        ((C A + C B * X ^ 2) ^ k).natDegree =
            k * (C A + C B * X ^ 2).natDegree := natDegree_pow _ _
        _ ≤ k * 2 := Nat.mul_le_mul_left k <| by
          apply (natDegree_add_le _ _).trans
          apply max_le
          · simp
          · exact natDegree_mul_le.trans (by simp)
        _ = 2 * k := by ring
    · simp
  rw [hg_degree] at hdegree
  simp only [natDegree_one, zero_add] at hdegree
  have : 4 * q.natDegree ≤ 2 * k := by lia
  lia

private theorem multiset_prod_le_sum_pow_card
    (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) :
    s.prod ≤ s.sum ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : 0 ≤ a := hs a (by simp)
      have hs' : ∀ x ∈ s, 0 ≤ x := by simp_all
      have hsum : 0 ≤ s.sum := Multiset.sum_nonneg hs'
      have htotal : 0 ≤ a + s.sum := by positivity
      have hpow : s.sum ^ s.card ≤ (a + s.sum) ^ s.card :=
        pow_le_pow_left₀ hsum (by linarith) _
      calc
        (a ::ₘ s).prod = a * s.prod := by simp
        _ ≤ a * (s.sum ^ s.card) :=
          mul_le_mul_of_nonneg_left (ih hs') ha
        _ ≤ (a + s.sum) * ((a + s.sum) ^ s.card) :=
          mul_le_mul (by linarith) hpow (pow_nonneg hsum _) htotal
        _ = (a ::ₘ s).sum ^ (a ::ₘ s).card := by
          simp [pow_succ']

/-- The sum-of-squared-roots expression from the first two lower
coefficients of a monic split polynomial is nonnegative. -/
theorem coeff_sq_sub_two_mul_nonneg
    {p : ℝ[X]} {k : ℕ} (hp : p.Monic) (hdeg : p.natDegree = k)
    (hk : 2 ≤ k) (hsplits : p.Splits) :
    0 ≤ p.coeff (k - 1) ^ 2 - 2 * p.coeff (k - 2) := by
  have hcard : p.roots.card = k := (splits_iff_card_roots.mp hsplits).trans hdeg
  have hsum : p.roots.sum = -p.coeff (k - 1) := by
    rw [coeff_eq_esymm_roots_of_card (hcard.trans hdeg.symm) (by
      rw [hdeg]
      lia), hp.leadingCoeff, hdeg, show k - (k - 1) = 1 by lia,
      Samuelson.esymm_one]
    ring
  have hesymm : p.roots.esymm 2 = p.coeff (k - 2) := by
    rw [coeff_eq_esymm_roots_of_card (hcard.trans hdeg.symm) (by
      rw [hdeg]
      lia), hp.leadingCoeff, hdeg, show k - (k - 2) = 2 by lia]
    ring
  calc
    0 ≤ (p.roots.map (· ^ 2)).sum := Multiset.sum_nonneg fun x hx => by
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
      positivity
    _ = p.roots.sum ^ 2 - 2 * p.roots.esymm 2 := Samuelson.sum_map_sq_eq _
    _ = p.coeff (k - 1) ^ 2 - 2 * p.coeff (k - 2) := by
      rw [hsum, hesymm]
      ring

/-- For a monic split polynomial, the square of the constant term is bounded
by the appropriate power of the sum of the squared roots, written using the
first two lower coefficients. -/
theorem eval_zero_sq_le_coeff_sq_sub_two_mul_pow
    {p : ℝ[X]} {k : ℕ} (hp : p.Monic) (hdeg : p.natDegree = k)
    (hk : 2 ≤ k) (hsplits : p.Splits) :
    p.eval 0 ^ 2 ≤
      (p.coeff (k - 1) ^ 2 - 2 * p.coeff (k - 2)) ^ k := by
  have hcard : p.roots.card = k := (splits_iff_card_roots.mp hsplits).trans hdeg
  have hsum : p.roots.sum = -p.coeff (k - 1) := by
    rw [coeff_eq_esymm_roots_of_card (hcard.trans hdeg.symm) (by
      rw [hdeg]
      lia), hp.leadingCoeff, hdeg, show k - (k - 1) = 1 by lia,
      Samuelson.esymm_one]
    ring
  have hesymm : p.roots.esymm 2 = p.coeff (k - 2) := by
    rw [coeff_eq_esymm_roots_of_card (hcard.trans hdeg.symm) (by
      rw [hdeg]
      lia), hp.leadingCoeff, hdeg, show k - (k - 2) = 2 by lia]
    ring
  have hsqsum : (p.roots.map (· ^ 2)).sum =
      p.coeff (k - 1) ^ 2 - 2 * p.coeff (k - 2) := by
    rw [Samuelson.sum_map_sq_eq, hsum, hesymm]
    ring
  have hprod := multiset_prod_le_sum_pow_card (p.roots.map (· ^ 2)) (by
    intro x hx
    obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
    positivity)
  rw [Multiset.card_map, hcard, hsqsum] at hprod
  rw [hsplits.eval_eq_prod_roots, hp.leadingCoeff]
  simp only [one_mul, zero_sub]
  calc
    (p.roots.map fun x => -x).prod ^ 2 =
        (p.roots.map (· ^ 2)).prod := by
          induction p.roots using Multiset.induction_on with
          | empty => simp
          | cons a s ih =>
              simp only [Multiset.map_cons, Multiset.prod_cons]
              rw [mul_pow, ih]
              ring
    _ ≤ _ := hprod

/-- Repeated-root preservation through degree `k` forces the half-degree bound
on the `k`-th differential coefficient. -/
theorem appellCoefficient_natDegree_le_of_shiftedPower_splits
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic) {k : ℕ} (hk : 2 ≤ k)
    (hpres : ∀ r : ℝ, 0 ≤ r → (shiftedPowerImage P k r).Splits) :
    (appellCoefficient P k).natDegree ≤ k / 2 := by
  let q := C (k.factorial : ℝ) * appellCoefficient P k
  let A := (P k).coeff (k - 1) ^ 2 - 2 * (P k).coeff (k - 2)
  let B := -2 *
    (k * (P (k - 1)).coeff (k - 2) -
      (k - 1) * (P k).coeff (k - 1))
  have hbound : ∀ r : ℝ, 0 ≤ r → (q.eval (-r)) ^ 2 ≤ (A + B * r) ^ k := by
    intro r hr
    have hroot := eval_zero_sq_le_coeff_sq_sub_two_mul_pow
      (shiftedPowerImage_monic hPdeg hPmonic k r)
      (shiftedPowerImage_natDegree hPdeg hPmonic k r) hk (hpres r hr)
    rw [eval_zero_shiftedPowerImage] at hroot
    simp only [q, eval_mul, eval_C]
    rw [coeff_shiftedPowerImage_sub_one hPdeg hPmonic (by lia) r,
      coeff_shiftedPowerImage_sub_two hPdeg hPmonic hk r] at hroot
    dsimp only [A, B]
    convert hroot using 1
    ring
  have hdegree := natDegree_le_half_of_sq_eval_neg_le_affine_pow hbound
  have hfactorial : (k.factorial : ℝ) ≠ 0 := by positivity
  simpa only [q, natDegree_C_mul hfactorial] using hdegree

/-- A degree-triangular monic basis transform preserving every polynomial with
nonpositive real roots satisfies the half-degree bound on its differential
coefficients. -/
theorem appellCoefficient_natDegree_le
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) (k : ℕ) :
    (appellCoefficient P k).natDegree ≤ k / 2 := by
  by_cases hk : 2 ≤ k
  · apply appellCoefficient_natDegree_le_of_shiftedPower_splits
      hPdeg hPmonic hk
    intro r hr
    have hinput : ((X + C r) ^ k : ℝ[X]).Splits :=
      (Polynomial.Splits.X_add_C r).pow k
    have hroots : ∀ x ∈ ((X + C r) ^ k : ℝ[X]).roots, x ≤ 0 := by
      intro x hx
      rw [roots_pow, roots_X_add_C] at hx
      have hx' : x = -r := Multiset.mem_singleton.mp (Multiset.mem_nsmul.mp hx).2
      rw [hx']
      exact neg_nonpos.mpr hr
    have himage := hpres ((X + C r) ^ k) hinput hroots
    have hnonzero : basisTransform P ((X + C r) ^ k) ≠ 0 :=
      (basisTransform_monic_of_monic hPdeg hPmonic
        ((monic_X_add_C r).pow k)).ne_zero
    rw [shiftedPowerImage, show X - C r = X + C (-r) by rw [C_neg]; ring]
    exact (isRealRooted_comp_X_add_C hnonzero himage (-r)).2
  · have hk' : k ≤ 1 := by lia
    interval_cases k
    · have hPzero : P 0 = 1 :=
        eq_one_of_monic_natDegree_zero (hPmonic 0) (hPdeg 0)
      simp [appellCoefficient, hPzero]
    · have hPzero : P 0 = 1 :=
        eq_one_of_monic_natDegree_zero (hPmonic 0) (hPdeg 0)
      have hQ : appellCoefficient P 1 = P 1 - X := by
        norm_num [appellCoefficient, hPzero, Finset.sum_range_succ]
        ring
      rw [hQ]
      have hPone : (P 1).IsMonicOfDegree 1 := ⟨hPdeg 1, hPmonic 1⟩
      have hX : (X : ℝ[X]).IsMonicOfDegree 1 := ⟨natDegree_X, monic_X⟩
      exact Nat.le_zero.mpr <|
        Nat.lt_one_iff.mp (hPone.natDegree_sub_lt (by lia) hX)

/-- A root-preserving monic basis has the explicit finite formula for every
coefficient diagonal. -/
theorem coeff_eq_sum_appellCoefficient
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    {n j : ℕ} (hj : j ≤ n) :
    (P n).coeff (n - j) =
      ∑ k ∈ Icc j (2 * j),
        (n.descFactorial k : ℝ) * (appellCoefficient P k).coeff (k - j) := by
  exact coeff_eq_sum_of_isAppellExpansion
    (isAppellExpansion_appellCoefficient P)
    (appellCoefficient_natDegree_le hPdeg hPmonic hpres) hj

/-- Every coefficient diagonal of a root-preserving monic basis is a
falling-factorial-divisible polynomial of degree at most twice its index. -/
theorem exists_diagonalPolynomial
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) (j : ℕ) :
    ∃ A : ℝ[X], A.natDegree ≤ 2 * j ∧ descPochhammer ℝ j ∣ A ∧
      ∀ n, j ≤ n → (P n).coeff (n - j) = A.eval (n : ℝ) := by
  exact exists_diagonalPolynomial_of_isAppellExpansion
    (isAppellExpansion_appellCoefficient P)
    (appellCoefficient_natDegree_le hPdeg hPmonic hpres) j

/-- Root preservation forces the quadratic coefficient governing the first
lower basis diagonal to be nonnegative. -/
theorem two_mul_coeff_one_appellCoefficient_two_nonneg
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) :
    0 ≤ 2 * (appellCoefficient P 2).coeff 1 := by
  have hsplits (r : ℝ) (hr : 0 ≤ r) : (shiftedPowerImage P 2 r).Splits := by
    have hinput : ((X + C r) ^ 2 : ℝ[X]).Splits :=
      (Polynomial.Splits.X_add_C r).pow 2
    have hroots : ∀ x ∈ ((X + C r) ^ 2 : ℝ[X]).roots, x ≤ 0 := by
      intro x hx
      rw [roots_pow, roots_X_add_C] at hx
      have hx' : x = -r := Multiset.mem_singleton.mp (Multiset.mem_nsmul.mp hx).2
      rw [hx']
      exact neg_nonpos.mpr hr
    have himage := hpres ((X + C r) ^ 2) hinput hroots
    have hnonzero : basisTransform P ((X + C r) ^ 2) ≠ 0 :=
      (basisTransform_monic_of_monic hPdeg hPmonic
        ((monic_X_add_C r).pow 2)).ne_zero
    rw [shiftedPowerImage, show X - C r = X + C (-r) by rw [C_neg]; ring]
    exact (isRealRooted_comp_X_add_C hnonzero himage (-r)).2
  have hslope : 0 ≤ -2 *
      (2 * (P 1).coeff 0 - (P 2).coeff 1) := by
    apply slope_nonneg_of_affine_nonneg_on_nonneg
      (A := (P 2).coeff 1 ^ 2 - 2 * (P 2).coeff 0)
    intro r hr
    have h := coeff_sq_sub_two_mul_nonneg
      (shiftedPowerImage_monic hPdeg hPmonic 2 r)
      (shiftedPowerImage_natDegree hPdeg hPmonic 2 r) (by norm_num) (hsplits r hr)
    rw [coeff_shiftedPowerImage_sub_one hPdeg hPmonic (by norm_num) r,
      coeff_shiftedPowerImage_sub_two hPdeg hPmonic (by norm_num) r] at h
    norm_num at h
    nlinarith [h]
  have hPzero : P 0 = 1 :=
    eq_one_of_monic_natDegree_zero (hPmonic 0) (hPdeg 0)
  rw [two_mul_coeff_one_appellCoefficient_two hPzero]
  linarith

/-- Under the explicit Appell expansion, root preservation makes the first
lower coefficient diagonal `α n + β * choose n 2` with `β ≥ 0`. -/
theorem exists_coeff_sub_one_eq_linear_add_choose
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) :
    ∃ α β : ℝ, 0 ≤ β ∧ ∀ n, 1 ≤ n →
      (P n).coeff (n - 1) = α * n + β * (n.choose 2 : ℝ) := by
  refine ⟨(appellCoefficient P 1).coeff 0,
    2 * (appellCoefficient P 2).coeff 1,
    two_mul_coeff_one_appellCoefficient_two_nonneg hPdeg hPmonic hpres, ?_⟩
  intro n hn
  exact coeff_sub_one_eq_linear_add_choose (isAppellExpansion_appellCoefficient P)
    (appellCoefficient_natDegree_le hPdeg hPmonic hpres) hn

end RealRooted
