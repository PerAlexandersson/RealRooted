import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Degree
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Basic
import RealRooted.Interlacing.ResidueCriterion

/-! # Degree bookkeeping for the weighted deco transform -/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDecoTransform_monic (w : ℝ) {p : ℝ[X]} (hp : p.Monic) :
    (weightedDecoTransform w p).Monic :=
  Polynomial.basisTransform_monic_of_monic
    (weightedDecoEulerian_natDegree w) (weightedDecoEulerian_monic w) hp

theorem weightedDecoDiagonal_monic (w : ℝ) (n : ℕ) (a : ℝ) :
    (weightedDecoDiagonal w n a).Monic :=
  weightedDecoTransform_monic w ((monic_X_add_C a).pow n)

@[simp]
theorem weightedDecoDiagonal_natDegree (w : ℝ) (n : ℕ) (a : ℝ) :
    (weightedDecoDiagonal w n a).natDegree = n := by
  have hle : (weightedDecoDiagonal w n a).natDegree ≤ n := by
    unfold weightedDecoDiagonal weightedDecoTransform
    calc
      (Polynomial.basisTransform (weightedDecoEulerian w)
          ((X + C a) ^ n)).natDegree ≤ ((X + C a) ^ n).natDegree :=
        Polynomial.basisTransform_natDegree_le_of_natDegree_le
          (fun m ↦ (weightedDecoEulerian_natDegree w m).le) ((X + C a) ^ n)
      _ = n := by
        rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
        simp
  have hcoeff : (weightedDecoDiagonal w n a).coeff n = 1 := by
    have hinput : ((X + C a) ^ n).Monic := (monic_X_add_C a).pow n
    have hdegInput : ((X + C a) ^ n).natDegree = n := by
      rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
      simp
    rw [← hdegInput]
    simpa [weightedDecoDiagonal, weightedDecoTransform] using
      (Polynomial.coeff_basisTransform_natDegree_eq_one_of_monic
        (weightedDecoEulerian_natDegree w) (weightedDecoEulerian_monic w) hinput)
  exact natDegree_eq_of_le_of_coeff_ne_zero hle (by norm_num [hcoeff])

theorem weightedDecoDiagonal_hasPosLeadingCoeff (w : ℝ) (n : ℕ) (a : ℝ) :
    HasPosLeadingCoeff (weightedDecoDiagonal w n a) :=
  hasPosLeadingCoeff_of_monic (weightedDecoDiagonal_monic w n a)

@[simp]
theorem weightedDecoLagBasis_natDegree (w : ℝ) (n : ℕ) :
    (weightedDecoLagBasis w n).natDegree = n - 1 := by
  cases n with
  | zero => simp [weightedDecoLagBasis]
  | succ n => simp [weightedDecoLagBasis, weightedDecoEulerian_natDegree]

theorem weightedDecoDiagonalLag_natDegree_lt (w : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (a : ℝ) :
    (weightedDecoDiagonalLag w n a).natDegree < n := by
  have hinputDegree : ((X + C a) ^ n).natDegree = n := by
    rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
    simp
  unfold weightedDecoDiagonalLag weightedDecoLagTransform
  refine lt_of_le_of_lt
    (Polynomial.basisTransform_natDegree_le_of_support ?_) (Nat.sub_lt hn zero_lt_one)
  intro m hm
  rw [weightedDecoLagBasis_natDegree]
  have hmle : m ≤ n := by
    rw [← hinputDegree]
    exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hm)
  exact Nat.sub_le_sub_right hmle 1

theorem weightedDecoDiagonalLag_degree_lt (w : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (a : ℝ) :
    (weightedDecoDiagonalLag w n a).degree < n := by
  calc
    (weightedDecoDiagonalLag w n a).degree ≤
        ((weightedDecoDiagonalLag w n a).natDegree : WithBot ℕ) :=
      degree_le_natDegree
    _ < n := by exact_mod_cast weightedDecoDiagonalLag_natDegree_lt w hn a

theorem weightedDecoCompanionBasis_degree_lt (w : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (weightedDecoCompanionBasis w n).degree < n := by
  have hpoly : 1 ≤ (weightedDecoEulerian w n).natDegree := by
    rw [weightedDecoEulerian_natDegree]
    exact hn
  have hzero : (0 : ℝ[X]).degree < (weightedDecoEulerian w n).natDegree := by
    simp
  have haux := residueAuxiliary_degree_lt hpoly hzero 1 0
  have hform :
      weightedDecoCompanionBasis w n =
        residueAuxiliary 1 0 (weightedDecoEulerian w n) 0 +
          C w * weightedDecoLagBasis w n := by
    simp [weightedDecoCompanionBasis, residueAuxiliary]
    ring
  rw [hform]
  apply (degree_add_le _ _).trans_lt
  rw [max_lt_iff]
  constructor
  · simpa [weightedDecoEulerian_natDegree] using haux
  · calc
      (C w * weightedDecoLagBasis w n).degree ≤
          ((C w * weightedDecoLagBasis w n).natDegree : WithBot ℕ) :=
        degree_le_natDegree
      _ ≤ (weightedDecoLagBasis w n).natDegree := by
        exact_mod_cast natDegree_C_mul_le w (weightedDecoLagBasis w n)
      _ < n := by
        rw [weightedDecoLagBasis_natDegree]
        exact_mod_cast Nat.sub_lt hn zero_lt_one

theorem weightedDecoCompanionBasis_natDegree_le (w : ℝ) (n : ℕ) :
    (weightedDecoCompanionBasis w n).natDegree ≤ n - 1 := by
  cases n with
  | zero => simp [weightedDecoCompanionBasis, weightedDecoLagBasis]
  | succ n =>
      have hlt := weightedDecoCompanionBasis_degree_lt w (n := n + 1) (by lia)
      by_cases hzero : weightedDecoCompanionBasis w (n + 1) = 0
      · simp [hzero]
      · have hnat : (weightedDecoCompanionBasis w (n + 1)).natDegree < n + 1 :=
          (natDegree_lt_iff_degree_lt hzero).2 hlt
        lia

theorem weightedDecoDiagonalCompanion_natDegree_lt (w : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (a : ℝ) :
    (weightedDecoDiagonalCompanion w n a).natDegree < n := by
  have hinputDegree : ((X + C a) ^ n).natDegree = n := by
    rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
    simp
  unfold weightedDecoDiagonalCompanion weightedDecoCompanionTransform
  refine lt_of_le_of_lt
    (Polynomial.basisTransform_natDegree_le_of_support ?_) (Nat.sub_lt hn zero_lt_one)
  intro m hm
  refine (weightedDecoCompanionBasis_natDegree_le w m).trans ?_
  have hmle : m ≤ n := by
    rw [← hinputDegree]
    exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hm)
  exact Nat.sub_le_sub_right hmle 1

theorem weightedDecoDiagonalCompanion_degree_lt (w : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (a : ℝ) :
    (weightedDecoDiagonalCompanion w n a).degree < n := by
  calc
    (weightedDecoDiagonalCompanion w n a).degree ≤
        ((weightedDecoDiagonalCompanion w n a).natDegree : WithBot ℕ) :=
      degree_le_natDegree
    _ < n := by
      exact_mod_cast weightedDecoDiagonalCompanion_natDegree_lt w hn a

end RealRooted.Applications.OEIS
