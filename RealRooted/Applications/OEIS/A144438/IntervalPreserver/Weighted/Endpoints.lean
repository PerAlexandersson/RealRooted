import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Degree
import RealRooted.BasisTransform

/-! # Endpoint estimates for the weighted diagonal family -/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

theorem HasNonnegCoeffs.weightedDecoTransform {w : ℝ} (hw : 0 ≤ w)
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (weightedDecoTransform w p) :=
  hp.basisTransform (weightedDecoEulerian_hasNonnegCoeffs hw)

theorem HasNonnegCoeffs.weightedDecoLagTransform {w : ℝ} (hw : 0 ≤ w)
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (weightedDecoLagTransform w p) := by
  apply hp.basisTransform
  intro n
  cases n with
  | zero => simpa [weightedDecoLagBasis] using hasNonnegCoeffs_zero
  | succ n => exact weightedDecoEulerian_hasNonnegCoeffs hw n

theorem weightedDecoTransform_eval_zero (w : ℝ) (p : ℝ[X]) :
    (weightedDecoTransform w p).eval 0 = p.eval 1 := by
  rw [← coeff_zero_eq_eval_zero, weightedDecoTransform,
    Polynomial.coeff_basisTransform, Polynomial.eval_eq_sum]
  simp

theorem weightedDecoDiagonal_hasNonnegCoeffs {w : ℝ} (hw : 0 ≤ w)
    {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (weightedDecoDiagonal w n a) := by
  apply HasNonnegCoeffs.weightedDecoTransform hw
  exact (hasNonnegCoeffs_X.add (hasNonnegCoeffs_C ha)).pow n

theorem weightedDecoDiagonalLag_hasNonnegCoeffs {w : ℝ} (hw : 0 ≤ w)
    {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (weightedDecoDiagonalLag w n a) := by
  apply HasNonnegCoeffs.weightedDecoLagTransform hw
  exact (hasNonnegCoeffs_X.add (hasNonnegCoeffs_C ha)).pow n

@[simp]
theorem weightedDecoDiagonal_eval_zero (w : ℝ) (n : ℕ) (a : ℝ) :
    (weightedDecoDiagonal w n a).eval 0 = (1 + a) ^ n := by
  rw [weightedDecoDiagonal, weightedDecoTransform_eval_zero]
  simp

theorem weightedDecoDiagonal_ne_zero (w : ℝ) {n : ℕ} {a : ℝ}
    (ha : -1 < a) : weightedDecoDiagonal w n a ≠ 0 := by
  intro hzero
  have h := congrArg (fun p : ℝ[X] ↦ p.eval 0) hzero
  simp only [weightedDecoDiagonal_eval_zero, eval_zero] at h
  have hbase : 0 < 1 + a := by linarith
  have hpow : 0 < (1 + a) ^ n := pow_pos hbase n
  linarith

theorem weightedDecoDiagonal_eval_one_pos {w : ℝ} (hw : 0 ≤ w)
    {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    0 < (weightedDecoDiagonal w n a).eval 1 :=
  eval_pos_of_hasNonnegCoeffs (weightedDecoDiagonal_hasNonnegCoeffs hw ha)
    (weightedDecoDiagonal_ne_zero w (by linarith)) (by norm_num)

theorem weightedDecoDiagonalLag_eval_one_nonneg {w : ℝ} (hw : 0 ≤ w)
    {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (weightedDecoDiagonalLag w n a).eval 1 := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg fun k _ ↦
    mul_nonneg (weightedDecoDiagonalLag_hasNonnegCoeffs hw ha k) (by positivity)

def weightedDecoDiagonalAtOne (w : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  (weightedDecoDiagonal w n a).eval 1

def weightedDecoDiagonalLagAtOne (w : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  (weightedDecoDiagonalLag w n a).eval 1

def weightedDecoGamma (w : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  weightedDecoDiagonalAtOne w n a / weightedDecoDiagonalAtOne w (n - 1) a

def weightedDecoKappa (w : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  weightedDecoDiagonalLagAtOne w n a / weightedDecoDiagonalAtOne w n a

def weightedDecoEta (w : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  (n : ℝ) * a / weightedDecoGamma w n a

@[simp]
theorem weightedDecoDiagonalAtOne_zero (w a : ℝ) :
    weightedDecoDiagonalAtOne w 0 a = 1 := by
  simp [weightedDecoDiagonalAtOne]

@[simp]
theorem weightedDecoDiagonalAtOne_one (w a : ℝ) :
    weightedDecoDiagonalAtOne w 1 a = 2 + a := by
  simp [weightedDecoDiagonalAtOne]
  ring

@[simp]
theorem weightedDecoDiagonalLagAtOne_one (w a : ℝ) :
    weightedDecoDiagonalLagAtOne w 1 a = 1 := by
  simp [weightedDecoDiagonalLagAtOne]

@[simp]
theorem weightedDecoGamma_one (w a : ℝ) :
    weightedDecoGamma w 1 a = 2 + a := by
  simp [weightedDecoGamma]

@[simp]
theorem weightedDecoKappa_one (w a : ℝ) :
    weightedDecoKappa w 1 a = 1 / (2 + a) := by
  simp [weightedDecoKappa]

theorem weightedDecoDiagonalLagAtOne_succ (w : ℝ) (n : ℕ) (a : ℝ) :
    weightedDecoDiagonalLagAtOne w (n + 1) a =
      weightedDecoDiagonalAtOne w n a +
        a * weightedDecoDiagonalLagAtOne w n a := by
  change (weightedDecoDiagonalLag w (n + 1) a).eval 1 =
    (weightedDecoDiagonal w n a).eval 1 +
      a * (weightedDecoDiagonalLag w n a).eval 1
  rw [weightedDecoDiagonalLag_succ]
  simp only [eval_add, eval_mul, eval_C]

theorem weightedDecoDiagonalAtOne_succ_succ (w : ℝ) (n : ℕ) (a : ℝ) :
    weightedDecoDiagonalAtOne w (n + 2) a =
      ((n : ℝ) + 3 + a) * weightedDecoDiagonalAtOne w (n + 1) a -
        ((n : ℝ) + 1) * a * weightedDecoDiagonalAtOne w n a +
          w * weightedDecoDiagonalLagAtOne w (n + 1) a := by
  rw [weightedDecoDiagonalAtOne, weightedDecoDiagonal_succ,
    weightedDecoDiagonalCompanion_succ_eq]
  simp only [eval_add, eval_sub, eval_mul, eval_one, eval_X, eval_C, one_mul,
    weightedDecoDiagonalAtOne, weightedDecoDiagonalLagAtOne]
  ring

theorem weightedDecoGamma_succ_succ (w : ℝ) (n : ℕ) {a : ℝ}
    (hw : 0 ≤ w) (ha : 0 ≤ a) :
    weightedDecoGamma w (n + 2) a =
      (n : ℝ) + 3 + a - ((n : ℝ) + 1) * a /
        weightedDecoGamma w (n + 1) a +
          w * weightedDecoKappa w (n + 1) a := by
  have hp0 := weightedDecoDiagonal_eval_one_pos hw (n := n) ha
  have hp1 := weightedDecoDiagonal_eval_one_pos hw (n := n + 1) ha
  rw [weightedDecoGamma, weightedDecoGamma, weightedDecoKappa]
  rw [show n + 2 - 1 = n + 1 by lia, show n + 1 - 1 = n by lia]
  rw [weightedDecoDiagonalAtOne_succ_succ]
  have hp0' : weightedDecoDiagonalAtOne w n a ≠ 0 := ne_of_gt hp0
  have hp1' : weightedDecoDiagonalAtOne w (n + 1) a ≠ 0 := ne_of_gt hp1
  field_simp [hp0', hp1']

theorem weightedDecoKappa_succ (w : ℝ) (n : ℕ) {a : ℝ}
    (hw : 0 ≤ w) (ha : 0 ≤ a) :
    weightedDecoKappa w (n + 1) a =
      (1 + a * weightedDecoKappa w n a) / weightedDecoGamma w (n + 1) a := by
  have hp := weightedDecoDiagonal_eval_one_pos hw (n := n) ha
  have hpSucc := weightedDecoDiagonal_eval_one_pos hw (n := n + 1) ha
  rw [weightedDecoKappa, weightedDecoGamma, weightedDecoKappa,
    weightedDecoDiagonalLagAtOne_succ]
  simp only [Nat.add_sub_cancel]
  have hp' : weightedDecoDiagonalAtOne w n a ≠ 0 := ne_of_gt hp
  have hpSucc' : weightedDecoDiagonalAtOne w (n + 1) a ≠ 0 := ne_of_gt hpSucc
  field_simp [hp', hpSucc']

theorem weightedDeco_endpoint_bounds {w a : ℝ}
    (hw0 : 0 ≤ w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * a + 1 < weightedDecoGamma w n a ∧
        2 + a ≤ weightedDecoGamma w n a ∧
          0 ≤ weightedDecoKappa w n a ∧ weightedDecoKappa w n a ≤ 1 / 2 := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero =>
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
        one_mul, Nat.reduceAdd]
      change a + 1 < weightedDecoGamma w 1 a ∧
        2 + a ≤ weightedDecoGamma w 1 a ∧
          0 ≤ weightedDecoKappa w 1 a ∧ weightedDecoKappa w 1 a ≤ 1 / 2
      rw [weightedDecoGamma_one, weightedDecoKappa_one]
      constructor
      · linarith
      constructor
      · rfl
      constructor
      · positivity
      · have : 0 < 2 + a := by linarith
        rw [div_le_iff₀ this]
        linarith
  | succ m ih =>
      have ih' :
          (m + 1 : ℝ) * a + 1 < weightedDecoGamma w (m + 1) a ∧
            2 + a ≤ weightedDecoGamma w (m + 1) a ∧
              0 ≤ weightedDecoKappa w (m + 1) a ∧
                weightedDecoKappa w (m + 1) a ≤ 1 / 2 := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.add_comm, add_comm] using ih
      have hgammaRec := weightedDecoGamma_succ_succ w m hw0 ha0
      have hkappaRec := weightedDecoKappa_succ w (m + 1) hw0 ha0
      have hgammaPos : 0 < weightedDecoGamma w (m + 1) a := by
        have : 0 ≤ (m + 1 : ℝ) * a := by positivity
        linarith [ih'.1]
      have heta :
          (m + 1 : ℝ) * a / weightedDecoGamma w (m + 1) a < 1 := by
        rw [div_lt_one hgammaPos]
        linarith [ih'.1]
      have hwKappa : 0 ≤ w * weightedDecoKappa w (m + 1) a :=
        mul_nonneg hw0 ih'.2.2.1
      have hgammaStrong :
          (m + 2 : ℝ) + a < weightedDecoGamma w (m + 2) a := by
        rw [hgammaRec]
        linarith
      have hgammaLinear :
          (m + 2 : ℝ) * a + 1 < weightedDecoGamma w (m + 2) a := by
        have : (m + 2 : ℝ) * a + 1 ≤ (m + 2 : ℝ) + a := by
          nlinarith
        linarith
      have hgammaFloor : 2 + a ≤ weightedDecoGamma w (m + 2) a := by
        linarith
      have hkappaNonneg : 0 ≤ weightedDecoKappa w (m + 2) a := by
        rw [hkappaRec]
        have hnum : 0 ≤ 1 + a * weightedDecoKappa w (m + 1) a :=
          add_nonneg zero_le_one (mul_nonneg ha0 ih'.2.2.1)
        exact div_nonneg hnum
          (le_trans (by linarith : 0 ≤ 2 + a) hgammaFloor)
      have hkappaHalf : weightedDecoKappa w (m + 2) a ≤ 1 / 2 := by
        rw [hkappaRec, div_le_iff₀ (lt_of_lt_of_le (by linarith) hgammaFloor)]
        have hmul := mul_le_mul_of_nonneg_left ih'.2.2.2 ha0
        nlinarith [hmul]
      have hind := And.intro hgammaLinear
        (And.intro hgammaFloor (And.intro hkappaNonneg hkappaHalf))
      convert hind using 1 <;> norm_num <;> ring_nf

theorem weightedDecoEta_lt_one {w a : ℝ} (hw0 : 0 ≤ w)
    {n : ℕ} (hn : 1 ≤ n) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    weightedDecoEta w n a < 1 := by
  have hgamma := (weightedDeco_endpoint_bounds hw0 ha0 ha1 n hn).1
  have hna : 0 ≤ (n : ℝ) * a := mul_nonneg (by positivity) ha0
  have hgammaPos : 0 < weightedDecoGamma w n a := by linarith
  rw [weightedDecoEta, div_lt_one hgammaPos]
  linarith

end RealRooted.Applications.OEIS
