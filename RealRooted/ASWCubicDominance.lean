import RealRooted.ASWCubicClosedFormAdapter
import RealRooted.ComplexCesaro

/-!
# Dominant roots for cubic ASW minors

This file rewrites the cubic partial-fraction closed form as three geometric
modes and applies the complex Cesaro lemma. It proves that nonnegative
shift-one Toeplitz minors force the nonnegative real characteristic root to
have modulus at least that of the nonreal conjugate pair. Applying the same
argument to the shift-two recurrence proves the reverse inequality.
-/

noncomputable section

namespace RealRooted

open Complex
open scoped ComplexConjugate

/-- Coefficient of the real geometric mode in the cubic partial fraction
expansion. -/
def aswCubicRealModeWeight (r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) ^ 2 / (((r : ℂ) - z) * ((r : ℂ) - conj z))

/-- Coefficient of the nonreal geometric mode in the cubic partial fraction
expansion. -/
def aswCubicComplexModeWeight (r : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 / ((z - (r : ℂ)) * (z - conj z))

lemma aswCubicComplexModeWeight_conj (r : ℝ) (z : ℂ) :
    conj (aswCubicComplexModeWeight r z) =
      (conj z) ^ 2 / ((conj z - (r : ℂ)) * (conj z - z)) := by
  simp [aswCubicComplexModeWeight, map_div₀, map_mul, map_sub, map_pow]

/-- The partial-fraction closed form is a sum of one real and one conjugate
pair of geometric modes. -/
theorem aswCubicClosedForm_eq_geometricModes (r : ℝ) (z : ℂ) (n : ℕ) :
    aswCubicClosedForm r z n =
      aswCubicRealModeWeight r z * (r : ℂ) ^ n +
        aswCubicComplexModeWeight r z * z ^ n +
          conj (aswCubicComplexModeWeight r z) * (conj z) ^ n := by
  rw [aswCubicComplexModeWeight_conj]
  simp only [aswCubicClosedForm, aswCubicRealModeWeight,
    aswCubicComplexModeWeight, pow_add]
  ring

lemma aswCubicComplexModeWeight_ne_zero (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    aswCubicComplexModeWeight r z ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero 2 (by
      intro h
      apply hz
      simp [h])
  · apply mul_ne_zero
    · exact sub_ne_zero.mpr (by
        intro h
        apply hz
        rw [h]
        simp)
    · exact sub_ne_zero.mpr (by
        intro h
        apply hz
        have him := congrArg Complex.im h
        simp only [conj_im] at him
        linarith)

/-- Nonnegative shift-one cubic Toeplitz minors force the nonreal
characteristic root to have modulus at most the nonnegative real root. -/
theorem norm_le_of_aswShiftedToeplitzMinor_one_nonneg
    (u : ℕ → ℝ) (hu : ∀ j, 4 ≤ j → u j = 0)
    (r : ℝ) {z : ℂ} (hr : 0 ≤ r) (hz : z.im ≠ 0)
    (hsum : (r : ℂ) + z + conj z = u 1)
    (hpairs : (r : ℂ) * z + (r : ℂ) * conj z + z * conj z = u 0 * u 2)
    (hprod : (r : ℂ) * z * conj z = u 0 ^ 2 * u 3)
    (hnonneg : ∀ n, 0 ≤ aswShiftedToeplitzMinor u 1 n) :
    ‖z‖ ≤ r := by
  apply norm_le_of_nonneg_conjugate_geometric hr hz
    (aswCubicComplexModeWeight_ne_zero r hz)
  · intro n
    rw [congrFun
      (aswShiftedToeplitzMinor_one_eq_closedForm u hu r hz hsum hpairs hprod) n]
    exact aswCubicClosedForm_eq_geometricModes r z n
  · exact hnonneg

/-- The nonnegative real root of the shift-two characteristic polynomial. -/
def aswCubicShiftTwoRealRoot (a : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq z / a

/-- One root from the nonreal conjugate pair of the shift-two characteristic
polynomial. -/
def aswCubicShiftTwoComplexRoot (a r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) * z / a

private lemma ofReal_aswCubicShiftTwoRealRoot (a : ℝ) (z : ℂ) :
    (aswCubicShiftTwoRealRoot a z : ℂ) = z * conj z / a := by
  rw [aswCubicShiftTwoRealRoot, Complex.ofReal_div, Complex.mul_conj]

private lemma conj_aswCubicShiftTwoComplexRoot (a r : ℝ) (z : ℂ) :
    conj (aswCubicShiftTwoComplexRoot a r z) = (r : ℂ) * conj z / a := by
  simp [aswCubicShiftTwoComplexRoot, map_div₀, map_mul]

private lemma im_aswCubicShiftTwoComplexRoot (a r : ℝ) (z : ℂ) (ha : a ≠ 0) :
    (aswCubicShiftTwoComplexRoot a r z).im = r * z.im / a := by
  simp [aswCubicShiftTwoComplexRoot, Complex.div_im, Complex.normSq_ofReal]
  field_simp [ha]

/-- The shift-two cubic Toeplitz minors equal the closed form for the scaled
pairwise-product roots. -/
theorem aswShiftedToeplitzMinor_two_eq_closedForm
    (u : ℕ → ℝ) (hu : ∀ j, 4 ≤ j → u j = 0)
    (a r : ℝ) {z : ℂ} (ha : 0 < a) (hr : 0 < r) (hz : z.im ≠ 0)
    (hsum : (r : ℂ) + z + conj z = u 1)
    (hpairs : (r : ℂ) * z + (r : ℂ) * conj z + z * conj z = a * u 2)
    (hprod : (r : ℂ) * z * conj z = a ^ 2 * u 3)
    (ha0 : u 0 = a) :
    (fun n ↦ (aswShiftedToeplitzMinor u 2 n : ℂ)) =
      aswCubicClosedForm (aswCubicShiftTwoRealRoot a z)
        (aswCubicShiftTwoComplexRoot a r z) := by
  have hroots := aswCubicShiftTwo_roots_from_shiftOne
    (a : ℂ) (u 1) (u 2) (u 3) (r : ℂ) z (conj z)
      hsum (by linear_combination hpairs) hprod (Complex.ofReal_ne_zero.mpr ha.ne')
  have hconj := conj_aswCubicShiftTwoComplexRoot a r z
  have hreal := ofReal_aswCubicShiftTwoRealRoot a z
  have hzim : (aswCubicShiftTwoComplexRoot a r z).im ≠ 0 := by
    rw [im_aswCubicShiftTwoComplexRoot a r z ha.ne']
    exact div_ne_zero (mul_ne_zero hr.ne' hz) ha.ne'
  apply eq_aswCubicClosedForm_of_recurrence _ _ hzim
  · simp
  · rw [aswShiftedToeplitzMinor_one]
    rw [hreal, hconj, aswCubicShiftTwoComplexRoot]
    linear_combination -hroots.1
  · rw [aswShiftedToeplitzMinor_two_two]
    push_cast
    rw [hreal, hconj, aswCubicShiftTwoComplexRoot]
    rw [← hroots.1, ← hroots.2.1]
    ring
  · intro n
    have hrec := congrArg (↑Complex.ofReal)
      (aswShiftedToeplitzMinor_two_cubic_rec u hu n)
    push_cast at hrec
    rw [hreal, hconj, aswCubicShiftTwoComplexRoot]
    have hs : z * conj z / a + (r : ℂ) * z / a + (r : ℂ) * conj z / a = u 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using hroots.1
    have hp :
        z * conj z / a * ((r : ℂ) * z / a) +
            z * conj z / a * ((r : ℂ) * conj z / a) +
              (r : ℂ) * z / a * ((r : ℂ) * conj z / a) = u 1 * u 3 := by
      simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hroots.2.1
    have hpr :
        z * conj z / a * ((r : ℂ) * z / a) * ((r : ℂ) * conj z / a) =
          a * (u 3 : ℂ) ^ 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hroots.2.2
    rw [hs, hp, hpr]
    rw [show (u 0 : ℂ) = a by exact_mod_cast ha0] at hrec
    exact hrec

/-- Nonnegative shift-two cubic Toeplitz minors force the real shift-one root
to have modulus at most that of the nonreal shift-one root. -/
theorem le_norm_of_aswShiftedToeplitzMinor_two_nonneg
    (u : ℕ → ℝ) (hu : ∀ j, 4 ≤ j → u j = 0)
    (a r : ℝ) {z : ℂ} (ha : 0 < a) (hr : 0 < r) (hz : z.im ≠ 0)
    (hsum : (r : ℂ) + z + conj z = u 1)
    (hpairs : (r : ℂ) * z + (r : ℂ) * conj z + z * conj z = a * u 2)
    (hprod : (r : ℂ) * z * conj z = a ^ 2 * u 3)
    (ha0 : u 0 = a)
    (hnonneg : ∀ n, 0 ≤ aswShiftedToeplitzMinor u 2 n) :
    r ≤ ‖z‖ := by
  have hzim : (aswCubicShiftTwoComplexRoot a r z).im ≠ 0 := by
    rw [im_aswCubicShiftTwoComplexRoot a r z ha.ne']
    exact div_ne_zero (mul_ne_zero hr.ne' hz) ha.ne'
  have hdominance := norm_le_of_nonneg_conjugate_geometric
    (r := aswCubicShiftTwoRealRoot a z)
    (A := aswCubicRealModeWeight (aswCubicShiftTwoRealRoot a z)
      (aswCubicShiftTwoComplexRoot a r z))
    (B := aswCubicComplexModeWeight (aswCubicShiftTwoRealRoot a z)
      (aswCubicShiftTwoComplexRoot a r z))
    (div_nonneg (Complex.normSq_nonneg z) ha.le) hzim
    (aswCubicComplexModeWeight_ne_zero _ hzim) (x := fun n ↦
      aswShiftedToeplitzMinor u 2 n) ?_ hnonneg
  · rw [aswCubicShiftTwoComplexRoot, norm_div, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le, Complex.norm_real,
      Real.norm_of_nonneg ha.le, aswCubicShiftTwoRealRoot,
      Complex.normSq_eq_norm_sq] at hdominance
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (by
      intro h
      apply hz
      simp [h])
    have hmul : r * ‖z‖ ≤ ‖z‖ ^ 2 :=
      (div_le_div_iff_of_pos_right ha).mp hdominance
    nlinarith
  · intro n
    rw [congrFun
      (aswShiftedToeplitzMinor_two_eq_closedForm u hu a r ha hr hz
        hsum hpairs hprod ha0) n]
    exact aswCubicClosedForm_eq_geometricModes _ _ n

end RealRooted
