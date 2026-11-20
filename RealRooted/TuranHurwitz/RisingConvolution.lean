module

public import RealRooted.TuranHurwitz.Recurrence
public import RealRooted.TuranHurwitz.BinomialComposition
import RealRooted.TuranHurwitz.FormalParity
public import Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
public import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The rising-factorial convolution at the normalization pole

The binomial product at opposite formal times reduces to a series in `t²`.
Comparing coefficients gives the alternating convolution for every index.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The real rising factorial `(d)_j`, using Mathlib's ascending Pochhammer polynomial. -/
@[expose] noncomputable def rising (d : ℝ) (j : ℕ) : ℝ := (ascPochhammer ℝ j).eval d

/-- The zeroth rising factorial. -/
@[simp] theorem rising_zero (d : ℝ) : rising d 0 = 1 := by simp [rising]

/-- The recurrence for real rising factorials. -/
theorem rising_succ (d : ℝ) (j : ℕ) : rising d (j + 1) = rising d j * (d + j) := by
  exact ascPochhammer_succ_eval j d

/-- Splitting a rising factorial at an arbitrary index. -/
theorem rising_add (d : ℝ) (m j : ℕ) :
    rising d (m + j) = rising d m * rising (d + m) j := by
  have h := congrArg (Polynomial.eval d) (ascPochhammer_mul (S := ℝ) m j)
  simpa only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, rising] using h.symm

/-- Rising factorials are strictly positive for positive starting value. -/
theorem rising_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < rising d j :=
  ascPochhammer_pos j d hd

/-- The normalized negative-binomial series `(1-t)^(-d)`. -/
@[expose] noncomputable def risingSeries (d : ℝ) : PowerSeries ℝ :=
  (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.X)

/-- The normalized rising series has initial value one. -/
@[simp] theorem constantCoeff_risingSeries (d : ℝ) :
    PowerSeries.constantCoeff (risingSeries d) = 1 := by
  exact constantCoeff_binomial_subst _ _ (by simp)

/-- Its formal Euler equation gives the rising-factorial coefficient recurrence. -/
theorem risingSeries_euler (d : ℝ) :
    (1 - PowerSeries.X) * PowerSeries.derivative (risingSeries d) =
      PowerSeries.C d * risingSeries d := by
  have h := binomial_subst_euler (-d) (-PowerSeries.X : PowerSeries ℝ) (by simp)
  simp only [map_neg, PowerSeries.derivative_X, neg_mul, mul_neg, neg_neg,
    Algebra.algebraMap_self, RingHom.id_apply, mul_one, ← sub_eq_add_neg] at h
  exact h

/-- The formal coefficient recurrence for the rising series. -/
theorem coeff_risingSeries_step (d : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * PowerSeries.coeff (k + 1) (risingSeries d) =
      (d + k) * PowerSeries.coeff k (risingSeries d) := by
  have h := congrArg (PowerSeries.coeff k) (risingSeries_euler d)
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_derivative,
    PowerSeries.coeff_X_mul_derivative, PowerSeries.coeff_C_mul] at h
  linear_combination h

/-- The factorially normalized coefficients are the real rising factorials. -/
theorem factorial_mul_coeff_risingSeries (d : ℝ) (k : ℕ) :
    (k.factorial : ℝ) * PowerSeries.coeff k (risingSeries d) = rising d k := by
  induction k with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k ih =>
      have h := coeff_risingSeries_step d k
      rw [rising_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      linear_combination (k.factorial : ℝ) * h + (d + k) * ih

/-- The coefficient formula for the normalized rising series. -/
theorem coeff_risingSeries (d : ℝ) (k : ℕ) :
    PowerSeries.coeff k (risingSeries d) = rising d k / (k.factorial : ℝ) := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply (eq_div_iff hfac).mpr
  rw [mul_comm]
  exact factorial_mul_coeff_risingSeries d k

/-- Opposite formal times turn the product of negative-binomial series into a square expansion. -/
theorem risingSeries_pair (d : ℝ) :
    risingSeries d * PowerSeries.rescale (-1) (risingSeries d) =
      PowerSeries.expand 2 (by decide) (risingSeries d) := by
  have hX : PowerSeries.HasSubst (-PowerSeries.X : PowerSeries ℝ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hp := binomial_subst_mul (-d) (-PowerSeries.X : PowerSeries ℝ) PowerSeries.X
    (by simp) (by simp)
  rw [show (-PowerSeries.X : PowerSeries ℝ) + PowerSeries.X +
    (-PowerSeries.X) * PowerSeries.X = -(PowerSeries.X ^ 2) by ring] at hp
  rw [risingSeries, rescale_subst_scalar _ _ _ hX]
  simp only [map_neg, PowerSeries.rescale_X, map_neg, map_one, neg_one_mul, neg_neg]
  rw [hp, PowerSeries.expand_apply,
    PowerSeries.subst_comp_subst_apply hX
      (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp))]
  have hsq : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries ℝ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hneg : (-PowerSeries.X : PowerSeries ℝ).subst (PowerSeries.X ^ 2) =
      -((PowerSeries.X : PowerSeries ℝ) ^ 2) := by
    rw [← PowerSeries.coe_substAlgHom hsq, map_neg, PowerSeries.substAlgHom_X]
  rw [hneg]

/-- The exact alternating rising-factorial convolution at every even index. -/
theorem alternating_rising_convolution (d : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1),
      (-1 : ℝ) ^ j * (rising d j / (j.factorial : ℝ)) *
        (rising d (2 * n - j) / ((2 * n - j).factorial : ℝ))) =
      rising d n / (n.factorial : ℝ) := by
  have h := congrArg (PowerSeries.coeff (2 * n)) (risingSeries_pair d)
  rw [mul_comm (risingSeries d), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_expand_mul] at h
  simpa only [PowerSeries.coeff_rescale, coeff_risingSeries] using h

/-- The constant-polynomial sequence of rising factorials. -/
@[expose] noncomputable def risingFamily (d : ℝ) (j : ℕ) : ℝ[X] := C (rising d j)

/-- The extended Turán expression of rising factorials has the closed convolution value. -/
theorem turan_risingFamily (d : ℝ) (m n : ℕ) :
    turan m n (risingFamily d) =
      C ((-1 : ℝ) ^ n * rising d m ^ 2 * (rising (d + m) n / (n.factorial : ℝ))) := by
  rw [turan]
  simp only [risingFamily, ← map_mul, ← map_sum]
  congr 1
  calc
    _ = ((-1 : ℝ) ^ n * rising d m ^ 2) *
        ∑ j ∈ Finset.range (2 * n + 1),
          (-1 : ℝ) ^ j * (rising (d + m) j / (j.factorial : ℝ)) *
            (rising (d + m) (2 * n - j) / ((2 * n - j).factorial : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ 2 * n := by simpa using Finset.mem_range.mp hj
      rw [show m + 2 * n - j = m + (2 * n - j) by lia, rising_add, rising_add,
        pow_add]
      ring
    _ = _ := by rw [alternating_rising_convolution]

/-- Any sequence with geometrically scaled rising values has nonzero Turán values. -/
theorem aeval_turan_ne_zero_of_rising_values (P : ℕ → ℝ[X]) (z s : ℂ) {d : ℝ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hP : ∀ j, Polynomial.aeval z (P j) = s ^ j * (rising d j : ℂ)) (m n : ℕ) :
    Polynomial.aeval z (turan m n P) ≠ 0 := by
  have hv : ∀ j, Polynomial.aeval z (P j) = s ^ j *
      Polynomial.aeval (0 : ℂ) (risingFamily d j) := by
    intro j
    simpa [risingFamily] using hP j
  rw [aeval_turan_scaling P (risingFamily d) z 0 s hv, turan_risingFamily]
  apply mul_ne_zero (pow_ne_zero _ hs)
  rw [Polynomial.aeval_C]
  apply (map_ne_zero (algebraMap ℝ ℂ)).mpr
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero 2 (rising_pos hd m).ne'))
    (div_ne_zero (rising_pos (add_pos_of_pos_of_nonneg hd (Nat.cast_nonneg m)) n).ne'
      (by exact_mod_cast Nat.factorial_ne_zero n))

end RealRooted.TuranHurwitz
