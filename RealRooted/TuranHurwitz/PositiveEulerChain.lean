module

public import RealRooted.TuranHurwitz.Laguerre.SectorCoefficients
public import RealRooted.TuranHurwitz.RisingConvolution
public import RealRooted.EulerOperator.Shift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normalized positive Euler chains

The integer parameter shift in part (ii) is implemented by a finite chain
of normalized shifted Euler operators.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The positive Euler factors, each normalized to fix the constant coefficient. -/
@[expose] noncomputable def positiveEuler (b : ℝ) : ℕ → ℂ[X] → ℂ[X]
  | 0, p => p
  | N + 1, p => C (((b + N)⁻¹ : ℝ) : ℂ) *
      RealRooted.eulerShift ((b + N : ℝ) : ℂ) (positiveEuler b N p)

/-- A normalized Euler chain multiplies the coefficient of index `j` by a rising ratio. -/
theorem coeff_positiveEuler {b : ℝ} (hb : 0 < b) (N j : ℕ) (p : ℂ[X]) :
    (positiveEuler b N p).coeff j =
      ((rising (b + j) N / rising b N : ℝ) : ℂ) * p.coeff j := by
  induction N with
  | zero => simp [positiveEuler]
  | succ N ih =>
      rw [positiveEuler, coeff_C_mul, RealRooted.coeff_eulerShift, ih,
        rising_succ, rising_succ]
      have hN := (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg N)).ne'
      have hr := (rising_pos hb N).ne'
      push_cast
      field_simp
      ring

/-- A normalized Euler chain fixes evaluation at zero. -/
theorem eval_zero_positiveEuler {b : ℝ} (hb : 0 < b) (N : ℕ) (p : ℂ[X]) :
    (positiveEuler b N p).eval 0 = p.eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_positiveEuler hb]
  simp [(rising_pos hb N).ne', coeff_zero_eq_eval_zero]

/-- A normalized positive Euler chain has the same degree as its nonzero input. -/
theorem natDegree_positiveEuler {b : ℝ} (hb : 0 < b) (N : ℕ) {p : ℂ[X]} (hp : p ≠ 0) :
    (positiveEuler b N p).natDegree = p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_positiveEuler hb, coeff_eq_zero_of_natDegree_lt hj, mul_zero]
  · rw [coeff_positiveEuler hb, coeff_natDegree]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (div_pos (rising_pos (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg _)) N)
        (rising_pos hb N)).ne') (leadingCoeff_ne_zero.mpr hp)

/-- A normalized positive Euler chain preserves the cone of roots and its nonzero constant. -/
theorem roots_positiveEuler {b : ℝ} (hb : 0 < b) (N : ℕ) {x : ℂ} {p : ℂ[X]}
    (hpzero : p.eval 0 ≠ 0) (hp : ∀ z ∈ p.roots, z ∈ twoRaySector x) :
    ∀ z ∈ (positiveEuler b N p).roots, z ∈ twoRaySector x := by
  induction N with
  | zero => exact hp
  | succ N ih =>
      have hN := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg N)
      have heval : (positiveEuler b N p).eval 0 ≠ 0 := by
        rwa [eval_zero_positiveEuler hb]
      intro z hz
      rw [positiveEuler, roots_C_mul _
        (Complex.ofReal_ne_zero.mpr (inv_ne_zero hN.ne'))] at hz
      apply eulerStep_roots_mem_convex (convex_twoRaySector x) (zero_mem_twoRaySector x)
        heval ih hN z
      simpa only [RealRooted.eulerShift, add_comm] using hz

/-- Derivatives of a normalized Euler image retain nonzero paired coefficients. -/
theorem paired_coeff_positiveEuler_derivative {b : ℝ} (hb : 0 < b) (N : ℕ)
    {x : ℂ} (hx : 0 < x.re) {p : ℂ[X]} (hpzero : p.eval 0 ≠ 0)
    (hp : ∀ z ∈ p.roots, z ∈ twoRaySector x) {m n : ℕ} (hmn : m + n ≤ p.natDegree) :
    let q := derivative^[m] (positiveEuler b N p)
    (q * q.comp (-X)).coeff (2 * n) ≠ 0 := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hpzero
  let f := positiveEuler b N p
  have hfdegree : f.natDegree = p.natDegree := natDegree_positiveEuler hb N hpne
  have hfzero : f.eval 0 ≠ 0 := by rwa [eval_zero_positiveEuler hb]
  have hfne : f ≠ 0 := by intro h; simp [h] at hfzero
  let S := twoRaySector x ∩ {z : ℂ | z.re < 0}
  have hS : Convex ℝ S := (convex_twoRaySector x).inter
    ((convex_Iio (0 : ℝ)).linear_preimage Complex.reLm)
  have hfroots : ∀ z ∈ f.roots, z ∈ S := by
    intro z hz
    have hcone := roots_positiveEuler hb N hpzero hp z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hev : f.eval z = 0 := (mem_roots hfne).mp hz
      exact hfzero (by simpa only [h] using hev)
    exact ⟨hcone, twoRaySector_re_neg hx hcone hz0⟩
  have hm : m ≤ f.natDegree := by rw [hfdegree]; lia
  have hconst : (derivative^[m] f).eval 0 ≠ 0 := by
    have h := coeff_ne_zero_of_roots_mem_convex hS (by simp [S]) hfne hfroots hm
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, Nat.zero_add, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_pos.mpr le_rfl).ne') h
  apply paired_coeff_ne_zero_of_twoRaySector hx hconst
  · intro z hz
    exact (iterate_derivative_roots_mem_convex hS hfroots m z hz).1
  · rw [natDegree_iterate_derivative_eq, hfdegree]
    lia

end RealRooted.TuranHurwitz
