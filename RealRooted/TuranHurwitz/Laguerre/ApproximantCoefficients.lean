module

public import RealRooted.TuranHurwitz.Laguerre.Reduction
public import RealRooted.TuranHurwitz.Laguerre.Approximant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Explicit coefficients of the Laguerre approximation

The normalized Laguerre coefficients separate the approximation index
from the fixed coefficient index.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Normalizing the constant term gives a binomial coefficient divided by a rising factorial. -/
theorem coeff_normalized_generalizedLaguerre {alpha : ℝ} (halpha : 0 < alpha)
    (k r : ℕ) :
    (C ((rising alpha k)⁻¹) * generalizedLaguerre k (alpha - 1)).coeff r =
      (k.choose r : ℝ) / rising alpha r := by
  rw [coeff_C_mul, coeff_generalizedLaguerre]
  by_cases hr : r ≤ k
  · rw [ite_eq_left hr]
    have hsplit := rising_add alpha r (k - r)
    rw [Nat.add_sub_of_le hr] at hsplit
    have hshift : alpha - 1 + (r : ℝ) + 1 = alpha + r := by ring
    rw [hshift]
    change (rising alpha k)⁻¹ *
      ((k.choose r : ℝ) * rising (alpha + r) (k - r)) = _
    field_simp [(rising_pos halpha k).ne', (rising_pos halpha r).ne']
    linear_combination -(k.choose r : ℝ) * hsplit
  · rw [ite_eq_right hr, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hr)]
    simp

/-- The normalized Laguerre row is its finite coefficient expansion. -/
theorem normalized_generalizedLaguerre_eq_sum {alpha : ℝ} (halpha : 0 < alpha)
    (k : ℕ) :
    C ((rising alpha k)⁻¹) * generalizedLaguerre k (alpha - 1) =
      ∑ r ∈ Finset.range (k + 1), C ((k.choose r : ℝ) / rising alpha r) * X ^ r := by
  have hdeg :
      (C ((rising alpha k)⁻¹) * generalizedLaguerre k (alpha - 1)).natDegree = k := by
    rw [natDegree_C_mul (inv_ne_zero (rising_pos halpha k).ne'),
      natDegree_generalizedLaguerre]
  simpa only [hdeg, coeff_normalized_generalizedLaguerre halpha] using
    (as_sum_range_C_mul_X_pow (C ((rising alpha k)⁻¹) *
      generalizedLaguerre k (alpha - 1)))

/-- The scalar-normalized Laguerre factor after complex scaling. -/
theorem coeff_scaled_normalizedLaguerre {alpha : ℝ} (halpha : 0 < alpha)
    (k r : ℕ) (y : ℂ) :
    (C (((rising alpha k)⁻¹ : ℝ) : ℂ) *
      ((generalizedLaguerre k (alpha - 1)).map Complex.ofRealHom).comp (C y * X)).coeff r =
      (((k.choose r : ℝ) / rising alpha r : ℝ) : ℂ) * y ^ r := by
  have hmap : C (((rising alpha k)⁻¹ : ℝ) : ℂ) *
        ((generalizedLaguerre k (alpha - 1)).map Complex.ofRealHom).comp (C y * X) =
      ((C ((rising alpha k)⁻¹) * generalizedLaguerre k (alpha - 1)).map
        Complex.ofRealHom).comp (C y * X) := by
    simp only [Polynomial.map_mul, Polynomial.map_C, mul_comp, C_comp]
    rfl
  rw [hmap, comp_C_mul_X_coeff, coeff_map, coeff_normalized_generalizedLaguerre halpha]
  rfl

/-- The binomial factor after complex scaling. -/
theorem coeff_scaled_binomial (a : ℂ) (k r : ℕ) :
    ((1 + C a * X) ^ k).coeff r = (k.choose r : ℂ) * a ^ r := by
  have heq : (1 + C a * X) ^ k = ((1 + X) ^ k).comp (C a * X) := by
    simp only [pow_comp, add_comp, one_comp, X_comp]
  rw [heq, comp_C_mul_X_coeff, coeff_one_add_X_pow]

/-- A Cauchy product gives every fixed coefficient of the complex approximant. -/
theorem coeff_laguerreApproxBase {alpha : ℝ} (halpha : 0 < alpha)
    (a b : ℝ) (k j : ℕ) (x : ℂ) :
    (laguerreApproxBase a b alpha k x).coeff j =
      ∑ r ∈ Finset.range (j + 1),
        ((k.choose (j - r) : ℂ) * (((a / k : ℝ) : ℂ) ^ (j - r))) *
          ((((k.choose r : ℝ) / rising alpha r : ℝ) : ℂ) *
            ((((b / k : ℝ) : ℂ) * x) ^ r)) := by
  rw [laguerreApproxBase, mul_comm, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro r _
  rw [coeff_scaled_normalizedLaguerre halpha, coeff_scaled_binomial, mul_comm]

/-- The fixed-index real polynomial extracted from the finite approximant. -/
@[expose] noncomputable def laguerreApproxFamily (c : LaguerreParameters) (k j : ℕ) : ℝ[X] :=
  C (rising (c.a₂ / c.a₁) j / rising (1 / c.sigma) j * (j.factorial : ℝ)) *
    ∑ r ∈ Finset.range (j + 1),
      C (((k.choose (j - r) : ℝ) * ((c.a₁ / c.sigma / k) ^ (j - r))) *
        ((k.choose r : ℝ) / rising (c.a₂ / c.a₁) r) *
          (c.b₂ / c.sigma / k) ^ r) * laguerreShift c ^ r

/-- Every fixed-index approximation has degree at most its index. -/
theorem natDegree_laguerreApproxFamily_le (c : LaguerreParameters) (k j : ℕ) :
    (laguerreApproxFamily c k j).natDegree ≤ j := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro r hr
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_pow, show (laguerreShift c).natDegree = 1 from natDegree_X_add_C _, mul_one]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)

/-- Integer shifts identify the Euler coefficient multiplier with the rising ratio. -/
theorem rising_integer_shift_ratio {beta : ℝ} (hbeta : 0 < beta) (N j : ℕ) :
    rising (beta + j) N / rising beta N = rising (beta + N) j / rising beta j := by
  have h₁ := rising_add beta j N
  have h₂ := rising_add beta N j
  rw [Nat.add_comm j N] at h₁
  field_simp [(rising_pos hbeta N).ne', (rising_pos hbeta j).ne']
  linear_combination h₂ - h₁

/-- The real approximating row evaluates to the normalized Euler coefficient. -/
theorem aeval_laguerreApproxFamily {c : LaguerreParameters} (hc : c.Admissible)
    {N : ℕ} (hN : c.a₂ / c.a₁ - 1 / c.sigma = (N : ℝ)) (k j : ℕ) (z : ℂ) :
    Polynomial.aeval z (laguerreApproxFamily c k j) =
      (j.factorial : ℂ) *
        (positiveEuler (1 / c.sigma) N
          (laguerreApproxBase (c.a₁ / c.sigma) (c.b₂ / c.sigma) (c.a₂ / c.a₁) k
            (z + (c.lam : ℂ)))).coeff j := by
  rw [coeff_positiveEuler (one_div_pos.mpr hc.sigma_pos),
    rising_integer_shift_ratio (one_div_pos.mpr hc.sigma_pos)]
  have hparam : 1 / c.sigma + (N : ℝ) = c.a₂ / c.a₁ := by linarith
  rw [hparam, coeff_laguerreApproxBase hc.ratio_pos]
  simp only [laguerreApproxFamily, map_mul, map_sum, Polynomial.aeval_C, map_pow,
    laguerreShift, map_add, Polynomial.aeval_X, Complex.coe_algebraMap]
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_pow]
  ring

end RealRooted.TuranHurwitz
