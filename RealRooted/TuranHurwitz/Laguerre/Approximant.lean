module

public import RealRooted.TuranHurwitz.PositiveEulerChain
public import RealRooted.Laguerre.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The polynomial Laguerre approximants

We keep the shifted complex parameter separate from the positive real
scales. The root argument then applies to every admissible part (ii) family.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The finite product approximating the exponential times the Laguerre generating series. -/
@[expose] noncomputable def laguerreApproxBase (a b alpha : ℝ) (k : ℕ) (x : ℂ) : ℂ[X] :=
  (1 + C ((a / k : ℝ) : ℂ) * X) ^ k *
    (C (((rising alpha k)⁻¹ : ℝ) : ℂ) *
      ((generalizedLaguerre k (alpha - 1)).map Complex.ofRealHom).comp
        (C (((b / k : ℝ) : ℂ) * x) * X))

/-- The approximant has constant coefficient one. -/
theorem eval_zero_laguerreApproxBase {alpha : ℝ} (halpha : 0 < alpha)
    (a b : ℝ) (k : ℕ) (x : ℂ) : (laguerreApproxBase a b alpha k x).eval 0 = 1 := by
  simp only [laguerreApproxBase, eval_mul, eval_pow, eval_add, eval_one, eval_C,
    eval_X, mul_zero, add_zero, one_pow, eval_comp, eval_map]
  rw [eval₂_at_zero, coeff_zero_eq_eval_zero, generalizedLaguerre_eval_zero,
    sub_add_cancel, one_mul]
  change (↑(rising alpha k)⁻¹ : ℂ) * ↑(rising alpha k) = 1
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (rising_pos halpha k).ne', Complex.ofReal_one]

/-- The approximant has degree twice the approximation index. -/
theorem natDegree_laguerreApproxBase {a b alpha : ℝ} (ha : 0 < a) (hb : 0 < b)
    (halpha : 0 < alpha) {k : ℕ} (hk : 0 < k) {x : ℂ} (hx : x ≠ 0) :
    (laguerreApproxBase a b alpha k x).natDegree = 2 * k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha0 : ((a / k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_pos ha hkR).ne'
  have hb0 : ((b / k : ℝ) : ℂ) * x ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hb hkR).ne') hx
  have hfirst : (1 + C ((a / k : ℝ) : ℂ) * X).natDegree = 1 := by
    simpa only [C_1, add_comm] using natDegree_linear (b := (1 : ℂ)) ha0
  have hsecond :
      (((generalizedLaguerre k (alpha - 1)).map Complex.ofRealHom).comp
        (C (((b / k : ℝ) : ℂ) * x) * X)).natDegree = k := by
    rw [natDegree_comp, natDegree_map, natDegree_generalizedLaguerre,
      natDegree_C_mul_X _ hb0, mul_one]
  rw [laguerreApproxBase, natDegree_mul, natDegree_pow, hfirst,
    natDegree_C_mul (Complex.ofReal_ne_zero.mpr (inv_ne_zero (rising_pos halpha k).ne')),
    hsecond]
  · lia
  · apply pow_ne_zero
    intro h
    have hd := congrArg natDegree h
    rw [hfirst, natDegree_zero] at hd
    exact Nat.one_ne_zero hd
  · exact mul_ne_zero (C_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (inv_ne_zero (rising_pos halpha k).ne')))
      (by intro h; have hd := congrArg natDegree h; rw [hsecond, natDegree_zero] at hd; lia)

/-- Every root lies on one of the two generating rays of the cone. -/
theorem roots_laguerreApproxBase {a b alpha : ℝ} (ha : 0 < a) (hb : 0 < b)
    (halpha : 0 < alpha) {k : ℕ} (hk : 0 < k) {x : ℂ} (hx : 0 < x.re) :
    ∀ z ∈ (laguerreApproxBase a b alpha k x).roots, z ∈ twoRaySector x := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  intro z hz
  have hev : (laguerreApproxBase a b alpha k x).eval z = 0 :=
    (Polynomial.mem_roots'.mp hz).2
  simp only [laguerreApproxBase, eval_mul, eval_pow, eval_add, eval_one, eval_C,
    eval_X, eval_comp] at hev
  rcases mul_eq_zero.mp hev with hfirst | hsecond
  · have heq : 1 + ((a / k : ℝ) : ℂ) * z = 0 := eq_zero_of_pow_eq_zero hfirst
    refine ⟨(k : ℝ) / a, 0, (div_pos hkR ha).le, le_rfl, ?_⟩
    simp only [Complex.ofReal_div, Complex.ofReal_zero, zero_div, add_zero]
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast at heq
    field_simp at heq ⊢
    linear_combination heq
  · have hL :
        ((generalizedLaguerre k (alpha - 1)).map Complex.ofRealHom).eval
          ((((b / k : ℝ) : ℂ) * x) * z) = 0 := by
      exact (mul_eq_zero.mp hsecond).resolve_left
        (Complex.ofReal_ne_zero.mpr (inv_ne_zero (rising_pos halpha k).ne'))
    have hroot : (((b / k : ℝ) : ℂ) * x) * z ∈
        ((generalizedLaguerre k (alpha - 1)).map Complex.ofRealHom).roots :=
      (mem_roots ((monic_generalizedLaguerre k (alpha - 1)).map _).ne_zero).mpr hL
    have hsplit := RealRooted.generalizedLaguerre_splits k (by linarith : -1 ≤ alpha - 1)
    rw [hsplit.roots_map_of_injective Complex.ofReal_injective] at hroot
    obtain ⟨r, hr, heq⟩ := Multiset.mem_map.mp hroot
    change (r : ℂ) = _ at heq
    have hrneg := RealRooted.generalizedLaguerre_roots_neg k (by linarith) r hr
    refine ⟨0, -r * (k : ℝ) / b, le_refl _,
      (div_nonneg (mul_nonneg (neg_nonneg.mpr hrneg.le) hkR.le) hb.le), ?_⟩
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Complex.ofReal_zero, zero_add]
    push_cast at heq ⊢
    field_simp at heq ⊢
    linear_combination -heq

/-- Euler-normalized Laguerre approximants have all the paired derivative coefficients needed. -/
theorem paired_coeff_laguerreApproxBase {a b alpha beta : ℝ} (ha : 0 < a) (hb : 0 < b)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (N : ℕ) {k : ℕ} (hk : 0 < k)
    {x : ℂ} (hx : 0 < x.re) {m n : ℕ} (hmn : m + n ≤ 2 * k) :
    let q := derivative^[m] (positiveEuler beta N (laguerreApproxBase a b alpha k x))
    (q * q.comp (-X)).coeff (2 * n) ≠ 0 := by
  apply paired_coeff_positiveEuler_derivative hbeta N hx
  · rw [eval_zero_laguerreApproxBase halpha]
    exact one_ne_zero
  · exact roots_laguerreApproxBase ha hb halpha hk hx
  · rwa [natDegree_laguerreApproxBase ha hb halpha hk
      (by intro h; simp [h] at hx)]

end RealRooted.TuranHurwitz
