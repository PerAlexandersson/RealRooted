module

public import RealRooted.Basic.Coefficients
public import RealRooted.PFPolynomial
public import RealRooted.SimpleRoots
public import Mathlib.RingTheory.Polynomial.Chebyshev

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import RealRooted.CubicDiscriminant
import RealRooted.Interlacing.OuterDifference
import RealRooted.Linear
import RealRooted.MaWang.CriticalSign
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.Mathlib.RingTheory.Polynomial.Chebyshev.Bounds
import RealRooted.PosCombo
import RealRooted.RootCountJump
import RealRooted.SameDegreeDerivative
import RealRooted.WagnerRightSum.Sign

/-!
# Critical values and Chebyshev level polynomials

This file gives an exact critical-value criterion for constant shifts and applies it to
Chebyshev polynomials of the first kind.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- Subtracting a constant preserves the positive leading coefficient of a polynomial of
positive degree. -/
private lemma hasPosLeadingCoeff_sub_C {f : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hdeg : f.natDegree ≠ 0) (s : ℝ) :
    HasPosLeadingCoeff (f - C s) := by
  unfold HasPosLeadingCoeff at hf ⊢
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C, Polynomial.coeff_sub]
  simpa [Polynomial.coeff_C, hdeg] using hf

/-- If two constant levels of a positive-leading nonconstant polynomial are real-rooted,
then every intermediate level is interlaced by the common derivative. -/
theorem derivative_interlaces_sub_C_of_mem_Icc {f : ℝ[X]} {a b s : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : f.natDegree ≠ 0)
    (hab : a ≤ b) (hs : s ∈ Icc a b)
    (ha_splits : (f - C a).Splits) (hb_splits : (f - C b).Splits) :
    Interlaces f.derivative (f - C s) := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · have hs_eq : s = a := by grind
    subst s
    simpa only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] using
      derivative_interlaces_of_natDegree_ne_zero ha_splits (by simpa)
  let β : ℝ := (s - a) / (b - a)
  have hβ0 : 0 ≤ β := div_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hab)
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    exact (div_le_one (sub_pos.mpr hab_lt)).mpr (by linarith [hs.2])
  have ha_pos : HasPosLeadingCoeff (f - C a) := hasPosLeadingCoeff_sub_C hf_pos hdeg a
  have hb_pos : HasPosLeadingCoeff (f - C b) := hasPosLeadingCoeff_sub_C hf_pos hdeg b
  have ha_inter : StrictInterl f.derivative (f - C a) := by
    simpa only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] using
      (derivative_interlaces_of_natDegree_ne_zero ha_splits (by simpa)).toStrictInterl
  have hb_inter : StrictInterl f.derivative (f - C b) := by
    simpa only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] using
      (derivative_interlaces_of_natDegree_ne_zero hb_splits (by simpa)).toStrictInterl
  have hcombo : PosComboRealRooted (f - C a) (f - C b) :=
    PosComboRealRooted.of_commonLeftInterleaver ha_inter hb_inter ha_pos hb_pos
  have hsegment := hcombo.isRealRooted_closed_segment ha_pos.ne_zero ha_splits
    hb_pos.ne_zero hb_splits hβ0 hβ1
  have hbary : (1 - β) * a + β * b = s := by
    dsimp [β]
    field_simp
    ring
  have hlevel : C (1 - β) * (f - C a) + C β * (f - C b) = f - C s := by
    calc
      C (1 - β) * (f - C a) + C β * (f - C b) =
          C ((1 - β) + β) * f - C ((1 - β) * a + β * b) := by
            simp only [map_add, map_sub, map_mul, map_one]
            ring
      _ = f - C s := by rw [hbary]; simp
  have hinter := derivative_interlaces_of_natDegree_ne_zero hsegment.2 (by
    rw [hlevel, Polynomial.natDegree_sub_C]
    exact hdeg)
  simpa only [hlevel, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] using hinter

/-- If two constant levels of a nonconstant real polynomial split, then every intermediate
constant level splits. -/
theorem splits_sub_C_of_mem_Icc {f : ℝ[X]} {a b s : ℝ} (hdeg : f.natDegree ≠ 0)
    (hs : s ∈ Icc a b) (ha_splits : (f - C a).Splits) (hb_splits : (f - C b).Splits) :
    (f - C s).Splits := by
  have hf0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt
    (Nat.pos_of_ne_zero hdeg))
  rcases hf0.lt_or_gt with hneg | hpos
  · have hf_pos : HasPosLeadingCoeff (-f) := by
      simpa [HasPosLeadingCoeff, leadingCoeff_neg] using hneg
    have hs' : -s ∈ Icc (-b) (-a) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hlevel : ∀ t : ℝ, -f - C (-t) = -(f - C t) := fun t ↦ by rw [map_neg]; ring
    have h := (derivative_interlaces_sub_C_of_mem_Icc hf_pos (by simpa using hdeg)
      (by linarith [hs.1, hs.2]) hs' (by rw [hlevel]; exact hb_splits.neg)
      (by rw [hlevel]; exact ha_splits.neg)).1.2
    rw [hlevel] at h
    exact splits_neg_iff.mp h
  · exact (derivative_interlaces_sub_C_of_mem_Icc hpos hdeg (hs.1.trans hs.2) hs ha_splits
      hb_splits).1.2

/-- If two split constant levels have all roots in a closed interval, then every
intermediate level has all roots in the same interval. -/
theorem roots_sub_C_mem_Icc_of_endpoint_roots_mem_Icc {f : ℝ[X]} {a b s L U : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : f.natDegree ≠ 0)
    (hs : s ∈ Icc a b) (ha_splits : (f - C a).Splits)
    (hb_splits : (f - C b).Splits)
    (ha_roots : ∀ r ∈ (f - C a).roots, r ∈ Icc L U)
    (hb_roots : ∀ r ∈ (f - C b).roots, r ∈ Icc L U) :
    ∀ r ∈ (f - C s).roots, r ∈ Icc L U := by
  have ha_pos : HasPosLeadingCoeff (f - C a) := hasPosLeadingCoeff_sub_C hf_pos hdeg a
  have hb_pos : HasPosLeadingCoeff (f - C b) := hasPosLeadingCoeff_sub_C hf_pos hdeg b
  intro r hr
  have hs_pos : HasPosLeadingCoeff (f - C s) := hasPosLeadingCoeff_sub_C hf_pos hdeg s
  have hroot : f.eval r = s := by
    have hroot0 := (Polynomial.mem_roots hs_pos.ne_zero).mp hr
    have : f.eval r - s = 0 := by simpa [Polynomial.IsRoot.def] using hroot0
    exact sub_eq_zero.mp this
  have ha_eval : (f - C a).eval r = s - a := by simp [hroot]
  have hb_eval : (f - C b).eval r = s - b := by simp [hroot]
  constructor
  · by_contra hL
    have hrL : r < L := lt_of_not_ge hL
    have hroot_gt_a : ∀ t ∈ (f - C a).roots, r < t := fun t ht ↦
      lt_of_lt_of_le hrL (ha_roots t ht).1
    have hroot_gt_b : ∀ t ∈ (f - C b).roots, r < t := fun t ht ↦
      lt_of_lt_of_le hrL (hb_roots t ht).1
    rcases f.natDegree.even_or_odd with heven | hodd
    · have heven_a : Even (f - C a).natDegree := by
        simpa only [Polynomial.natDegree_sub_C] using heven
      have heven_b : Even (f - C b).natDegree := by
        simpa only [Polynomial.natDegree_sub_C] using heven
      have ha_eval_pos := eval_pos_of_all_roots_gt_of_even
        ha_pos.ne_zero ha_pos heven_a hroot_gt_a
      have hb_eval_pos := eval_pos_of_all_roots_gt_of_even
        hb_pos.ne_zero hb_pos heven_b hroot_gt_b
      rw [ha_eval] at ha_eval_pos
      rw [hb_eval] at hb_eval_pos
      nlinarith [hs.1, hs.2]
    · have hodd_a : Odd (f - C a).natDegree := by
        simpa only [Polynomial.natDegree_sub_C] using hodd
      have hodd_b : Odd (f - C b).natDegree := by
        simpa only [Polynomial.natDegree_sub_C] using hodd
      have ha_eval_neg := eval_neg_of_all_roots_gt_of_odd
        ha_pos.ne_zero ha_pos hodd_a hroot_gt_a
      have hb_eval_neg := eval_neg_of_all_roots_gt_of_odd
        hb_pos.ne_zero hb_pos hodd_b hroot_gt_b
      rw [ha_eval] at ha_eval_neg
      rw [hb_eval] at hb_eval_neg
      nlinarith [hs.1, hs.2]
  · by_contra hU
    have hUr : U < r := lt_of_not_ge hU
    have ha_eval_pos := eval_pos_of_all_roots_lt ha_pos.ne_zero ha_splits ha_pos
      (fun t ht ↦ lt_of_le_of_lt (ha_roots t ht).2 hUr)
    have hb_eval_pos := eval_pos_of_all_roots_lt hb_pos.ne_zero hb_splits hb_pos
      (fun t ht ↦ lt_of_le_of_lt (hb_roots t ht).2 hUr)
    rw [ha_eval] at ha_eval_pos
    rw [hb_eval] at hb_eval_pos
    nlinarith [hs.1, hs.2]

/-- A constant level of a polynomial with simple real critical points is real-rooted exactly
when its value has the opposite weak sign from the second derivative at every critical point. -/
theorem splits_sub_C_iff_eval_secondDerivative_nonpos {f : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : 2 ≤ f.natDegree)
    (hder_splits : f.derivative.Splits) (hder_nodup : f.derivative.roots.Nodup)
    (s : ℝ) :
    (f - C s).Splits ↔
      ∀ r, f.derivative.IsRoot r →
        f.derivative.derivative.eval r * (f.eval r - s) ≤ 0 := by
  have hder_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  have hlevel_pos : HasPosLeadingCoeff (f - C s) :=
    hasPosLeadingCoeff_sub_C hf_pos (by lia) s
  have hder_degree : f.derivative.natDegree = f.natDegree - 1 :=
    f.natDegree_derivative
  constructor
  · intro hlevel_splits r hr
    have hinter0 :=
      (derivative_interlaces_of_natDegree_ne_zero hlevel_splits (by
        rw [Polynomial.natDegree_sub_C]
        lia)).toStrictInterl
    have hinter : StrictInterl f.derivative (f - C s) := by
      simpa only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] using hinter0
    have hsign := hinter.eval_mul_derivative_nonpos_of_left_root hder_pos hlevel_pos hr
    simpa [Polynomial.eval_sub, mul_comm] using hsign
  · intro hsign
    have hinter : StrictInterl f.derivative (f - C s) :=
      strictInterl_of_eval_mul_derivative_nonpos hder_pos hder_splits hder_nodup
        hlevel_pos (by rw [Polynomial.natDegree_sub_C, hder_degree]; lia)
        (by rw [Polynomial.natDegree_sub_C, hder_degree]; lia) fun r hr ↦ by
          simpa [Polynomial.eval_sub, mul_comm] using hsign r hr
    exact hinter.2.1.2

/-- Strict critical-value signs make the corresponding constant level split with simple roots. -/
theorem splits_and_hasSimpleRoots_sub_C_of_eval_secondDerivative_neg {f : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : 2 ≤ f.natDegree)
    (hder_splits : f.derivative.Splits) (s : ℝ)
    (hsign : ∀ r, f.derivative.IsRoot r →
      f.derivative.derivative.eval r * (f.eval r - s) < 0) :
    (f - C s).Splits ∧ HasSimpleRoots (f - C s) := by
  have hder_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  have hlevel_pos : HasPosLeadingCoeff (f - C s) :=
    hasPosLeadingCoeff_sub_C hf_pos (by lia) s
  have hder_degree : f.derivative.natDegree = f.natDegree - 1 :=
    f.natDegree_derivative
  have hpackage := strictInterl_package_of_eval_mul_derivative_neg_succ
    hder_splits hder_pos hlevel_pos hder_degree (by
      rw [Polynomial.natDegree_sub_C]
      lia) fun r hr ↦ by
      simpa [Polynomial.eval_sub, mul_comm] using hsign r hr
  exact ⟨hpackage.2.2.1, hpackage.2.2.2.2.1⟩

namespace Chebyshev

open Polynomial.Chebyshev

/-- The affine Chebyshev level family
`α (Tₙ(1 + λ X) - h)`, packaged as a polynomial sequence. -/
def affineLevel (α lam h : ℝ) (n : ℕ) : ℝ[X] :=
  C α * ((T ℝ n - C h).comp (1 + C lam * X))

/-- The affine Chebyshev level family satisfies its order-three recurrence. -/
theorem affineLevel_add_three (α lam h : ℝ) (n : ℕ) :
    affineLevel α lam h (n + 3) =
      (C 3 + C (2 * lam) * X) * affineLevel α lam h (n + 2) -
        (C 3 + C (2 * lam) * X) * affineLevel α lam h (n + 1) +
          affineLevel α lam h n := by
  have hn3 : ((n + 3 : ℕ) : ℤ) = (n : ℤ) + 1 + 2 := by
    norm_num
    ring
  have hn2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by
    norm_num
  have hn1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
    norm_num
  have hn2' : (n : ℤ) + 1 + 1 = ((n + 2 : ℕ) : ℤ) := by
    rw [hn2]
    ring
  have hrec2 : T ℝ (n + 2 : ℕ) = 2 * X * T ℝ (n + 1 : ℕ) - T ℝ n := by
    rw [hn2, T_add_two, hn1]
  have hrec3 : T ℝ (n + 3 : ℕ) =
      2 * X * T ℝ (n + 2 : ℕ) - T ℝ (n + 1 : ℕ) := by
    rw [hn3, T_add_two, hn2', hn1]
  unfold affineLevel
  rw [hrec3, hrec2]
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp, Polynomial.ofNat_comp, map_mul]
  rw [map_ofNat Polynomial.C 2, map_ofNat Polynomial.C 3]
  ring

/-- The second-kind Chebyshev polynomial over `ℝ` splits. -/
private lemma U_splits (n : ℕ) : (U ℝ n).Splits := by
  rw [Polynomial.splits_iff_card_roots, roots_U_real,
    Finset.card_val, Finset.card_image_of_injOn, Finset.card_range,
    natDegree_U_natCast]
  exact (Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)

/-- The second-kind Chebyshev polynomial over `ℝ` has no repeated roots. -/
private lemma U_roots_nodup (n : ℕ) : (U ℝ n).roots.Nodup := by
  rw [roots_U_real]
  exact Finset.nodup _

/-- The derivative of a positive-index first-kind Chebyshev polynomial is its usual
positive scalar multiple of a second-kind Chebyshev polynomial. -/
private lemma derivative_T_eq_C_mul_U {n : ℕ} (hn : n ≠ 0) :
    (T ℝ n).derivative = C (n : ℝ) * U ℝ ((n - 1 : ℕ) : ℤ) := by
  rw [T_derivative_eq_U]
  rw [Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr hn)]
  simp

/-- Critical points of a positive-degree first-kind Chebyshev polynomial lie in `(-1, 1)`. -/
private lemma derivative_T_roots_mem_Ioo {n : ℕ} (hn : n ≠ 0) :
    ∀ r ∈ (T ℝ n).derivative.roots, r ∈ Ioo (-1 : ℝ) 1 := by
  intro r hr
  rw [derivative_T_eq_C_mul_U hn, Polynomial.roots_C_mul _ (by positivity),
    roots_U_real, Finset.mem_val] at hr
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
  have hk_lt : k < n - 1 := Finset.mem_range.mp hk
  have hn_den : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
  rw [hn_den]
  have hn_cast : (0 : ℝ) < n := by positivity
  have hangle_pos : 0 < (k + 1 : ℝ) * Real.pi / n := by positivity
  have hangle_lt : (k + 1 : ℝ) * Real.pi / n < Real.pi := by
    calc
      (k + 1 : ℝ) * Real.pi / n < n * Real.pi / n := by
        gcongr
        exact_mod_cast (by lia : k + 1 < n)
      _ = Real.pi := by field_simp
  constructor
  · simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (le_of_lt hangle_pos) (le_refl Real.pi) hangle_lt
  · simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (le_refl 0) (le_of_lt hangle_lt) hangle_pos

/-- The derivative of `Tₙ` splits and has distinct roots for `n ≥ 2`. -/
private lemma derivative_T_splits_and_nodup {n : ℕ} (hn : 2 ≤ n) :
    (T ℝ n).derivative.Splits ∧ (T ℝ n).derivative.roots.Nodup := by
  have hn0 : n ≠ 0 := by lia
  rw [derivative_T_eq_C_mul_U hn0]
  exact ⟨(U_splits (n - 1)).C_mul _, by
    rw [Polynomial.roots_C_mul _ (by positivity)]
    exact U_roots_nodup (n - 1)⟩

/-- Positive rescaling of the variable preserves a positive leading coefficient. -/
private lemma hasPosLeadingCoeff_comp_C_mul_X {p : ℝ[X]} {a : ℝ}
    (hp : HasPosLeadingCoeff p) (ha : 0 < a) :
    HasPosLeadingCoeff (p.comp (C a * X)) := by
  unfold HasPosLeadingCoeff at hp ⊢
  rw [Polynomial.leadingCoeff_comp (by simp [ha.ne']),
    Polynomial.leadingCoeff_C_mul_X]
  exact mul_pos hp (pow_pos ha _)

/-- At every critical point of `Tₙ`, a level `h ∈ [-1, 1]` has the weak sign required
by the critical-value criterion. -/
private lemma eval_secondDerivative_mul_sub_nonpos {n : ℕ} (hn : 2 ≤ n)
    {h r : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) (hr : (T ℝ n).derivative.IsRoot r) :
    (T ℝ n).derivative.derivative.eval r * ((T ℝ n).eval r - h) ≤ 0 := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (by lia : n ≠ 0)
  have hU : (U ℝ ((n : ℤ) - 1)).eval r = 0 := by
    rw [Polynomial.IsRoot.def, T_derivative_eq_U, Polynomial.eval_mul,
      Polynomial.eval_intCast, mul_eq_zero] at hr
    exact hr.resolve_left (by exact_mod_cast hn0)
  have hpell := congrArg (Polynomial.eval r)
    (T_sq_add_one_sub_X_sq_mul_U_sq ℝ ((n : ℤ) - 1))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, sub_add_cancel,
    hU] at hpell
  norm_num at hpell
  have hTsq : (T ℝ n).eval r ^ 2 = 1 := by
    rcases hpell with hT | hT <;> rw [hT] <;> norm_num
  have hode := congrArg (Polynomial.eval r)
    (one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) (n : ℤ))
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_intCast,
    Function.iterate_succ_apply, Function.iterate_zero_apply,
    Polynomial.IsRoot.def.mp hr, mul_zero, zero_sub] at hode
  norm_num at hode
  have hr_mem := derivative_T_roots_mem_Ioo (by lia : n ≠ 0) r
    ((Polynomial.mem_roots (Polynomial.derivative_ne_zero.mpr (by simp; lia))).mpr hr)
  have hden : 0 < 1 - r ^ 2 := by nlinarith [hr_mem.1, hr_mem.2]
  have hn_sq : 0 < ((n : ℝ) ^ 2) := sq_pos_of_pos (by positivity)
  have hheight : 0 ≤ 1 - h * (T ℝ n).eval r := by
    rcases hpell with hT | hT
    · rw [hT]
      linarith [hh.2]
    · rw [hT]
      linarith [hh.1]
  have hmul : (1 - r ^ 2) *
      ((T ℝ n).derivative.derivative.eval r * ((T ℝ n).eval r - h)) ≤ 0 := by
    have heq : (1 - r ^ 2) *
        ((T ℝ n).derivative.derivative.eval r * ((T ℝ n).eval r - h)) =
        -((n : ℝ) ^ 2) * (1 - h * (T ℝ n).eval r) := by
      calc
        (1 - r ^ 2) *
            ((T ℝ n).derivative.derivative.eval r * ((T ℝ n).eval r - h)) =
            ((1 - r ^ 2) * (T ℝ n).derivative.derivative.eval r) *
              ((T ℝ n).eval r - h) := by ring
        _ = (-((n : ℝ) ^ 2) * (T ℝ n).eval r) * ((T ℝ n).eval r - h) := by
          rw [hode]
          ring
        _ = -((n : ℝ) ^ 2) * (1 - h * (T ℝ n).eval r) := by
          rw [← hTsq]
          ring
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn_sq.le) hheight
  by_contra hpositive
  exact (not_lt_of_ge hmul) (mul_pos hden (lt_of_not_ge hpositive))

/-- For `n ≥ 1`, the level polynomial `Tₙ - h` has degree `n`. -/
theorem natDegree_T_sub_C {n : ℕ} (h : ℝ) :
    (T ℝ n - C h).natDegree = n := by
  simp

/-- For `n ≥ 1` and `h ∈ [-1, 1]`, the level polynomial `Tₙ - h` splits over `ℝ`. -/
theorem T_sub_C_splits {n : ℕ} (hn : n ≠ 0) {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) :
    (T ℝ n - C h).Splits := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with rfl | hn_gt
  · simp [T_one]
  have hn2 : 2 ≤ n := by lia
  have hder := derivative_T_splits_and_nodup hn2
  apply (splits_sub_C_iff_eval_secondDerivative_nonpos
    (f := T ℝ n) (by simp [HasPosLeadingCoeff]) (by simpa using hn2)
    hder.1 hder.2 h).mpr
  exact fun r hr ↦ eval_secondDerivative_mul_sub_nonpos hn2 hh hr

/-- Every root of `Tₙ - h`, for `n ≥ 1` and `h ∈ [-1, 1]`, lies in `[-1, 1]`. -/
theorem T_sub_C_roots_mem_Icc {n : ℕ} (hn : n ≠ 0) {h : ℝ}
    (hh : h ∈ Icc (-1 : ℝ) 1) :
    ∀ r ∈ (T ℝ n - C h).roots, r ∈ Icc (-1 : ℝ) 1 := by
  intro r hr
  have hlevel_ne : T ℝ n - C h ≠ 0 := by
    intro hzero
    have hdegree := natDegree_T_sub_C (n := n) h
    rw [hzero] at hdegree
    exact hn hdegree.symm
  have hroot : (T ℝ n).eval r = h := by
    have hroot0 := (Polynomial.mem_roots hlevel_ne).mp hr
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      sub_eq_zero] at hroot0
    exact hroot0
  have hhabs : |h| ≤ 1 := abs_le.mpr hh
  exact Set.mem_Icc.mpr <| abs_le.mp <|
    (abs_eval_T_real_le_one_iff (n := (n : ℤ)) (by exact_mod_cast hn) r).mpr
      (by simpa [hroot] using hhabs)

/-- For an interior level `h ∈ (-1, 1)`, `Tₙ - h` has simple roots, all in `(-1, 1)`. -/
theorem T_sub_C_splits_simple_roots_mem_Ioo {n : ℕ} (hn : n ≠ 0) {h : ℝ}
    (hh : h ∈ Ioo (-1 : ℝ) 1) :
    (T ℝ n - C h).Splits ∧ HasSimpleRoots (T ℝ n - C h) ∧
      ∀ r ∈ (T ℝ n - C h).roots, r ∈ Ioo (-1 : ℝ) 1 := by
  have hh_closed : h ∈ Icc (-1 : ℝ) 1 := ⟨hh.1.le, hh.2.le⟩
  have hsplits := T_sub_C_splits hn hh_closed
  have hsimple : HasSimpleRoots (T ℝ n - C h) := by
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with rfl | hn_gt
    · simpa [T_one] using
        hasSimpleRoots_of_natDegree_le_one (X_sub_C_ne_zero h) (by simp)
    have hn2 : 2 ≤ n := by lia
    have hstrict := splits_and_hasSimpleRoots_sub_C_of_eval_secondDerivative_neg
      (f := T ℝ n) (by simp [HasPosLeadingCoeff]) (by simpa using hn2)
      (derivative_T_splits_and_nodup hn2).1 h (fun r hr ↦ by
        have hsign := eval_secondDerivative_mul_sub_nonpos hn2 hh_closed hr
        have hpell := congrArg (Polynomial.eval r)
          (T_sq_add_one_sub_X_sq_mul_U_sq ℝ ((n : ℤ) - 1))
        have hU : (U ℝ ((n : ℤ) - 1)).eval r = 0 := by
          rw [Polynomial.IsRoot.def, T_derivative_eq_U, Polynomial.eval_mul,
            Polynomial.eval_intCast, mul_eq_zero] at hr
          exact hr.resolve_left (by exact_mod_cast hn)
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, sub_add_cancel,
          hU] at hpell
        norm_num at hpell
        have hne : (T ℝ n).eval r - h ≠ 0 := by
          intro heq
          rcases hpell with hT | hT
          · rw [hT] at heq
            linarith [hh.2]
          · rw [hT] at heq
            linarith [hh.1]
        have hder_simple : HasSimpleRoots (T ℝ n).derivative :=
          HasSimpleRoots.of_roots_nodup
            (Polynomial.derivative_ne_zero.mpr (by simp; lia))
            (derivative_T_splits_and_nodup hn2).2
        exact lt_of_le_of_ne hsign
          (mul_ne_zero (hder_simple.eval_derivative_ne_zero hr) hne))
    exact hstrict.2
  refine ⟨hsplits, hsimple, ?_⟩
  intro r hr
  have hlevel_ne : T ℝ n - C h ≠ 0 := by
    intro hzero
    have hdegree := natDegree_T_sub_C (n := n) h
    rw [hzero] at hdegree
    exact hn hdegree.symm
  have hroot : (T ℝ n).eval r = h := by
    have hroot0 := (Polynomial.mem_roots hlevel_ne).mp hr
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      sub_eq_zero] at hroot0
    exact hroot0
  have hr_closed := T_sub_C_roots_mem_Icc hn hh_closed r hr
  have hstrict_abs : |r| < 1 := by
    apply lt_of_le_of_ne (abs_le.mpr hr_closed)
    intro habs
    have hT_ge := one_le_abs_eval_T_real (n : ℤ) (le_of_eq habs.symm)
    have hh_abs : |h| < 1 := abs_lt.mpr hh
    rw [hroot] at hT_ge
    linarith
  exact abs_lt.mp hstrict_abs

/-- Affine substitution and scalar multiplication preserve splitting of an
admissible positive-index Chebyshev level. -/
theorem affineLevel_splits (α lam h : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hh : h ∈ Icc (-1 : ℝ) 1) :
    (affineLevel α lam h n).Splits := by
  unfold affineLevel
  exact ((T_sub_C_splits hn hh).comp_of_natDegree_le_one (by compute_degree!)).C_mul α

/-- With positive scalar and affine parameters, an affine Chebyshev level has
positive leading coefficient. -/
theorem affineLevel_hasPosLeadingCoeff {α lam h : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hα : 0 < α) (hlam : 0 < lam) :
    HasPosLeadingCoeff (affineLevel α lam h n) := by
  have hlevel_pos : HasPosLeadingCoeff (T ℝ n - C h) :=
    hasPosLeadingCoeff_sub_C (f := T ℝ n) (by simp [HasPosLeadingCoeff])
      (by simpa using hn) h
  have htranslated := HasPosLeadingCoeff.comp_X_add_C hlevel_pos 1
  have hscaled := hasPosLeadingCoeff_comp_C_mul_X htranslated hlam
  have hfinal := hasPosLeadingCoeff_C_mul hα hscaled
  simpa [affineLevel, Polynomial.comp_assoc, add_comm] using hfinal

/-- A positive-index affine Chebyshev level with positive parameters has degree `n`. -/
theorem affineLevel_natDegree {α lam h : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hα : 0 < α) (hlam : 0 < lam) :
    (affineLevel α lam h n).natDegree = n := by
  have hlevel_pos : HasPosLeadingCoeff (T ℝ n - C h) :=
    hasPosLeadingCoeff_sub_C (f := T ℝ n) (by simp [HasPosLeadingCoeff])
      (by simpa using hn) h
  have hinner_degree : (1 + C lam * X : ℝ[X]).natDegree = 1 := by
    compute_degree!; exact hlam.ne'
  have hinner_lc : (1 + C lam * X : ℝ[X]).leadingCoeff = lam := by
    rw [Polynomial.leadingCoeff, hinner_degree]
    compute_degree!
  unfold affineLevel
  rw [Polynomial.natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hα.ne')]
  rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
  · rw [natDegree_T_sub_C, hinner_degree, mul_one]
  · rw [hinner_lc]
    exact mul_ne_zero hlevel_pos.ne' (pow_ne_zero _ hlam.ne')

/-- The leading coefficient of a positive-index affine Chebyshev level is
`α * 2^(n - 1) * lam^n`. -/
theorem affineLevel_leadingCoeff {α lam h : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hα : 0 < α) (hlam : 0 < lam) :
    (affineLevel α lam h n).leadingCoeff = α * 2 ^ (n - 1) * lam ^ n := by
  have hT_degree : (T ℝ n).natDegree = n := by simp
  have hlevel_lc : (T ℝ n - C h).leadingCoeff = (T ℝ n).leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [Polynomial.natDegree_sub_C, hT_degree, Polynomial.coeff_sub]
    simp [Polynomial.coeff_C, hn]
  have hinner_degree : (1 + C lam * X : ℝ[X]).natDegree = 1 := by
    compute_degree!; exact hlam.ne'
  have hinner_lc : (1 + C lam * X : ℝ[X]).leadingCoeff = lam := by
    rw [Polynomial.leadingCoeff, hinner_degree]
    compute_degree!
  unfold affineLevel
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hα.ne')]
  rw [Polynomial.leadingCoeff_comp (by rw [hinner_degree]; exact one_ne_zero), hlevel_lc,
    Polynomial.Chebyshev.leadingCoeff_T, hinner_lc, natDegree_T_sub_C]
  norm_num
  ring

/-- Every real root of an affine Chebyshev level with positive scale parameter
lies in the transported interval `[-2 / lam, 0]`. -/
theorem affineLevel_isRoot_mem_Icc {α lam h r : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hα : α ≠ 0) (hlam : 0 < lam)
    (hh : h ∈ Icc (-1 : ℝ) 1) (hr : (affineLevel α lam h n).IsRoot r) :
    r ∈ Icc (-2 / lam) 0 := by
  rw [affineLevel, Polynomial.IsRoot.def, Polynomial.eval_mul,
    Polynomial.eval_C, mul_eq_zero] at hr
  have hlevel := hr.resolve_left hα
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hlevel
  have hT : (T ℝ n).eval (1 + lam * r) = h := by
    rw [Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] at hlevel
    exact hlevel
  have hxabs : |1 + lam * r| ≤ 1 :=
    (abs_eval_T_real_le_one_iff (n := (n : ℤ)) (by exact_mod_cast hn) _).mpr (by
      rw [hT]
      exact abs_le.mpr hh)
  have hx := abs_le.mp hxabs
  constructor
  · apply (div_le_iff₀ hlam).2
    nlinarith [hx.1]
  · nlinarith [hx.2]

/-- Positive affine Chebyshev levels at admissible heights are PF polynomials. -/
theorem affineLevel_isPFPolynomial {α lam h : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hα : 0 < α) (hlam : 0 < lam)
    (hh : h ∈ Icc (-1 : ℝ) 1) :
    IsPFPolynomial (affineLevel α lam h n) := by
  let q := (T ℝ n - C h).comp (X + C 1)
  have hlevel_splits := T_sub_C_splits hn hh
  have hq_splits : q.Splits := by
    exact hlevel_splits.comp_X_add_C 1
  have hlevel_pos : HasPosLeadingCoeff (T ℝ n - C h) :=
    hasPosLeadingCoeff_sub_C (f := T ℝ n) (by simp [HasPosLeadingCoeff])
      (by simpa using hn) h
  have hq_pos : HasPosLeadingCoeff q :=
    HasPosLeadingCoeff.comp_X_add_C hlevel_pos 1
  have hq_roots : ∀ r ∈ q.roots, r ≤ 0 := by
    intro r hr
    have hq_root := (Polynomial.mem_roots hq_pos.ne_zero).mp hr
    have hlevel_root : (T ℝ n - C h).IsRoot (r + 1) := by
      simpa [q, Polynomial.IsRoot.def] using hq_root
    have hlevel_mem := (Polynomial.mem_roots hlevel_pos.ne_zero).mpr hlevel_root
    have ht_mem := T_sub_C_roots_mem_Icc hn hh (r + 1) hlevel_mem
    linarith [ht_mem.2]
  have hq_nonneg : HasNonnegCoeffs q :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq_splits).2
      ⟨hq_pos, hq_roots⟩).1
  have hq_pf := IsPFPolynomial.of_realRooted_nonneg hq_nonneg hq_splits
  have hscaled := hq_pf.comp_C_mul_X_add_C hlam (show 0 ≤ (0 : ℝ) by rfl)
  have hfinal := hscaled.const_mul hα
  simpa [q, affineLevel, Polynomial.comp_assoc, add_comm] using hfinal

/-- At an interior height, a positive affine Chebyshev level splits with simple
roots, all in the open transported interval `(-2 / lam, 0)`. -/
theorem affineLevel_splits_simple_roots_mem_Ioo {α lam h : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hα : 0 < α) (hlam : 0 < lam)
    (hh : h ∈ Ioo (-1 : ℝ) 1) :
    (affineLevel α lam h n).Splits ∧ HasSimpleRoots (affineLevel α lam h n) ∧
      ∀ r ∈ (affineLevel α lam h n).roots, r ∈ Ioo (-2 / lam) 0 := by
  have hbase := T_sub_C_splits_simple_roots_mem_Ioo hn hh
  have hcomp_simple := hbase.2.1.comp_C_mul_X_add_C (a := lam) (b := 1) hlam.ne'
  have hsimple : HasSimpleRoots (affineLevel α lam h n) := by
    apply HasSimpleRoots.C_mul (c := α) _ hα.ne'
    simpa [affineLevel, add_comm] using hcomp_simple
  refine ⟨affineLevel_splits α lam h hn ⟨hh.1.le, hh.2.le⟩, hsimple, ?_⟩
  intro r hr
  have hfamily_pos := affineLevel_hasPosLeadingCoeff (h := h) hn hα hlam
  have hfamily_root := (Polynomial.mem_roots hfamily_pos.ne_zero).mp hr
  rw [affineLevel, Polynomial.IsRoot.def, Polynomial.eval_mul,
    Polynomial.eval_C, mul_eq_zero] at hfamily_root
  have hlevel_eval := hfamily_root.resolve_left hα.ne'
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hlevel_eval
  have hlevel_root : (T ℝ n - C h).IsRoot (1 + lam * r) := by
    exact hlevel_eval
  have hlevel_pos : HasPosLeadingCoeff (T ℝ n - C h) :=
    hasPosLeadingCoeff_sub_C (f := T ℝ n) (by simp [HasPosLeadingCoeff])
      (by simpa using hn) h
  have hlevel_mem := (Polynomial.mem_roots hlevel_pos.ne_zero).mpr hlevel_root
  have hx := hbase.2.2 (1 + lam * r) hlevel_mem
  constructor
  · apply (div_lt_iff₀ hlam).2
    nlinarith [hx.1]
  · nlinarith [hx.2]

/-- For a fixed height `h`, every positive-index first-kind Chebyshev level
polynomial splits over `ℝ` exactly when `|h| ≤ 1`. -/
theorem forall_pos_T_sub_C_splits_iff_abs_le_one (h : ℝ) :
    (∀ n : ℕ, n ≠ 0 → (T ℝ n - C h).Splits) ↔ |h| ≤ 1 := by
  constructor
  · intro hall
    have hsplits : (T ℝ 3 - C h).Splits := hall 3 (by norm_num)
    have hdisc := cubicDiscr_nonneg_of_splits_natDegree_three
      (natDegree_T_sub_C (n := 3) h) hsplits
    have hT3 : T ℝ (3 : ℤ) = 4 * X ^ 3 - 3 * X := by
      rw [show (3 : ℤ) = 1 + 2 by norm_num, T_add_two]
      rw [show (1 + 1 : ℤ) = 2 by norm_num, T_two, T_one]
      ring
    have hdisc_eq : cubicDiscr (T ℝ (3 : ℤ) - C h) = 432 * (1 - h ^ 2) := by
      have hpoly : T ℝ (3 : ℤ) - C h =
          C 4 * X ^ 3 + C 0 * X ^ 2 + C (-3) * X + C (-h) := by
        rw [hT3]
        norm_num [← C_ofNat]
        rw [map_ofNat Polynomial.C 3, map_ofNat Polynomial.C 4]
        ring
      rw [hpoly, cubicDiscr_of_coeffs]
      norm_num
      ring
    norm_num at hdisc
    rw [hdisc_eq] at hdisc
    exact (sq_le_one_iff_abs_le_one h).mp (by nlinarith)
  · intro hh n hn
    exact T_sub_C_splits hn (abs_le.mp hh)

/-- For nonzero affine and scalar parameters, all positive-index affine
Chebyshev levels split exactly for heights of absolute value at most one. -/
theorem forall_pos_affineLevel_splits_iff_abs_le_one
    (α lam h : ℝ) (hα : α ≠ 0) (hlam : lam ≠ 0) :
    (∀ n : ℕ, n ≠ 0 → (affineLevel α lam h n).Splits) ↔ |h| ≤ 1 := by
  have hinner_degree : (1 + C lam * X : ℝ[X]).natDegree = 1 := by
    compute_degree!
  constructor
  · intro hall
    apply (forall_pos_T_sub_C_splits_iff_abs_le_one h).mp
    intro n hn
    have hscaled := (hall n hn).C_mul α⁻¹
    have hscale_eq : C α⁻¹ * affineLevel α lam h n =
        (T ℝ n - C h).comp (1 + C lam * X) := by
      unfold affineLevel
      rw [← mul_assoc, ← map_mul]
      simp [hα]
    have hcomp : ((T ℝ n - C h).comp (1 + C lam * X)).Splits := by
      rw [← hscale_eq]
      exact hscaled
    exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one hinner_degree).mpr hcomp
  · intro hh n hn
    exact affineLevel_splits α lam h hn (abs_le.mp hh)

/-- For positive scalar and affine parameters, all positive-index affine
Chebyshev levels are PF polynomials exactly at heights of absolute value at most one. -/
theorem forall_pos_affineLevel_isPFPolynomial_iff_abs_le_one
    (α lam h : ℝ) (hα : 0 < α) (hlam : 0 < lam) :
    (∀ n : ℕ, n ≠ 0 → IsPFPolynomial (affineLevel α lam h n)) ↔ |h| ≤ 1 := by
  constructor
  · intro hall
    apply (forall_pos_affineLevel_splits_iff_abs_le_one α lam h hα.ne' hlam.ne').mp
    intro n hn
    exact (hall n hn).ne_zero_and_splits
      (affineLevel_hasPosLeadingCoeff hn hα hlam).ne_zero |>.2
  · intro hh n hn
    exact affineLevel_isPFPolynomial hn hα hlam (abs_le.mp hh)

/-- A Chebyshev polynomial of degree at least two shifted upward by more than one
cannot split over the reals. -/
theorem not_splits_T_add_C_of_one_lt {d : ℕ} {c : ℝ}
    (hd : 2 ≤ d) (hc : 1 < c) :
    ¬(Polynomial.Chebyshev.T ℝ d + C c).Splits := by
  let q := Polynomial.Chebyshev.T ℝ d + C c
  have hTdegree : (Polynomial.Chebyshev.T ℝ d).natDegree = d := by
    simp
  have hdegree : q.natDegree = d := by
    dsimp [q]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact hTdegree
    · rw [hTdegree]
      simp
      lia
  intro hsplits
  have hroots : ∀ r ∈ q.roots, r < -1 := by
    intro r hr
    have hrzero := Polynomial.isRoot_of_mem_roots hr
    rw [Polynomial.IsRoot.def] at hrzero
    by_contra hrnot
    have hrge : -1 ≤ r := le_of_not_gt hrnot
    by_cases hrle : r ≤ 1
    · have hbound := Polynomial.Chebyshev.abs_eval_T_real_le_one (d : ℤ)
        (abs_le.mpr ⟨by linarith, hrle⟩)
      have hlower := (abs_le.mp hbound).1
      simp only [q, eval_add, eval_C] at hrzero
      linarith
    · have hbound := Polynomial.Chebyshev.one_le_eval_T_real (d : ℤ)
        (le_of_not_ge hrle)
      simp only [q, eval_add, eval_C] at hrzero
      linarith
  have hderDegree : q.derivative.natDegree = d - 1 := by
    rw [q.natDegree_derivative, hdegree]
  have hderSplits : q.derivative.Splits := hsplits.derivative
  have hcard : q.derivative.roots.card = d - 1 := by
    rw [Polynomial.splits_iff_card_roots.mp hderSplits, hderDegree]
  have hcardPos : 0 < q.derivative.roots.card := by
    rw [hcard]
    lia
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hcardPos
  have hqDegree : 2 ≤ q.natDegree := by
    rw [hdegree]
    exact hd
  have hrlt : r < -1 := roots_derivative_lt_of_roots_lt hsplits hqDegree hroots r hr
  have hrzero := Polynomial.isRoot_of_mem_roots hr
  rw [Polynomial.IsRoot.def] at hrzero
  have hindex : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by
    norm_cast
    lia
  have hUzero :
      (Polynomial.Chebyshev.U ℝ ((d - 1 : ℕ) : ℤ)).eval r = 0 := by
    simp only [q, derivative_add, Polynomial.Chebyshev.T_derivative_eq_U,
      derivative_C, add_zero, eval_mul, eval_intCast] at hrzero
    rw [hindex] at hrzero
    exact (mul_eq_zero.mp hrzero).resolve_left (by positivity)
  have hUne : Polynomial.Chebyshev.U ℝ ((d - 1 : ℕ) : ℤ) ≠ 0 :=
    Polynomial.Chebyshev.U_ne_zero ℝ _ (by norm_num)
  have hUmem := (Polynomial.mem_roots hUne).mpr hUzero
  rw [Polynomial.Chebyshev.roots_U_real, Finset.mem_val] at hUmem
  obtain ⟨k, _, hrEq⟩ := Finset.mem_image.mp hUmem
  rw [← hrEq] at hrlt
  exact (not_lt_of_ge (Real.neg_one_le_cos _)) hrlt

end Chebyshev

end RealRooted
