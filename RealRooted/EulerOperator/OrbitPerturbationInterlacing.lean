module

public import RealRooted.EulerOperator.OrbitPerturbation
public import RealRooted.Basic.ProperPosition
import RealRooted.MaWang.CriticalSign
import RealRooted.Mathlib.Analysis.Polynomial.InverseBernstein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monomial perturbations of the centered Euler orbit

Let `p n` be the orbit of `1` under the centered Euler step `f ↦ X f + α (X² - 1) f'`.  For
`α ≥ 1 / 2` and `-1 < b ≤ 1` the perturbed rows `h n = p n + b X ^ n` have simple roots in
`(-1, 1)` and consecutive rows interlace strictly (RealRooted #2513, Theorem 1 in centered
coordinates).

The proof compares `h n` with `p n` at the sign alternation points of `p n`: the critical values
of `p n` dominate `b c ^ n` (`centeredEulerOrbit_critical_values` and
`centeredEulerOrbit_small_critical`), so `h n` changes sign like `p n`.  Since
`h (n + 1) = X h n + α (X² - 1) (p n)'`, the root-sign criterion
`strictInterl_of_eval_mul_derivative_neg` gives `h n ≺ h (n + 1)`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The leading coefficients of the centered Euler orbit are at least one for `α ≥ 0`. -/
theorem one_le_leadingCoeff_centeredEulerOrbit {α : ℝ} (hα : 0 ≤ α) (n : ℕ) :
    1 ≤ (centeredEulerOrbit α n).leadingCoeff := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hne : centeredEulerOrbit α n ≠ 0 := by
        intro h0
        rw [h0, leadingCoeff_zero] at ih
        linarith
      have hnn : 0 ≤ α * ((centeredEulerOrbit α n).natDegree : ℝ) :=
        mul_nonneg hα (Nat.cast_nonneg _)
      rw [centeredEulerOrbit_succ, (centeredEulerStep_degree_leadingCoeff hne (by linarith)).2]
      nlinarith

/-- `p` has the sign of `p (C (k + 1))` on `(C k, C (k + 1))` when `p` changes sign across the
interval and `p'` does not vanish inside it. -/
private theorem derivative_mul_eval_pos {p : ℝ[X]} {u v r : ℝ}
    (hne : ∀ x ∈ Ioo u v, p.derivative.eval x ≠ 0) (hprod : p.eval u * p.eval v < 0)
    (hr : r ∈ Ioo u v) : 0 < p.derivative.eval r * p.eval v := by
  have huv : u ≤ v := (hr.1.trans hr.2).le
  rcases Polynomial.derivative_pos_or_neg_of_ne_zero hne with hd | hd
  · have hmono : StrictMonoOn (fun x ↦ p.eval x) (Icc u v) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc u v) p.continuous.continuousOn
        fun x hx ↦ ?_
      rw [interior_Icc] at hx
      simpa [Polynomial.deriv] using hd x hx
    have hlt : p.eval u < p.eval v :=
      hmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ (hr.1.trans hr.2)
    have hv : 0 < p.eval v := by nlinarith
    exact mul_pos (hd r hr) hv
  · have hanti : StrictAntiOn (fun x ↦ p.eval x) (Icc u v) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc u v) p.continuous.continuousOn
        fun x hx ↦ ?_
      rw [interior_Icc] at hx
      simpa [Polynomial.deriv] using hd x hx
    have hlt : p.eval v < p.eval u :=
      hanti ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ (hr.1.trans hr.2)
    have hv : p.eval v < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg (hd r hr) hv

/-- Perturbing `p` by `b X ^ n` keeps the sign of `p` at its alternation points when the
critical values of `p` dominate `b c ^ n` and `b > -1`. -/
private theorem eval_add_monomial_mul_pos {p : ℝ[X]} {n : ℕ} {b : ℝ} (hb : -1 < b)
    (hone : p.eval 1 = 1) (hmone : p.eval (-1) = (-1) ^ n)
    (hcrit : ∀ c ∈ Ioo (-1 : ℝ) 1, p.derivative.eval c = 0 → |b * c ^ n| < |p.eval c|)
    {c : ℝ} (hc : c = -1 ∨ c = 1 ∨ (c ∈ Ioo (-1 : ℝ) 1 ∧ p.derivative.eval c = 0)) :
    0 < (p + C b * X ^ n).eval c * p.eval c := by
  have hev : (p + C b * X ^ n).eval c = p.eval c + b * c ^ n := by simp
  rw [hev]
  rcases hc with rfl | rfl | ⟨hmem, hcr⟩
  · have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hmone, show ((-1 : ℝ) ^ n + b * (-1) ^ n) * (-1) ^ n = (1 + b) * ((-1 : ℝ) ^ n) ^ 2 by
      ring, hsq]
    linarith
  · rw [hone, one_pow]
    linarith
  · have hlt := hcrit _ hmem hcr
    have h1 : -(|b * c ^ n| * |p.eval c|) ≤ b * c ^ n * p.eval c := by
      rw [← abs_mul]
      exact neg_abs_le _
    have h2 : |p.eval c| * |p.eval c| = p.eval c * p.eval c := abs_mul_abs_self _
    nlinarith [mul_pos ((abs_nonneg _).trans_lt hlt) (sub_pos.mpr hlt)]

/-- Monomial perturbation of one centered Euler step.  Let `p` have degree `n > 0`, positive
leading coefficient, simple roots in `(-1, 1)`, `p 1 = 1` and `p (-1) = (-1) ^ n`, and let
`b > -1` be such that `|b c ^ n| < |p c|` at every critical point `c ∈ (-1, 1)` and
`lc p + b > 0`.  Then `h = p + b X ^ n` has degree `n`, positive leading coefficient and simple
roots in `(-1, 1)`, and `h` strictly interlaces `X h + α (X² - 1) p' = L p + b X ^ (n + 1)`. -/
theorem strictInterl_centeredEulerStep_add_monomial {α b : ℝ} (hα : 0 < α) (hb : -1 < b)
    {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (hdeg : p.natDegree = n)
    (hroot : IsRealRootedIn (Ioo (-1 : ℝ) 1) p) (hsimple : HasSimpleRoots p)
    (hpos : HasPosLeadingCoeff p) (hlead : 0 < p.leadingCoeff + b)
    (hone : p.eval 1 = 1) (hmone : p.eval (-1) = (-1) ^ n)
    (hcrit : ∀ c ∈ Ioo (-1 : ℝ) 1, p.derivative.eval c = 0 → |b * c ^ n| < |p.eval c|) :
    (p + C b * X ^ n).natDegree = n ∧ HasPosLeadingCoeff (p + C b * X ^ n) ∧
      IsRealRootedIn (Ioo (-1 : ℝ) 1) (p + C b * X ^ n) ∧ HasSimpleRoots (p + C b * X ^ n) ∧
      StrictInterl (p + C b * X ^ n) (centeredEulerStep α p + C b * X ^ (n + 1)) := by
  set h := p + C b * X ^ n with hh
  have hcoeff : h.coeff n = p.leadingCoeff + b := by
    simp [hh, leadingCoeff, hdeg]
  have hhdeg : h.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_add_le_of_degree_le hdeg.le (natDegree_C_mul_X_pow_le b n))
    (hcoeff ▸ hlead.ne')
  have hhpos : HasPosLeadingCoeff h := by
    rw [HasPosLeadingCoeff, leadingCoeff, hhdeg, hcoeff]
    exact hlead
  have hcard := card_roots_filter_Ioo_of_isRealRootedIn hroot
  rw [hdeg] at hcard
  obtain ⟨A, hA0, hAn, hAinc, hAcrit, hAprod, hAder⟩ :=
    Polynomial.exists_sign_alternation_points hn hdeg hcard hsimple.roots_nodup
  have hsame : ∀ k ≤ n, 0 < h.eval (A k) * p.eval (A k) := by
    intro k hk
    refine eval_add_monomial_mul_pos hb hone hmone hcrit ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl hA0
    rcases hk.eq_or_lt with rfl | hkn
    · exact Or.inr (Or.inl hAn)
    · exact Or.inr (Or.inr (hAcrit k hk0 hkn))
  have hsign : ∀ k < n, h.eval (A k) * h.eval (A (k + 1)) < 0 := by
    intro k hk
    have h1 := hsame k hk.le
    have h2 := hsame (k + 1) hk
    have h3 := hAprod k hk
    nlinarith [mul_pos h1 h2]
  obtain ⟨hnodup, hcardh, hloc, hdsign⟩ := Polynomial.roots_of_sign_changes hn hhdeg hAinc hsign
  have hmono : ∀ a c, a ≤ c → c ≤ n → A a ≤ A c := by
    intro a c hac hcn
    induction c, hac using Nat.le_induction with
    | base => exact le_rfl
    | succ c hac ih => exact (ih (by lia)).trans (hAinc c (by lia)).le
  have hinside : ∀ r, h.IsRoot r → r ∈ Ioo (-1 : ℝ) 1 := by
    intro r hr
    obtain ⟨k, hk, hrk⟩ := hloc r hr
    constructor
    · linarith [hmono 0 k (Nat.zero_le _) hk.le, hrk.1]
    · linarith [hmono (k + 1) n hk le_rfl, hrk.2]
  have hne : h ≠ 0 := hhpos.ne_zero
  have hsplit : h.Splits := splits_iff_card_roots.mpr (by rw [hcardh, hhdeg])
  have hreal : IsRealRootedIn (Ioo (-1 : ℝ) 1) h :=
    ⟨hne, hsplit, fun z hz ↦ hinside z ((mem_roots hne).mp hz)⟩
  -- The next row.
  set F := centeredEulerStep α p + C b * X ^ (n + 1) with hF
  have hFid : F = X * h + C α * (X ^ 2 - 1) * p.derivative := by
    simp only [hF, hh, centeredEulerStep]
    ring
  obtain ⟨hsdeg, hslc⟩ := centeredEulerStep_degree_leadingCoeff (α := α) hpos.ne_zero
    (by positivity)
  rw [hdeg] at hsdeg hslc
  have hFcoeff : F.coeff (n + 1) = (1 + α * n) * p.leadingCoeff + b := by
    simp only [hF, coeff_add, coeff_C_mul_X_pow, ↓reduceIte]
    rw [← hslc, leadingCoeff, hsdeg]
  have hFlc : 0 < (1 + α * n) * p.leadingCoeff + b := by
    have hlc : 0 < p.leadingCoeff := hpos
    have : 0 ≤ α * n * p.leadingCoeff := by positivity
    nlinarith
  have hFdeg : F.natDegree = n + 1 := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_add_le_of_degree_le hsdeg.le (natDegree_C_mul_X_pow_le b _))
    (by rw [hFcoeff]; exact hFlc.ne')
  have hFpos : HasPosLeadingCoeff F := by
    rw [HasPosLeadingCoeff, leadingCoeff, hFdeg, hFcoeff]
    exact hFlc
  refine ⟨hhdeg, hhpos, hreal, HasSimpleRoots.of_roots_nodup hne hnodup,
    strictInterl_of_eval_mul_derivative_neg hsplit hhpos hFpos (by lia) (by lia) (by lia) ?_⟩
  intro r hr
  obtain ⟨k, hk, hrk⟩ := hloc r hr
  have hr1 := hinside r hr
  have hFr : F.eval r = α * (r ^ 2 - 1) * p.derivative.eval r := by
    rw [hFid]
    simp [hr.eq_zero]
  have hp' := derivative_mul_eval_pos (hAder k hk) (hAprod k hk) hrk
  have hh' := hdsign k hk r hrk hr
  have hhp := hsame (k + 1) hk
  have hprod : 0 < h.derivative.eval r * p.derivative.eval r := by
    have hmul : 0 < (h.derivative.eval r * p.derivative.eval r) *
        (h.eval (A (k + 1)) * p.eval (A (k + 1))) := by
      have := mul_pos hh' hp'
      linarith [show (h.derivative.eval r * p.derivative.eval r) *
          (h.eval (A (k + 1)) * p.eval (A (k + 1))) =
        (h.derivative.eval r * h.eval (A (k + 1))) *
          (p.derivative.eval r * p.eval (A (k + 1))) by ring]
    exact (mul_pos_iff_of_pos_right hhp).mp hmul
  have hsq : r ^ 2 - 1 < 0 := by nlinarith [hr1.1, hr1.2]
  rw [hFr, show α * (r ^ 2 - 1) * p.derivative.eval r * h.derivative.eval r =
    α * (r ^ 2 - 1) * (h.derivative.eval r * p.derivative.eval r) by ring]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hα hsq) hprod

/-- **Monomial perturbations of the centered Euler orbit** (RealRooted #2513, Theorem 1 in
centered coordinates).  For `α ≥ 1 / 2`, `-1 < b ≤ 1` and `n > 0`, the polynomial
`h n = p n + b X ^ n` has degree `n`, positive leading coefficient and simple roots in `(-1, 1)`,
and `h n` strictly interlaces `h (n + 1)`. -/
theorem centeredEulerOrbit_add_monomial {α b : ℝ} (hα : 1 / 2 ≤ α) (hb : -1 < b) (hb1 : b ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    (centeredEulerOrbit α n + C b * X ^ n).natDegree = n ∧
      HasPosLeadingCoeff (centeredEulerOrbit α n + C b * X ^ n) ∧
      IsRealRootedIn (Ioo (-1 : ℝ) 1) (centeredEulerOrbit α n + C b * X ^ n) ∧
      HasSimpleRoots (centeredEulerOrbit α n + C b * X ^ n) ∧
      StrictInterl (centeredEulerOrbit α n + C b * X ^ n)
        (centeredEulerOrbit α (n + 1) + C b * X ^ (n + 1)) := by
  obtain ⟨hdeg, hpos, hroot, hsimple, hone, hmone⟩ := centeredEulerOrbit_package hα n
  have hlc := one_le_leadingCoeff_centeredEulerOrbit (α := α) (by linarith) n
  refine strictInterl_centeredEulerStep_add_monomial (by linarith) hb hn hdeg hroot hsimple hpos
    (by linarith) hone hmone ?_
  intro c hc hcrit
  have hbabs : |b| ≤ 1 := abs_le.mpr ⟨by linarith, hb1⟩
  rcases le_or_gt n 4 with h4 | h5
  · exact centeredEulerOrbit_small_critical hα hbabs hn h4 hc hcrit
  · have h1 := centeredEulerOrbit_critical_values hα h5 c hc hcrit
    have hcabs : |c| < 1 := abs_lt.mpr ⟨hc.1, hc.2⟩
    calc |b * c ^ n| = |b| * |c| ^ n := by rw [abs_mul, abs_pow]
      _ ≤ 1 * |c| ^ n := by gcongr
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (abs_nonneg c) hcabs (by lia)
      _ ≤ _ := h1

end RealRooted
