module

public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
import RealRooted.Interlacing.Multiplicity
import RealRooted.Derivative.Algebra
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.DerivativeRecurrence.RootWindow

/-!
# Exterior-root obstruction for a derivative of a lagged row

We prove the obstruction requested in RealRooted issue #1234, comment of
2026-11-09. For a positive-leading pair `g ≪ f`, at a root of `f` strictly
above all roots of `g` both derivatives are positive. At a root strictly
below all roots of `g`, the derivatives have opposite signs. The gap
hypotheses express that the outermost roots are unshared; interior roots
may be repeated or shared.

The final corollary uses the termwise flux shape underlying
`LiuWang.strictInterl_mul_add_sum_mul_of_eval_nonpos` (Liu--Wang,
*A unified approach to polynomial sequences with only real zeros*, Theorem 2.3,
arXiv:math/0509207v5). This is a necessary condition for a separate derivative
summand, not an obstruction to compensation in the combined flux.
-/

public section

open Polynomial

namespace RealRooted

/-- A nonconstant split polynomial has a nonempty finite set of roots. -/
private lemma roots_toFinset_nonempty {p : ℝ[X]} (hs : p.Splits)
    (hd : p.natDegree ≠ 0) : p.roots.toFinset.Nonempty := by
  rw [Multiset.toFinset_nonempty]
  exact Multiset.card_pos.mp (by rw [splits_iff_card_roots.mp hs]; lia)

/-- Strict exterior upper bounds can be replaced by an attained weak bound. -/
private lemma exists_root_upper_bound_lt {p : ℝ[X]} (hs : p.Splits)
    (hd : p.natDegree ≠ 0) {r : ℝ} (hgap : ∀ t ∈ p.roots, t < r) :
    ∃ U, (∀ t ∈ p.roots, t ≤ U) ∧ U < r := by
  have hne := roots_toFinset_nonempty hs hd
  refine ⟨p.roots.toFinset.max' hne, ?_, ?_⟩
  · exact fun t ht ↦ Finset.le_max' _ _ (Multiset.mem_toFinset.mpr ht)
  · exact hgap _ (Multiset.mem_toFinset.mp (Finset.max'_mem _ hne))

/-- Strict exterior lower bounds can be replaced by an attained weak bound. -/
private lemma exists_root_lower_bound_gt {p : ℝ[X]} (hs : p.Splits)
    (hd : p.natDegree ≠ 0) {r : ℝ} (hgap : ∀ t ∈ p.roots, r < t) :
    ∃ L, (∀ t ∈ p.roots, L ≤ t) ∧ r < L := by
  have hne := roots_toFinset_nonempty hs hd
  refine ⟨p.roots.toFinset.min' hne, ?_, ?_⟩
  · exact fun t ht ↦ Finset.min'_le _ _ (Multiset.mem_toFinset.mpr ht)
  · exact hgap _ (Multiset.mem_toFinset.mp (Finset.min'_mem _ hne))

/-- At an unshared root of the right polynomial, the interlacing sign product
is strictly positive, even if other roots are shared or repeated. -/
theorem StrictInterl.eval_mul_derivative_pos_of_not_isRoot
    {g f : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    {r : ℝ} (hr : f.IsRoot r) (hgr : ¬g.IsRoot r) :
    0 < g.eval r * f.derivative.eval r := by
  have hm : f.rootMultiplicity r = 1 := by
    have hpos := (rootMultiplicity_pos hgf.2.1.1).mpr hr
    have hle : f.rootMultiplicity r ≤ 1 := by
      by_contra h
      exact hgr (hgf.isRoot_of_one_lt_rootMultiplicity (by lia))
    lia
  exact lt_of_le_of_ne (hgf.eval_mul_eval_derivative_nonneg hg hf hr)
    (Ne.symm (mul_ne_zero hgr (eval_derivative_ne_zero_of_rootMultiplicity_eq_one hr hm)))

/-- At a root of `f` above every root of a nonconstant interlacer `g`, both
derivatives are positive. In the differ-by-one case this covers the largest
unshared root of `f`, including degree two. -/
theorem StrictInterl.derivative_eval_pos_of_roots_lt
    {g f : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    (hd : g.natDegree ≠ 0) {r : ℝ} (hr : f.IsRoot r)
    (hgap : ∀ t ∈ g.roots, t < r) :
    0 < g.derivative.eval r ∧ 0 < f.derivative.eval r := by
  obtain ⟨U, hU, hrU⟩ := exists_root_upper_bound_lt hgf.1.2 hd hgap
  have hgval := eval_pos_of_roots_le hgf.1.2 hg hU hrU
  have hprod := hgf.eval_mul_derivative_pos_of_not_isRoot hg hf hr hgval.ne'
  exact ⟨derivative_eval_pos_of_roots_le hgf.1.2 hg hd hU hrU,
    (mul_pos_iff.mp hprod).resolve_right (fun h ↦ (not_lt_of_ge hgval.le) h.1) |>.2⟩

/-- Below all roots of a nonconstant interlacer, the two derivative signs
are `(-1)^(deg g + 1)` and `(-1)^(deg g)`, respectively. For `deg f = d` and
`deg g = d - 1`, these are the signs `(-1)^d` and `(-1)^(d - 1)`. -/
theorem StrictInterl.derivative_eval_sign_of_lt_roots
    {g f : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    (hd : g.natDegree ≠ 0) {r : ℝ} (hr : f.IsRoot r)
    (hgap : ∀ t ∈ g.roots, r < t) :
    0 < (-1 : ℝ) ^ (g.natDegree + 1) * g.derivative.eval r ∧
      0 < (-1 : ℝ) ^ g.natDegree * f.derivative.eval r := by
  obtain ⟨L, hL, hrL⟩ := exists_root_lower_bound_gt hgf.1.2 hd hgap
  have hgval := neg_one_pow_mul_eval_pos_of_roots_ge hgf.1.2 hg hL hrL
  have hgr : ¬g.IsRoot r := by
    intro h
    rw [h.eq_zero, mul_zero] at hgval
    exact (lt_irrefl 0) hgval
  have hprod := hgf.eval_mul_derivative_pos_of_not_isRoot hg hf hr hgr
  have hsq : ((-1 : ℝ) ^ g.natDegree) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  refine ⟨derivative_neg_one_pow_mul_eval_pos_of_roots_ge hgf.1.2 hg hd hL hrL, ?_⟩
  have heq : ((-1 : ℝ) ^ g.natDegree * g.eval r) *
      ((-1 : ℝ) ^ g.natDegree * f.derivative.eval r) =
      g.eval r * f.derivative.eval r := by
    calc
      _ = ((-1 : ℝ) ^ g.natDegree) ^ 2 *
          (g.eval r * f.derivative.eval r) := by ring
      _ = _ := by rw [hsq, one_mul]
  have hpos : 0 < ((-1 : ℝ) ^ g.natDegree * g.eval r) *
      ((-1 : ℝ) ^ g.natDegree * f.derivative.eval r) := heq ▸ hprod
  exact (mul_pos_iff.mp hpos).resolve_right (fun h ↦ (not_lt_of_ge hgval.le) h.1) |>.2

/-- The derivative of an interlacer has opposite flux orientations at the
two unshared exterior roots of the current row. -/
theorem StrictInterl.derivative_eval_mul_derivative_outer_signs
    {g f : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    (hd : g.natDegree ≠ 0) {l r : ℝ} (hl : f.IsRoot l) (hr : f.IsRoot r)
    (hleft : ∀ t ∈ g.roots, l < t) (hright : ∀ t ∈ g.roots, t < r) :
    g.derivative.eval l * f.derivative.eval l < 0 ∧
      0 < g.derivative.eval r * f.derivative.eval r := by
  obtain ⟨hgr, hfr⟩ := hgf.derivative_eval_pos_of_roots_lt hg hf hd hr hright
  obtain ⟨hgl, hfl⟩ := hgf.derivative_eval_sign_of_lt_roots hg hf hd hl hleft
  rw [pow_succ] at hgl
  have hgneg : (-1 : ℝ) ^ g.natDegree * g.derivative.eval l < 0 := by
    nlinarith only [hgl]
  have hprod := mul_neg_of_neg_of_pos hgneg hfl
  have hsq : ((-1 : ℝ) ^ g.natDegree) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have heq : ((-1 : ℝ) ^ g.natDegree * g.derivative.eval l) *
      ((-1 : ℝ) ^ g.natDegree * f.derivative.eval l) =
      g.derivative.eval l * f.derivative.eval l := by
    calc
      _ = ((-1 : ℝ) ^ g.natDegree) ^ 2 *
          (g.derivative.eval l * f.derivative.eval l) := by ring
      _ = _ := by rw [hsq, one_mul]
  exact ⟨heq ▸ hprod, mul_pos hgr hfr⟩

/-- A separate derivative-lag summand has nonpositive root flux at both
outer roots exactly when its coefficient is nonnegative at the smallest
root and nonpositive at the largest root. This uses the evaluation-product
shape of the finite-family Liu--Wang flux calculation. -/
theorem StrictInterl.derivative_lag_flux_nonpos_iff
    {g f D : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    (hd : g.natDegree ≠ 0) {l r : ℝ} (hl : f.IsRoot l) (hr : f.IsRoot r)
    (hleft : ∀ t ∈ g.roots, l < t) (hright : ∀ t ∈ g.roots, t < r) :
    ((D * g.derivative).eval l * f.derivative.eval l ≤ 0 ∧
      (D * g.derivative).eval r * f.derivative.eval r ≤ 0) ↔
      D.eval r ≤ 0 ∧ 0 ≤ D.eval l := by
  obtain ⟨hneg, hpos⟩ :=
    hgf.derivative_eval_mul_derivative_outer_signs hg hf hd hl hr hleft hright
  simp only [eval_mul, mul_assoc]
  constructor
  · rintro ⟨hlflux, hrflux⟩
    constructor
    · exact nonpos_of_mul_nonpos_left hrflux hpos
    · exact nonneg_of_mul_nonpos_left hlflux hneg
  · rintro ⟨hDright, hDleft⟩
    exact ⟨mul_nonpos_of_nonneg_of_nonpos hDleft hneg.le,
      mul_nonpos_of_nonpos_of_nonneg hDright hpos.le⟩

/-- The all-root flux hypothesis for one derivative-lag term forces the
opposing exterior coefficient signs. Other summands may compensate in a
combined-flux criterion, so this conclusion is deliberately termwise. -/
theorem StrictInterl.eval_nonpos_and_nonneg_of_derivative_lag_flux
    {g f D : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    (hd : g.natDegree ≠ 0) {l r : ℝ} (hl : f.IsRoot l) (hr : f.IsRoot r)
    (hleft : ∀ t ∈ g.roots, l < t) (hright : ∀ t ∈ g.roots, t < r)
    (hflux : ∀ x, f.IsRoot x → (D * g.derivative).eval x * f.derivative.eval x ≤ 0) :
    D.eval r ≤ 0 ∧ 0 ≤ D.eval l := by
  exact (hgf.derivative_lag_flux_nonpos_iff hg hf hd hl hr hleft hright).mp
    ⟨hflux l hl, hflux r hr⟩

/-- If a term in the finite-family Liu--Wang presentation equals `D * g'`,
the theorem's interlacer, positive-leading, and coefficient-sign hypotheses
force the opposing exterior signs of `D`. No hypotheses concerning the
other summands or the output degree are needed for this necessary condition. -/
theorem StrictInterl.eval_nonpos_and_nonneg_of_finite_family_term
    {ι : Type*} {g f D : ℝ[X]} (hgf : StrictInterl g f)
    (hg : HasPosLeadingCoeff g) (hf : HasPosLeadingCoeff f)
    (hd : g.natDegree ≠ 0) {l r : ℝ} (hl : f.IsRoot l) (hr : f.IsRoot r)
    (hleft : ∀ t ∈ g.roots, l < t) (hright : ∀ t ∈ g.roots, t < r)
    {s : Finset ι} {b q : ι → ℝ[X]} {j : ι} (hj : j ∈ s)
    (hq : ∀ i ∈ s, StrictInterl (q i) f)
    (hqpos : ∀ i ∈ s, HasPosLeadingCoeff (q i))
    (hb : ∀ i ∈ s, ∀ x, f.IsRoot x → (b i).eval x ≤ 0)
    (hterm : b j * q j = D * g.derivative) :
    D.eval r ≤ 0 ∧ 0 ≤ D.eval l := by
  apply hgf.eval_nonpos_and_nonneg_of_derivative_lag_flux hg hf hd hl hr hleft hright
  intro x hx
  rw [← hterm, eval_mul, mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg (hb j hj x hx)
    ((hq j hj).eval_mul_eval_derivative_nonneg (hqpos j hj) hf hx)

end RealRooted
