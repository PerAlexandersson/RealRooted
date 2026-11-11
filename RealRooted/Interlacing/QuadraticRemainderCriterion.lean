module

public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
import RealRooted.QuadraticRoot
import RealRooted.Interlacing.Euclid
import RealRooted.IteratedDerivativeShift
import RealRooted.Hadamard.SchurSzegoSigns
import RealRooted.MaWang.CriticalSign
import RealRooted.SymmetricDecomposition.FPolynomialSequence
import Mathlib.Tactic

/-!
# A coefficient criterion for two interlacing quadratics

Two positive-leading quadratics have the prescribed alternating root order precisely when the
linear remainder obtained by cancelling their leading terms has the indicated signs.  This avoids
quadratic root comparisons in applications.
-/

public section

open Polynomial Filter

noncomputable section

namespace RealRooted

private lemma quadratic_eval (a b c x : ℝ) :
    (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval x = a * x ^ 2 + b * x + c := by
  simp

private lemma quadratic_derivative_eval (a b c x : ℝ) :
    (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval x = 2 * a * x + b := by
  simp [derivative_add, derivative_mul, derivative_pow]
  ring

private lemma quadratic_factor_of_roots {a b c r₁ r₂ : ℝ}
    (hne : r₁ ≠ r₂)
    (hr₁ : a * r₁ ^ 2 + b * r₁ + c = 0)
    (hr₂ : a * r₂ ^ 2 + b * r₂ + c = 0) (x : ℝ) :
    a * x ^ 2 + b * x + c = a * (x - r₁) * (x - r₂) := by
  have hsum : a * (r₁ + r₂) = -b := by
    have hdiff : (r₁ - r₂) * (a * (r₁ + r₂) + b) = 0 := by
      linear_combination hr₁ - hr₂
    have : a * (r₁ + r₂) + b = 0 :=
      (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)
    linarith
  have hprod : a * (r₁ * r₂) = c := by
    linear_combination r₁ * hsum - hr₁
  rw [show b = -a * (r₁ + r₂) by nlinarith, show c = a * (r₁ * r₂) by
    nlinarith]
  ring

private lemma quadratic_pos_eventually_atTop (A B d M : ℝ) (hA : 0 < A) :
    ∃ x > M, 0 < A * x ^ 2 + B * x + d := by
  let g : ℝ[X] := C A * X ^ 2 + C B * X + C d
  have hgdeg : g.natDegree = 2 := by
    exact natDegree_quadratic hA.ne'
  have hglc : 0 < g.leadingCoeff := by
    rw [show g = C A * X ^ 2 + C B * X + C d by rfl,
      leadingCoeff_quadratic hA.ne']
    exact hA
  have hdegree : 0 < g.degree :=
    natDegree_pos_iff_degree_pos.mp (by simp [hgdeg])
  have htends := tendsto_atTop_of_leadingCoeff_nonneg g hdegree hglc.le
  obtain ⟨x, hx⟩ :=
    ((htends.eventually (eventually_gt_atTop 0)).and (eventually_gt_atTop M)).exists
  exact ⟨x, hx.2, by simpa [g, quadratic_eval] using hx.1⟩

private lemma roots_eq_of_two_distinct_roots {p : ℝ[X]} {r₁ r₂ : ℝ}
    (hpdeg : p.natDegree = 2) (hr : r₁ < r₂)
    (hr₁ : p.IsRoot r₁) (hr₂ : p.IsRoot r₂) :
    p.Splits ∧ p.roots = (↑[r₁, r₂] : Multiset ℝ) := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hpdeg]; norm_num)
  have hsplits : p.Splits := by
    apply Polynomial.splits_of_finset_roots_of_natDegree_le_card (s := {r₁, r₂})
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hr₁
      · exact hr₂
    · rw [hpdeg]
      simp [hr.ne]
  have hsub : (↑[r₁, r₂] : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (by simp [hr.ne])]
    intro x hx
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (mem_roots hp0).mpr hr₁
    · exact (mem_roots hp0).mpr hr₂
  refine ⟨hsplits, (Multiset.eq_of_le_of_card_le hsub ?_).symm⟩
  rw [Polynomial.splits_iff_card_roots.mp hsplits, hpdeg]
  simp

/-! ### Private steps in the quadratic remainder argument -/

/-- A negative value of the scaled remainder-root expression forces positive discriminant. -/
private lemma quadratic_discrim_pos_of_remainder_value_neg
    {a b c u v : ℝ} (ha : 0 < a) (hu : u < 0)
    (hN : a * v ^ 2 - b * u * v + c * u ^ 2 < 0) :
    0 < b ^ 2 - 4 * a * c := by
  have hidentity : u ^ 2 * (b ^ 2 - 4 * a * c) - (2 * a * v - b * u) ^ 2 =
      -4 * a * (a * v ^ 2 - b * u * v + c * u ^ 2) := by
    ring
  have hDmul : 0 < u ^ 2 * (b ^ 2 - 4 * a * c) := by
    nlinarith [sq_nonneg (2 * a * v - b * u)]
  exact (pos_iff_pos_of_mul_pos hDmul).mp (sq_pos_of_neg hu)

/-- A positive discriminant, together with positivity and decrease at `L`, places both
quadratic roots strictly to the right of `L`. -/
private lemma quadratic_roots_strictly_right_of_point
    {a b c L : ℝ} (ha : 0 < a) (hD : 0 < b ^ 2 - 4 * a * c)
    (hfL : 0 < a * L ^ 2 + b * L + c) (hfL' : 2 * a * L + b < 0) :
    ∃ r₁ r₂ : ℝ, L < r₁ ∧ r₁ < r₂ ∧
      a * r₁ ^ 2 + b * r₁ + c = 0 ∧ a * r₂ ^ 2 + b * r₂ + c = 0 := by
  let D := b ^ 2 - 4 * a * c
  let sqrtD := Real.sqrt D
  have hsqrtD2 : sqrtD ^ 2 = D := Real.sq_sqrt (by simpa [D] using hD.le)
  have hsqrtD : 0 < sqrtD := Real.sqrt_pos.mpr (by simpa [D] using hD)
  let r₁ := (-b - sqrtD) / (2 * a)
  let r₂ := (-b + sqrtD) / (2 * a)
  have hr₁r₂ : r₁ < r₂ := by
    dsimp [r₁, r₂]
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith
  have hsum : a * (r₁ + r₂) = -b := by
    dsimp [r₁, r₂]
    field_simp
    ring
  have hprod : a * (r₁ * r₂) = c := by
    dsimp [r₁, r₂]
    field_simp
    linear_combination (-1 : ℝ) * hsqrtD2
  have hfr₁ : a * r₁ ^ 2 + b * r₁ + c = 0 := by
    linear_combination r₁ * hsum - hprod
  have hfr₂ : a * r₂ ^ 2 + b * r₂ + c = 0 := by
    linear_combination r₂ * hsum - hprod
  have hfour := four_mul_quadratic_eq a b c L
  have hLd : 2 * a * L + b < -sqrtD := by
    have hsq : D < (2 * a * L + b) ^ 2 := by
      rw [hfour] at *
      nlinarith
    nlinarith
  have hLr₁ : L < r₁ := by
    dsimp [r₁]
    apply (lt_div_iff₀' (by positivity)).mpr
    nlinarith
  exact ⟨r₁, r₂, hLr₁, hr₁r₂, hfr₁, hfr₂⟩

/-- If the scaled value at the linear remainder's root is negative, that root lies
strictly between the two roots of the quadratic. -/
private lemma remainder_root_strictly_between_quadratic_roots
    {a b c u v r₁ r₂ : ℝ} (ha : 0 < a) (hu : u < 0)
    (hN : a * v ^ 2 - b * u * v + c * u ^ 2 < 0) (hr₁r₂ : r₁ < r₂)
    (hfr₁ : a * r₁ ^ 2 + b * r₁ + c = 0)
    (hfr₂ : a * r₂ ^ 2 + b * r₂ + c = 0) :
    ∃ z : ℝ, r₁ < z ∧ z < r₂ ∧ u * z + v = 0 := by
  let z := -v / u
  have hu0 : u ≠ 0 := hu.ne
  have huz : u * z + v = 0 := by
    dsimp [z]
    field_simp
    ring
  have hfz : a * z ^ 2 + b * z + c < 0 := by
    have hscale : u ^ 2 * (a * z ^ 2 + b * z + c) =
        a * v ^ 2 - b * u * v + c * u ^ 2 := by
      dsimp [z]
      field_simp
      ring
    have hmul : u ^ 2 * (a * z ^ 2 + b * z + c) < 0 := by
      rw [hscale]
      exact hN
    exact neg_of_mul_neg_right hmul (sq_pos_of_neg hu).le
  have hfactor : a * z ^ 2 + b * z + c = a * (z - r₁) * (z - r₂) := by
    exact quadratic_factor_of_roots hr₁r₂.ne hfr₁ hfr₂ z
  have hr₁z : r₁ < z := by
    rw [hfactor] at hfz
    by_contra h
    push Not at h
    have hz₂ : z ≤ r₂ := h.trans hr₁r₂.le
    have hnonneg : 0 ≤ a * (z - r₁) * (z - r₂) :=
      mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr h))
        (sub_nonpos.mpr hz₂)
    exact (not_lt_of_ge hnonneg) hfz
  have hzr₂ : z < r₂ := by
    rw [hfactor] at hfz
    by_contra h
    push Not at h
    have hz₁ : r₁ ≤ z := hr₁r₂.le.trans h
    have hnonneg : 0 ≤ a * (z - r₁) * (z - r₂) :=
      mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hz₁)) (sub_nonneg.mpr h)
    exact (not_lt_of_ge hnonneg) hfz
  exact ⟨z, hr₁z, hzr₂, huz⟩

/-- Cancelling the leading terms of two quadratics leaves the indicated linear remainder. -/
private lemma quadratic_leading_term_cancellation
    (a b c A B d x : ℝ) :
    a * (A * x ^ 2 + B * x + d) - A * (a * x ^ 2 + b * x + c) =
      (a * B - A * b) * x + (a * d - A * c) := by
  ring

/-- A decreasing cancelled remainder whose root lies between the first quadratic's roots
gives opposite signs for the second quadratic at those roots. -/
private lemma second_quadratic_signs_at_first_roots
    {a b c A B d r₁ r₂ z : ℝ} (ha : 0 < a) (hu : a * B - A * b < 0)
    (hr₁z : r₁ < z) (hzr₂ : z < r₂)
    (hfr₁ : a * r₁ ^ 2 + b * r₁ + c = 0)
    (hfr₂ : a * r₂ ^ 2 + b * r₂ + c = 0)
    (huz : (a * B - A * b) * z + (a * d - A * c) = 0) :
    0 < A * r₁ ^ 2 + B * r₁ + d ∧ A * r₂ ^ 2 + B * r₂ + d < 0 := by
  have hrem (x : ℝ) :
      a * (A * x ^ 2 + B * x + d) - A * (a * x ^ 2 + b * x + c) =
        (a * B - A * b) * x + (a * d - A * c) :=
    quadratic_leading_term_cancellation a b c A B d x
  constructor
  · have hlin : 0 < (a * B - A * b) * r₁ + (a * d - A * c) := by
      have heq : (a * B - A * b) * r₁ + (a * d - A * c) =
          (a * B - A * b) * (r₁ - z) := by
        linear_combination huz
      rw [heq]
      exact mul_pos_of_neg_of_neg hu (sub_neg.mpr hr₁z)
    have heq : a * (A * r₁ ^ 2 + B * r₁ + d) =
        (a * B - A * b) * r₁ + (a * d - A * c) := by
      linear_combination hrem r₁ + A * hfr₁
    have hmul : 0 < a * (A * r₁ ^ 2 + B * r₁ + d) := heq.symm ▸ hlin
    exact (pos_iff_pos_of_mul_pos hmul).mp ha
  · have hlin : (a * B - A * b) * r₂ + (a * d - A * c) < 0 := by
      have heq : (a * B - A * b) * r₂ + (a * d - A * c) =
          (a * B - A * b) * (r₂ - z) := by
        linear_combination huz
      rw [heq]
      exact mul_neg_of_neg_of_pos hu (sub_pos.mpr hzr₂)
    have heq : a * (A * r₂ ^ 2 + B * r₂ + d) =
        (a * B - A * b) * r₂ + (a * d - A * c) := by
      linear_combination hrem r₂ + A * hfr₂
    have hmul : a * (A * r₂ ^ 2 + B * r₂ + d) < 0 := heq.symm ▸ hlin
    exact neg_of_mul_neg_right hmul ha.le

/-- Opposite signs at two points and eventual positivity produce one root in the interval
and a second root to its right. -/
private lemma second_quadratic_roots_around_first_roots
    {A B d r₁ r₂ : ℝ} (hA : 0 < A) (hr₁r₂ : r₁ < r₂)
    (hgr₁ : 0 < A * r₁ ^ 2 + B * r₁ + d)
    (hgr₂ : A * r₂ ^ 2 + B * r₂ + d < 0) :
    ∃ s₁ s₂ : ℝ, r₁ < s₁ ∧ s₁ < r₂ ∧ r₂ < s₂ ∧
      A * s₁ ^ 2 + B * s₁ + d = 0 ∧ A * s₂ ^ 2 + B * s₂ + d = 0 := by
  have hcont : Continuous fun x : ℝ ↦ A * x ^ 2 + B * x + d := by fun_prop
  obtain ⟨s₁, ⟨hr₁s₁, hs₁r₂⟩, hs₁⟩ :=
    intermediate_value_Ioo' hr₁r₂.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hgr₂, hgr₁⟩)
  obtain ⟨x, hr₂x, hgx⟩ := quadratic_pos_eventually_atTop A B d r₂ hA
  obtain ⟨s₂, ⟨hr₂s₂, hs₂x⟩, hs₂⟩ :=
    intermediate_value_Ioo hr₂x.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hgr₂, hgx⟩)
  exact ⟨s₁, s₂, hr₁s₁, hs₁r₂, hr₂s₂, hs₁, hs₂⟩

/-- The four sign conditions construct roots in the order `L < r₁ < s₁ < r₂ < s₂`. -/
private theorem ordered_roots_of_quadratic_remainder_signs
    {a b c A B d L : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hu : a * B - A * b < 0)
    (hN : a * (a * d - A * c) ^ 2 - b * (a * B - A * b) * (a * d - A * c) +
      c * (a * B - A * b) ^ 2 < 0)
    (hfL : 0 < (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval L)
    (hfL' : (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval L < 0) :
    ∃ r₁ r₂ s₁ s₂ : ℝ,
      L < r₁ ∧ r₁ < s₁ ∧ s₁ < r₂ ∧ r₂ < s₂ ∧
      (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r₁ ∧
      (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r₂ ∧
      (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot s₁ ∧
      (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot s₂ := by
  let u := a * B - A * b
  let v := a * d - A * c
  have hu' : u < 0 := by simpa [u] using hu
  have hN' : a * v ^ 2 - b * u * v + c * u ^ 2 < 0 := by simpa [u, v] using hN
  have hD : 0 < b ^ 2 - 4 * a * c :=
    quadratic_discrim_pos_of_remainder_value_neg ha hu' hN'
  have hfLalg : 0 < a * L ^ 2 + b * L + c := by simpa [quadratic_eval] using hfL
  have hfL'alg : 2 * a * L + b < 0 := by
    rw [quadratic_derivative_eval] at hfL'
    exact hfL'
  obtain ⟨r₁, r₂, hLr₁, hr₁r₂, hfr₁, hfr₂⟩ :=
    quadratic_roots_strictly_right_of_point ha hD hfLalg hfL'alg
  obtain ⟨z, hr₁z, hzr₂, huz⟩ :=
    remainder_root_strictly_between_quadratic_roots ha hu' hN' hr₁r₂ hfr₁ hfr₂
  obtain ⟨hgr₁, hgr₂⟩ := second_quadratic_signs_at_first_roots ha hu hr₁z hzr₂
    hfr₁ hfr₂ (by simpa [u, v] using huz)
  obtain ⟨s₁, s₂, hr₁s₁, hs₁r₂, hr₂s₂, hs₁, hs₂⟩ :=
    second_quadratic_roots_around_first_roots hA hr₁r₂ hgr₁ hgr₂
  refine ⟨r₁, r₂, s₁, s₂, hLr₁, hr₁s₁, hs₁r₂, hr₂s₂, ?_, ?_, ?_, ?_⟩
  · simpa [Polynomial.IsRoot.def, quadratic_eval] using hfr₁
  · simpa [Polynomial.IsRoot.def, quadratic_eval] using hfr₂
  · simpa [Polynomial.IsRoot.def, quadratic_eval] using hs₁
  · simpa [Polynomial.IsRoot.def, quadratic_eval] using hs₂

private theorem quadratic_remainder_signs_of_ordered_roots
    {a b c A B d L r₁ r₂ s₁ s₂ : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hLr₁ : L < r₁) (hr₁s₁ : r₁ < s₁) (hs₁r₂ : s₁ < r₂)
    (hr₂s₂ : r₂ < s₂)
    (hfr₁ : (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r₁)
    (hfr₂ : (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r₂)
    (hgs₁ : (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot s₁)
    (hgs₂ : (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot s₂) :
    a * B - A * b < 0 ∧
      a * (a * d - A * c) ^ 2 - b * (a * B - A * b) * (a * d - A * c) +
        c * (a * B - A * b) ^ 2 < 0 ∧
      0 < (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval L ∧
      (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval L < 0 := by
  let u := a * B - A * b
  let v := a * d - A * c
  have hfr₁' : a * r₁ ^ 2 + b * r₁ + c = 0 := by
    simpa [Polynomial.IsRoot.def, quadratic_eval] using hfr₁
  have hfr₂' : a * r₂ ^ 2 + b * r₂ + c = 0 := by
    simpa [Polynomial.IsRoot.def, quadratic_eval] using hfr₂
  have hgs₁' : A * s₁ ^ 2 + B * s₁ + d = 0 := by
    simpa [Polynomial.IsRoot.def, quadratic_eval] using hgs₁
  have hgs₂' : A * s₂ ^ 2 + B * s₂ + d = 0 := by
    simpa [Polynomial.IsRoot.def, quadratic_eval] using hgs₂
  have hgfactor (x : ℝ) : A * x ^ 2 + B * x + d = A * (x - s₁) * (x - s₂) :=
    quadratic_factor_of_roots (hs₁r₂.trans hr₂s₂).ne hgs₁' hgs₂' x
  have hgr₁ : 0 < A * r₁ ^ 2 + B * r₁ + d := by
    rw [hgfactor]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg hA (sub_neg.mpr hr₁s₁))
      (sub_neg.mpr (hr₁s₁.trans (hs₁r₂.trans hr₂s₂)))
  have hgr₂ : A * r₂ ^ 2 + B * r₂ + d < 0 := by
    rw [hgfactor]
    exact mul_neg_of_pos_of_neg
      (mul_pos hA (sub_pos.mpr hs₁r₂)) (sub_neg.mpr hr₂s₂)
  have hrem (x : ℝ) :
      a * (A * x ^ 2 + B * x + d) - A * (a * x ^ 2 + b * x + c) = u * x + v := by
    dsimp [u, v]
    ring
  have hur₁ : 0 < u * r₁ + v := by nlinarith [hrem r₁]
  have hur₂ : u * r₂ + v < 0 := by nlinarith [hrem r₂]
  have hu : u < 0 := by nlinarith
  let z := -v / u
  have hu0 : u ≠ 0 := hu.ne
  have huz : u * z + v = 0 := by
    dsimp [z]
    field_simp
    ring
  have hr₁z : r₁ < z := by nlinarith
  have hzr₂ : z < r₂ := by nlinarith
  have hffactor (x : ℝ) : a * x ^ 2 + b * x + c = a * (x - r₁) * (x - r₂) :=
    quadratic_factor_of_roots (hr₁s₁.trans hs₁r₂).ne hfr₁' hfr₂' x
  have hfz : a * z ^ 2 + b * z + c < 0 := by
    rw [hffactor]
    exact mul_neg_of_pos_of_neg
      (mul_pos ha (sub_pos.mpr hr₁z)) (sub_neg.mpr hzr₂)
  have hNscale : u ^ 2 * (a * z ^ 2 + b * z + c) =
      a * v ^ 2 - b * u * v + c * u ^ 2 := by
    dsimp [z]
    field_simp
    ring
  have hN' : a * v ^ 2 - b * u * v + c * u ^ 2 < 0 := by
    rw [← hNscale]
    exact mul_neg_of_pos_of_neg (sq_pos_of_neg hu) hfz
  have hfLalg : 0 < a * L ^ 2 + b * L + c := by
    rw [hffactor]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg ha (sub_neg.mpr hLr₁))
      (sub_neg.mpr (hLr₁.trans (hr₁s₁.trans hs₁r₂)))
  have hsum : a * (r₁ + r₂) = -b := by
    have hdiff : (r₁ - r₂) * (a * (r₁ + r₂) + b) = 0 := by
      linear_combination hfr₁' - hfr₂'
    have : a * (r₁ + r₂) + b = 0 :=
      (mul_eq_zero.mp hdiff).resolve_left
        (sub_ne_zero.mpr (hr₁s₁.trans hs₁r₂).ne)
    linarith
  have hfL'alg : 2 * a * L + b < 0 := by nlinarith
  refine ⟨by simpa [u] using hu, ?_, ?_, ?_⟩
  · simpa [u, v] using hN'
  · simpa [quadratic_eval] using hfLalg
  · rw [quadratic_derivative_eval]
    exact hfL'alg

/-- Two positive-leading quadratics have roots in the strict order
`L < r₁ < s₁ < r₂ < s₂` if and only if the cancelled linear remainder has negative
slope, its root lies below the first quadratic, and the first quadratic is positive and decreasing
at `L`.  The middle coefficient expression is `u² f (-v/u)`, with
`u = aB - Ab` and `v = ad - Ac`. -/
theorem exists_ordered_quadratic_roots_iff_remainder_signs
    {a b c A B d L : ℝ} (ha : 0 < a) (hA : 0 < A) :
    (∃ r₁ r₂ s₁ s₂ : ℝ,
      L < r₁ ∧ r₁ < s₁ ∧ s₁ < r₂ ∧ r₂ < s₂ ∧
      (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r₁ ∧
      (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r₂ ∧
      (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot s₁ ∧
      (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot s₂) ↔
    a * B - A * b < 0 ∧
      a * (a * d - A * c) ^ 2 - b * (a * B - A * b) * (a * d - A * c) +
        c * (a * B - A * b) ^ 2 < 0 ∧
      0 < (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval L ∧
      (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval L < 0 := by
  constructor
  · rintro ⟨r₁, r₂, s₁, s₂, hLr₁, hr₁s₁, hs₁r₂, hr₂s₂, hfr₁, hfr₂,
      hgs₁, hgs₂⟩
    exact quadratic_remainder_signs_of_ordered_roots ha hA hLr₁ hr₁s₁ hs₁r₂
      hr₂s₂ hfr₁ hfr₂ hgs₁ hgs₂
  · rintro ⟨hu, hN, hfL, hfL'⟩
    exact ordered_roots_of_quadratic_remainder_signs ha hA hu hN hfL hfL'

/-- The quadratic remainder inequalities imply same-degree strict interlacing, simplicity of both
quadratics, and absence of common roots. -/
theorem strictInterl_quadratics_of_remainder_signs
    {a b c A B d L : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hu : a * B - A * b < 0)
    (hN : a * (a * d - A * c) ^ 2 - b * (a * B - A * b) * (a * d - A * c) +
      c * (a * B - A * b) ^ 2 < 0)
    (hfL : 0 < (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval L)
    (hfL' : (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval L < 0) :
    StrictInterl (C a * X ^ 2 + C b * X + C c)
      (C A * X ^ 2 + C B * X + C d) ∧
      HasSimpleRoots (C a * X ^ 2 + C b * X + C c : ℝ[X]) ∧
      HasSimpleRoots (C A * X ^ 2 + C B * X + C d : ℝ[X]) ∧
      ∀ r, (C a * X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r →
        ¬ (C A * X ^ 2 + C B * X + C d : ℝ[X]).IsRoot r := by
  obtain ⟨r₁, r₂, s₁, s₂, hLr₁, hr₁s₁, hs₁r₂, hr₂s₂, hfr₁, hfr₂,
      hgs₁, hgs₂⟩ := ordered_roots_of_quadratic_remainder_signs ha hA hu hN hfL hfL'
  let f : ℝ[X] := C a * X ^ 2 + C b * X + C c
  let g : ℝ[X] := C A * X ^ 2 + C B * X + C d
  have hfdeg : f.natDegree = 2 := natDegree_quadratic ha.ne'
  have hgdeg : g.natDegree = 2 := natDegree_quadratic hA.ne'
  have hfr₁' : f.IsRoot r₁ := by simpa [f] using hfr₁
  have hfr₂' : f.IsRoot r₂ := by simpa [f] using hfr₂
  have hgs₁' : g.IsRoot s₁ := by simpa [g] using hgs₁
  have hgs₂' : g.IsRoot s₂ := by simpa [g] using hgs₂
  obtain ⟨hfs, hfroots⟩ := roots_eq_of_two_distinct_roots hfdeg
    (hr₁s₁.trans hs₁r₂) hfr₁' hfr₂'
  obtain ⟨hgs, hgroots⟩ := roots_eq_of_two_distinct_roots hgdeg
    (hs₁r₂.trans hr₂s₂) hgs₁' hgs₂'
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hfdeg]; norm_num)
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hgdeg]; norm_num)
  have hinter : StrictInterl f g := by
    refine ⟨⟨hf0, hfs⟩, ⟨hg0, hgs⟩, [r₁, r₂], [s₁, s₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [le_of_lt (hr₁s₁.trans hs₁r₂)]
    · simp [le_of_lt (hs₁r₂.trans hr₂s₂)]
    · exact hfroots.symm
    · exact hgroots.symm
    · exact Or.inr ⟨by simp, by
        simp [ListAlternates, ListInterlaces, hr₁s₁.le, hs₁r₂.le, hr₂s₂.le]⟩
  have hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hfr hgr
    have hfrmem : r ∈ f.roots := (mem_roots hf0).mpr hfr
    have hgrmem : r ∈ g.roots := (mem_roots hg0).mpr hgr
    rw [hfroots] at hfrmem
    rw [hgroots] at hgrmem
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hfrmem hgrmem
    rcases hfrmem with rfl | rfl <;> rcases hgrmem with rfl | rfl <;> nlinarith
  have hsimple := hinter.hasSimpleRoots_of_no_common_root fun r hr ↦ hno r hr.1 hr.2
  refine ⟨by simpa [f, g] using hinter, by simpa [f] using hsimple.1,
    by simpa [g] using hsimple.2, ?_⟩
  intro r hfr hgr
  exact hno r (by simpa [f] using hfr) (by simpa [g] using hgr)

/-- Under the quadratic remainder inequalities, adjoining the distinguished root `L` to the
second quadratic gives differ-by-one interlacing. -/
theorem interlaces_quadratic_mul_X_sub_C_of_remainder_signs
    {a b c A B d L : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hu : a * B - A * b < 0)
    (hN : a * (a * d - A * c) ^ 2 - b * (a * B - A * b) * (a * d - A * c) +
      c * (a * B - A * b) ^ 2 < 0)
    (hfL : 0 < (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval L)
    (hfL' : (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval L < 0) :
    Interlaces (C a * X ^ 2 + C b * X + C c)
      ((X - C L) * (C A * X ^ 2 + C B * X + C d)) := by
  obtain ⟨r₁, r₂, s₁, s₂, hLr₁, hr₁s₁, hs₁r₂, hr₂s₂, hfr₁, hfr₂,
      hgs₁, hgs₂⟩ := ordered_roots_of_quadratic_remainder_signs ha hA hu hN hfL hfL'
  let f : ℝ[X] := C a * X ^ 2 + C b * X + C c
  let g : ℝ[X] := C A * X ^ 2 + C B * X + C d
  have hfdeg : f.natDegree = 2 := natDegree_quadratic ha.ne'
  have hgdeg : g.natDegree = 2 := natDegree_quadratic hA.ne'
  have hfr₁' : f.IsRoot r₁ := by simpa [f] using hfr₁
  have hfr₂' : f.IsRoot r₂ := by simpa [f] using hfr₂
  have hgs₁' : g.IsRoot s₁ := by simpa [g] using hgs₁
  have hgs₂' : g.IsRoot s₂ := by simpa [g] using hgs₂
  obtain ⟨hfs, hfroots⟩ := roots_eq_of_two_distinct_roots hfdeg
    (hr₁s₁.trans hs₁r₂) hfr₁' hfr₂'
  obtain ⟨hgs, hgroots⟩ := roots_eq_of_two_distinct_roots hgdeg
    (hs₁r₂.trans hr₂s₂) hgs₁' hgs₂'
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hfdeg]; norm_num)
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hgdeg]; norm_num)
  have hprod0 : (X - C L) * g ≠ 0 := mul_ne_zero (X_sub_C_ne_zero L) hg0
  have hprods : ((X - C L) * g).Splits := (Splits.X_sub_C L).mul hgs
  have hproddeg : ((X - C L) * g).natDegree = 3 := by
    rw [natDegree_mul (X_sub_C_ne_zero L) hg0, hgdeg]
    simp
  have hprodroots : ((X - C L) * g).roots = (↑[L, s₁, s₂] : Multiset ℝ) := by
    rw [roots_mul hprod0, roots_X_sub_C, hgroots]
    simp
  simpa [f, g] using Interlaces.of_quadratic_cubic_root_lists
    (g := f) (f := (X - C L) * g) hprod0 hprods hf0 hfs hproddeg hfdeg hprodroots hfroots
    (hLr₁.trans hr₁s₁).le (hs₁r₂.trans hr₂s₂).le
    (hr₁s₁.trans hs₁r₂).le hLr₁.le
    hr₁s₁.le hs₁r₂.le hr₂s₂.le

/-! ## The normalized one-parameter family -/

/-- The monic quadratic family obtained from the issue's family by dividing by its positive
leading coefficient and writing `y = 1 / (t - 1)`. -/
@[expose] def normalizedQuadraticFamily (y : ℝ) : ℝ[X] :=
  C 1 * X ^ 2 + C ((6 + 11 * y - 3 * y ^ 2) / 7) * X +
    C ((1 + 3 * y + 3 * y ^ 2) / 7)

private lemma normalizedQuadraticFamily_natDegree (y : ℝ) :
    (normalizedQuadraticFamily y).natDegree = 2 := by
  exact natDegree_quadratic one_ne_zero

private lemma normalizedQuadraticFamily_monic (y : ℝ) :
    (normalizedQuadraticFamily y).Monic := by
  rw [Monic.def, leadingCoeff, normalizedQuadraticFamily_natDegree]
  simp [normalizedQuadraticFamily]

private lemma normalizedQuadraticFamily_nextCoeff (y : ℝ) :
    (normalizedQuadraticFamily y).nextCoeff = (6 + 11 * y - 3 * y ^ 2) / 7 := by
  rw [nextCoeff, normalizedQuadraticFamily_natDegree]
  simp [normalizedQuadraticFamily]

private lemma normalizedQuadraticFamily_discrim_pos {y : ℝ}
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) :
    0 < discrim (1 : ℝ) ((6 + 11 * y - 3 * y ^ 2) / 7)
      ((1 + 3 * y + 3 * y ^ 2) / 7) := by
  let b := (6 + 11 * y - 3 * y ^ 2) / 7
  let c := (1 + 3 * y + 3 * y ^ 2) / 7
  have hyfac : 0 ≤ y * (1 - 3 * y) :=
    mul_nonneg hy₀ (by nlinarith)
  have hmid : (1 : ℝ) * (-1 / 2 : ℝ) ^ 2 + b * (-1 / 2) + c < 0 := by
    have heq : (1 : ℝ) * (-1 / 2 : ℝ) ^ 2 + b * (-1 / 2) + c =
        (-1 - 4 * y - 6 * y * (1 - 3 * y)) / 28 := by
      dsimp [b, c]
      ring
    rw [heq]
    nlinarith
  have hfour := four_mul_quadratic_eq (1 : ℝ) b c (-1 / 2)
  have hdisc : 0 < discrim (1 : ℝ) b c :=
    by nlinarith [sq_nonneg (2 * (1 : ℝ) * (-1 / 2) + b)]
  simpa only [b, c] using hdisc

private lemma normalizedQuadraticFamily_splits {y : ℝ}
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) :
    (normalizedQuadraticFamily y).Splits := by
  have hdisc := normalizedQuadraticFamily_discrim_pos hy₀ hy₁
  simpa only [normalizedQuadraticFamily] using
    quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc.le

private lemma normalizedQuadraticFamily_strictInterl_of_lt
    {y z : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1 / 3) (hz₀ : 0 ≤ z) (hzy : z < y) :
    StrictInterl (normalizedQuadraticFamily y) (normalizedQuadraticFamily z) ∧
      ∃ r₁ r₂ s₁ s₂ : ℝ,
        -1 < r₁ ∧ r₁ < s₁ ∧ s₁ < r₂ ∧ r₂ < s₂ ∧
        (normalizedQuadraticFamily y).IsRoot r₁ ∧
        (normalizedQuadraticFamily y).IsRoot r₂ ∧
        (normalizedQuadraticFamily z).IsRoot s₁ ∧
        (normalizedQuadraticFamily z).IsRoot s₂ := by
  let b_y := (6 + 11 * y - 3 * y ^ 2) / 7
  let cy := (1 + 3 * y + 3 * y ^ 2) / 7
  let bz := (6 + 11 * z - 3 * z ^ 2) / 7
  let cz := (1 + 3 * z + 3 * z ^ 2) / 7
  let s := y + z
  let m := 11 - 3 * s
  let k := 3 * (1 + s)
  let q := -1 - 6 * s + 9 * s ^ 2 - (33 - 9 * s) * y * z
  have hs₀ : 0 ≤ s := by dsimp [s]; positivity
  have hs₁ : s < 2 / 3 := by dsimp [s]; nlinarith
  have hm : 0 < m := by dsimp [m]; nlinarith
  have hq : q < 0 := by
    have hsquare : 9 * s ^ 2 ≤ 6 * s := by nlinarith [mul_nonneg hs₀ (by nlinarith)]
    have hlast : 0 ≤ (33 - 9 * s) * y * z :=
      mul_nonneg (mul_nonneg (by nlinarith) hy₀) hz₀
    dsimp [q]
    nlinarith
  have hu_eq : bz - b_y = (z - y) * m / 7 := by
    dsimp [b_y, bz, m, s]
    ring
  have hv_eq : cz - cy = (z - y) * k / 7 := by
    dsimp [cy, cz, k, s]
    ring
  have hu : bz - b_y < 0 := by
    rw [hu_eq]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hzy) hm) (by norm_num)
  have hN_eq : (cz - cy) ^ 2 - b_y * (bz - b_y) * (cz - cy) +
      cy * (bz - b_y) ^ 2 = 2 * (z - y) ^ 2 / 49 * q := by
    rw [hu_eq, hv_eq]
    dsimp [b_y, cy, m, k, q, s]
    ring
  have hN : (cz - cy) ^ 2 - b_y * (bz - b_y) * (cz - cy) +
      cy * (bz - b_y) ^ 2 < 0 := by
    rw [hN_eq]
    exact mul_neg_of_pos_of_neg
      (div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (sub_ne_zero.mpr hzy.ne))) (by norm_num))
      hq
  have hfL_eq : (C 1 * X ^ 2 + C b_y * X + C cy : ℝ[X]).eval (-1) =
      2 * (1 - y) * (1 - 3 * y) / 7 := by
    simp [b_y, cy]
    ring
  have hfL : 0 < (C 1 * X ^ 2 + C b_y * X + C cy : ℝ[X]).eval (-1) := by
    rw [hfL_eq]
    exact div_pos (mul_pos (mul_pos (by norm_num) (by nlinarith)) (by nlinarith)) (by norm_num)
  have hfL'_eq : (C 1 * X ^ 2 + C b_y * X + C cy : ℝ[X]).derivative.eval (-1) =
      -(1 - y) * (8 - 3 * y) / 7 := by
    rw [quadratic_derivative_eval]
    dsimp [b_y]
    ring
  have hfL' : (C 1 * X ^ 2 + C b_y * X + C cy : ℝ[X]).derivative.eval (-1) < 0 := by
    rw [hfL'_eq]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (by nlinarith)) (by nlinarith)) (by norm_num)
  have hpackage :=
    strictInterl_quadratics_of_remainder_signs (a := 1) (b := b_y) (c := cy)
      (A := 1) (B := bz) (d := cz) (L := -1) (by norm_num) (by norm_num)
      (by simpa using hu) (by simpa using hN) hfL hfL'
  have hordered :=
    (exists_ordered_quadratic_roots_iff_remainder_signs
      (a := 1) (b := b_y) (c := cy) (A := 1) (B := bz) (d := cz) (L := -1)
      (by norm_num) (by norm_num)).mpr ⟨by simpa using hu, by simpa using hN, hfL, hfL'⟩
  constructor
  · simpa only [normalizedQuadraticFamily, b_y, cy, bz, cz] using hpackage.1
  · simpa only [normalizedQuadraticFamily, b_y, cy, bz, cz] using hordered

/-- For `0 ≤ z < y < 1/3`, the roots of `H_y` and `H_z` occur in the strict order
`-1 < r₁(y) < r₁(z) < r₂(y) < r₂(z)`. -/
theorem normalizedQuadraticFamily_exists_ordered_roots
    {y z : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1 / 3) (hz₀ : 0 ≤ z) (hzy : z < y) :
    ∃ r₁ r₂ s₁ s₂ : ℝ,
      -1 < r₁ ∧ r₁ < s₁ ∧ s₁ < r₂ ∧ r₂ < s₂ ∧
      (normalizedQuadraticFamily y).IsRoot r₁ ∧
      (normalizedQuadraticFamily y).IsRoot r₂ ∧
      (normalizedQuadraticFamily z).IsRoot s₁ ∧
      (normalizedQuadraticFamily z).IsRoot s₂ :=
  (normalizedQuadraticFamily_strictInterl_of_lt hy₀ hy₁ hz₀ hzy).2

private lemma normalizedQuadraticFamily_one_third_strictInterl
    {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1 / 3) :
    StrictInterl (normalizedQuadraticFamily (1 / 3)) (normalizedQuadraticFamily z) := by
  let f := normalizedQuadraticFamily (1 / 3)
  let g := normalizedQuadraticFamily z
  have hf_eq : f = (X + C 1) * (X + C (1 / 3)) := by
    dsimp [f, normalizedQuadraticFamily]
    norm_num
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, map_add]
    simp only [C_1]
    ring
  have hfs : f.Splits := by
    rw [hf_eq]
    exact (Splits.X_add_C 1).mul (Splits.X_add_C (1 / 3))
  have hfpos : HasPosLeadingCoeff f := by
    rw [hf_eq]
    exact (hasPosLeadingCoeff_of_monic (monic_X_add_C 1)).mul
      (hasPosLeadingCoeff_of_monic (monic_X_add_C (1 / 3)))
  have hgpos : HasPosLeadingCoeff g := by
    exact hasPosLeadingCoeff_of_monic (normalizedQuadraticFamily_monic z)
  have hfdeg : f.natDegree = 2 := by
    dsimp [f]
    exact normalizedQuadraticFamily_natDegree _
  have hgdeg : g.natDegree = 2 := by
    dsimp [g]
    exact normalizedQuadraticFamily_natDegree _
  apply strictInterl_of_eval_mul_derivative_neg hfs hfpos hgpos
    (by rw [hfdeg]; norm_num)
    (by rw [hfdeg, hgdeg])
    (by rw [hfdeg, hgdeg]; norm_num)
  intro r hr
  have hr' : (r + 1) * (r + 1 / 3) = 0 := by
    rw [hf_eq, Polynomial.IsRoot.def] at hr
    simpa using hr
  rcases mul_eq_zero.mp hr' with hr | hr
  · have hre : r = -1 := by linarith
    subst r
    have hge : 0 < g.eval (-1) := by
      dsimp [g, normalizedQuadraticFamily]
      simp only [map_one, one_mul, eval_add, eval_pow, eval_X, even_two, Even.neg_pow,
        one_pow, eval_mul, eval_C, mul_neg, mul_one]
      have : 0 < (1 - z) * (1 - 3 * z) := mul_pos (by linarith) (by linarith)
      nlinarith
    have hfder : f.derivative.eval (-1) < 0 := by
      rw [hf_eq]
      norm_num [derivative_mul, derivative_add]
    exact mul_neg_of_pos_of_neg hge hfder
  · have hre : r = -(1 / 3) := by linarith
    subst r
    have hge : g.eval (-(1 / 3)) < 0 := by
      dsimp [g, normalizedQuadraticFamily]
      simp only [one_div, map_one, one_mul, eval_add, eval_pow, eval_X, even_two,
        Even.neg_pow, inv_pow, eval_mul, eval_C, mul_neg]
      have : (3 * z - 1) * (6 * z + 1) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by positivity)
      nlinarith
    have hfder : 0 < f.derivative.eval (-(1 / 3)) := by
      rw [hf_eq]
      norm_num [derivative_mul, derivative_add]
    exact mul_neg_of_neg_of_pos hge hfder

/-- Every member of the normalized family on `[0, 1/3]` splits with two distinct roots, and all
of its roots belong to `[-1, 0)`. -/
theorem normalizedQuadraticFamily_splits_simple_roots_mem_Ico
    {y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) :
    (normalizedQuadraticFamily y).Splits ∧
      HasSimpleRoots (normalizedQuadraticFamily y) ∧
      ∀ r ∈ (normalizedQuadraticFamily y).roots, -1 ≤ r ∧ r < 0 := by
  let b := (6 + 11 * y - 3 * y ^ 2) / 7
  let c := (1 + 3 * y + 3 * y ^ 2) / 7
  have hdisc : 0 < discrim (1 : ℝ) b c := by
    simpa only [b, c] using normalizedQuadraticFamily_discrim_pos hy₀ hy₁
  have hsplits : (normalizedQuadraticFamily y).Splits :=
    normalizedQuadraticFamily_splits hy₀ hy₁
  have hne : normalizedQuadraticFamily y ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [normalizedQuadraticFamily_natDegree]; norm_num)
  have hrootFormula : (normalizedQuadraticFamily y).roots =
      {(-b - Real.sqrt (b ^ 2 - 4 * c)) / 2,
        (-b + Real.sqrt (b ^ 2 - 4 * c)) / 2} := by
    simpa [normalizedQuadraticFamily, b, c] using
      roots_quadratic_posLead (a := 1) (b := b) (c := c) one_pos (by simpa [discrim] using hdisc.le)
  have hsqrt : 0 < Real.sqrt (b ^ 2 - 4 * c) := by
    apply Real.sqrt_pos.mpr
    simpa [discrim] using hdisc
  have hsimple : HasSimpleRoots (normalizedQuadraticFamily y) := by
    apply HasSimpleRoots.of_roots_nodup hne
    rw [hrootFormula]
    simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, and_true]
    intro h
    have : Real.sqrt (b ^ 2 - 4 * c) = 0 := by linarith
    linarith
  have hbpos : 0 < b := by
    dsimp [b]
    nlinarith [sq_nonneg y]
  have hcpos : 0 < c := by
    dsimp [c]
    nlinarith [sq_nonneg y]
  have hble : b ≤ 4 / 3 := by
    have hfac : 0 ≤ (1 / 3 - y) * (10 - 3 * y) :=
      mul_nonneg (sub_nonneg.mpr hy₁) (by nlinarith)
    dsimp [b]
    nlinarith
  have hnegOne : 0 ≤ (1 : ℝ) - b + c := by
    have heq : (1 : ℝ) - b + c = 2 * (1 - y) * (1 - 3 * y) / 7 := by
      dsimp [b, c]
      ring
    rw [heq]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by nlinarith)) (by nlinarith)) (by norm_num)
  refine ⟨hsplits, hsimple, ?_⟩
  intro r hr
  have hroot : r ^ 2 + b * r + c = 0 := by
    have := (mem_roots hne).mp hr
    simpa [normalizedQuadraticFamily, b, c] using this
  constructor
  · by_contra h
    push Not at h
    have hsecond : r - 1 + b < 0 := by nlinarith
    have hdiff : 0 < (r + 1) * (r - 1 + b) :=
      mul_pos_of_neg_of_neg (by linarith) hsecond
    have hid : r ^ 2 + b * r + c - ((1 : ℝ) - b + c) =
        (r + 1) * (r - 1 + b) := by ring
    nlinarith
  · by_contra h
    push Not at h
    have hnonneg : 0 ≤ r ^ 2 + b * r :=
      add_nonneg (sq_nonneg r) (mul_nonneg hbpos.le h)
    nlinarith

/-- On the parameter interval `[0, 1/3]`, the normalized quadratics are in oriented
same-degree proper position exactly when the second parameter is at most the first. -/
theorem normalizedQuadraticFamily_strictInterl_iff
    {y z : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1 / 3) :
    StrictInterl (normalizedQuadraticFamily y) (normalizedQuadraticFamily z) ↔ z ≤ y := by
  constructor
  · intro h
    have hcoeff := h.nextCoeff_le_of_sameDegree_monic
      (normalizedQuadraticFamily_monic y) (normalizedQuadraticFamily_monic z)
      (by simp [normalizedQuadraticFamily_natDegree])
    have hcoeff' : (6 + 11 * z - 3 * z ^ 2) / 7 ≤
        (6 + 11 * y - 3 * y ^ 2) / 7 := by
      simpa only [normalizedQuadraticFamily_nextCoeff] using hcoeff
    have hm : 0 < 11 - 3 * (y + z) := by nlinarith
    have hprod : 0 ≤ (y - z) * (11 - 3 * (y + z)) := by
      nlinarith
    have hprod' : 0 ≤ (11 - 3 * (y + z)) * (y - z) := by
      simpa only [mul_comm] using hprod
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod' hm)
  · intro hzy
    by_cases hzy' : z = y
    · subst z
      exact StrictInterl.refl
        (ne_zero_of_natDegree_gt (n := 0) (by rw [normalizedQuadraticFamily_natDegree]; norm_num))
        (normalizedQuadraticFamily_splits hy₀ hy₁)
    · have hzylt : z < y := lt_of_le_of_ne hzy hzy'
      by_cases hy : y = 1 / 3
      · subst y
        exact normalizedQuadraticFamily_one_third_strictInterl hz₀ hzylt
      · exact (normalizedQuadraticFamily_strictInterl_of_lt hy₀
          (lt_of_le_of_ne hy₁ hy) hz₀ hzylt).1

/-- If `z ≤ y` on `[0, 1/3]`, adjoining the root `-1` to the `z`-quadratic gives
differ-by-one interlacing with the `y`-quadratic. -/
theorem normalizedQuadraticFamily_interlaces_mul_X_add_one_of_le
    {y z : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1 / 3)
    (hzy : z ≤ y) :
    Interlaces (normalizedQuadraticFamily y)
      ((X + C 1) * normalizedQuadraticFamily z) := by
  have hydata := normalizedQuadraticFamily_splits_simple_roots_mem_Ico hy₀ hy₁
  have hzdata := normalizedQuadraticFamily_splits_simple_roots_mem_Ico hz₀ hz₁
  have hy0 : normalizedQuadraticFamily y ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [normalizedQuadraticFamily_natDegree]; norm_num)
  have hz0 : normalizedQuadraticFamily z ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [normalizedQuadraticFamily_natDegree]; norm_num)
  have hsame := (normalizedQuadraticFamily_strictInterl_iff hy₀ hy₁ hz₀ hz₁).mpr hzy
  have hfactor : StrictInterl (normalizedQuadraticFamily y)
      ((X - C (-1)) * normalizedQuadraticFamily z) :=
    StrictInterl.of_mul_X_sub_C_right_of_roots_ge
      ⟨hy0, hydata.1⟩ ⟨hz0, hzdata.1⟩
      (by simp [normalizedQuadraticFamily_natDegree])
      (fun r hr ↦ (hydata.2.2 r hr).1) (fun r hr ↦ (hzdata.2.2 r hr).1) hsame
  have hdeg : (normalizedQuadraticFamily y).natDegree + 1 =
      ((X - C (-1)) * normalizedQuadraticFamily z).natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero (-1)) hz0]
    simp [normalizedQuadraticFamily_natDegree]
  simpa only [map_neg, map_one, neg_neg, sub_neg_eq_add] using hfactor.toInterlaces hdeg

private lemma strictInterl_of_interlaces_mul_X_add_one
    {f g : ℝ[X]} (h : Interlaces f ((X + C 1) * g))
    (hg₀ : g ≠ 0) (hgs : g.Splits)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 2)
    (hgroots : ∀ r ∈ g.roots, -1 ≤ r) :
    StrictInterl f g := by
  rcases h with ⟨hprod, hf, _, rs, ss, hrs, hss, hrsRoots, hssRoots, hint⟩
  let sg := g.roots.sort (· ≤ ·)
  have hsg : sg.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hsgRoots : (↑sg : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hminusOneSg : (-1 :: sg).Pairwise (· ≤ ·) := by
    simp only [List.pairwise_cons]
    refine ⟨?_, hsg⟩
    intro r hr
    apply hgroots r
    rw [← hsgRoots]
    exact Multiset.mem_coe.mpr hr
  have hprod₀ : (X + C 1) * g ≠ 0 := mul_ne_zero (X_add_C_ne_zero 1) hg₀
  have hprodRoots : ((X + C 1) * g).roots = (↑(-1 :: sg) : Multiset ℝ) := by
    rw [roots_mul hprod₀, roots_X_add_C]
    rw [← hsgRoots]
    simp
  have hrsPerm : rs.Perm (-1 :: sg) := by
    apply Multiset.coe_eq_coe.mp
    rw [hrsRoots, hprodRoots]
  have hrsEq : rs = -1 :: sg :=
    List.Perm.eq_of_pairwise' hrs hminusOneSg hrsPerm
  have hssLen : ss.length = 2 := by
    rw [← Multiset.coe_card, hssRoots, Polynomial.splits_iff_card_roots.mp hf.2, hfdeg]
  have hsgLen : sg.length = 2 := by
    rw [← Multiset.coe_card, hsgRoots, Polynomial.splits_iff_card_roots.mp hgs, hgdeg]
  have halt : ListAlternates ss sg := by
    rw [hrsEq] at hint
    exact listAlternates_of_listInterlaces_cons hint
  exact ⟨hf, ⟨hg₀, hgs⟩, ss, sg, hss, hsg, hssRoots, hsgRoots,
    Or.inr ⟨by rw [hssLen, hsgLen], halt⟩⟩

/-- On `[0, 1/3]`, `H_y` interlaces `(X + 1) H_z` exactly when `z ≤ y`. -/
theorem normalizedQuadraticFamily_interlaces_mul_X_add_one_iff
    {y z : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1 / 3) :
    Interlaces (normalizedQuadraticFamily y)
      ((X + C 1) * normalizedQuadraticFamily z) ↔ z ≤ y := by
  constructor
  · intro h
    have hzdata := normalizedQuadraticFamily_splits_simple_roots_mem_Ico hz₀ hz₁
    have hz0 : normalizedQuadraticFamily z ≠ 0 :=
      ne_zero_of_natDegree_gt (n := 0)
        (by rw [normalizedQuadraticFamily_natDegree]; norm_num)
    have hsame := strictInterl_of_interlaces_mul_X_add_one h hz0 hzdata.1
      (normalizedQuadraticFamily_natDegree y) (normalizedQuadraticFamily_natDegree z)
      (fun r hr ↦ (hzdata.2.2 r hr).1)
    exact (normalizedQuadraticFamily_strictInterl_iff hy₀ hy₁ hz₀ hz₁).mp hsame
  · exact normalizedQuadraticFamily_interlaces_mul_X_add_one_of_le hy₀ hy₁ hz₀ hz₁

/-- Consecutive rows `(X + 1)^n H_{y_n}` and `(X + 1)^(n+1) H_{y_{n+1}}`
interlace exactly when the parameter sequence decreases at `n`. -/
theorem normalizedQuadraticRows_interlaces_iff
    (y : ℕ → ℝ) (hy₀ : ∀ n, 0 ≤ y n) (hy₁ : ∀ n, y n ≤ 1 / 3) (n : ℕ) :
    Interlaces ((X + C 1) ^ n * normalizedQuadraticFamily (y n))
      ((X + C 1) ^ (n + 1) * normalizedQuadraticFamily (y (n + 1))) ↔
      y (n + 1) ≤ y n := by
  let f := normalizedQuadraticFamily (y n)
  let g := normalizedQuadraticFamily (y (n + 1))
  have hfdeg : f.natDegree = 2 := normalizedQuadraticFamily_natDegree _
  have hgdeg : g.natDegree = 2 := normalizedQuadraticFamily_natDegree _
  have hg₀ : g ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hgdeg]; norm_num)
  constructor
  · intro h
    have hstrict : StrictInterl ((X - C (-1 : ℝ)) ^ n * f)
        ((X - C (-1 : ℝ)) ^ n * ((X - C (-1 : ℝ)) * g)) := by
      simpa only [f, g, map_neg, map_one, neg_neg, sub_neg_eq_add, pow_succ,
        mul_assoc] using h.toStrictInterl
    have hbase : StrictInterl f ((X - C (-1 : ℝ)) * g) :=
      strictInterl_of_strictInterl_mul_pow_X_sub_C_both (-1) n hstrict
    have hrightdeg : ((X - C (-1 : ℝ)) * g).natDegree = 3 := by
      rw [natDegree_mul (X_sub_C_ne_zero (-1)) hg₀, hgdeg]
      simp
    have hbaseInter : Interlaces f ((X - C (-1 : ℝ)) * g) :=
      hbase.toInterlaces (by rw [hfdeg, hrightdeg])
    have hplus : Interlaces (normalizedQuadraticFamily (y n))
        ((X + C 1) * normalizedQuadraticFamily (y (n + 1))) := by
      simpa only [f, g, map_neg, map_one, neg_neg, sub_neg_eq_add] using hbaseInter
    exact (normalizedQuadraticFamily_interlaces_mul_X_add_one_iff
      (hy₀ n) (hy₁ n) (hy₀ (n + 1)) (hy₁ (n + 1))).mp hplus
  · intro hle
    have hbase := (normalizedQuadraticFamily_interlaces_mul_X_add_one_iff
      (hy₀ n) (hy₁ n) (hy₀ (n + 1)) (hy₁ (n + 1))).mpr hle
    have hfactorSplits : ((X + C 1) ^ n : ℝ[X]).Splits := (Splits.X_add_C 1).pow n
    have hfactor₀ : ((X + C 1) ^ n : ℝ[X]) ≠ 0 :=
      pow_ne_zero n (X_add_C_ne_zero 1)
    simpa only [pow_succ, mul_assoc] using
      hbase.mul_both_of_splits hfactorSplits hfactor₀

/-- Every row `(X + 1)^n H_y` has degree `n + 2`, positive coefficients through its
degree, and all roots in `[-1, 0)`. -/
theorem normalizedQuadraticRow_degree_coeff_roots
    {y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1 / 3) (n : ℕ) :
    ((X + C 1) ^ n * normalizedQuadraticFamily y).natDegree = n + 2 ∧
      (∀ k ≤ n + 2, 0 < ((X + C 1) ^ n * normalizedQuadraticFamily y).coeff k) ∧
      ∀ r ∈ ((X + C 1) ^ n * normalizedQuadraticFamily y).roots, -1 ≤ r ∧ r < 0 := by
  let q : ℝ[X] := (X + C 1) ^ n
  let h := normalizedQuadraticFamily y
  have hdata := normalizedQuadraticFamily_splits_simple_roots_mem_Ico hy₀ hy₁
  have h₀ : h ≠ 0 := ne_zero_of_natDegree_gt (n := 0)
    (by dsimp [h]; rw [normalizedQuadraticFamily_natDegree]; norm_num)
  have q₀ : q ≠ 0 := pow_ne_zero n (X_add_C_ne_zero 1)
  have qs : q.Splits := (Splits.X_add_C 1).pow n
  have qdeg : q.natDegree = n := by
    dsimp [q]
    rw [natDegree_pow]
    simp
  have hdeg : h.natDegree = 2 := by
    dsimp [h]
    exact normalizedQuadraticFamily_natDegree _
  have hrow₀ : q * h ≠ 0 := mul_ne_zero q₀ h₀
  have hrowSplits : (q * h).Splits := qs.mul hdata.1
  have hrowDeg : (q * h).natDegree = n + 2 := by
    rw [natDegree_mul q₀ h₀, qdeg, hdeg]
  have hrowRoots : ∀ r ∈ (q * h).roots, -1 ≤ r ∧ r < 0 := by
    intro r hr
    rw [roots_mul hrow₀] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · have hre : r = -1 := by
        dsimp [q] at hr
        rw [roots_pow, roots_X_add_C] at hr
        exact (by simpa using hr : n ≠ 0 ∧ r = -1).2
      simp [hre]
    · exact hdata.2.2 r hr
  have hrowMonic : (q * h).Monic := by
    exact (monic_X_add_C 1).pow n |>.mul (normalizedQuadraticFamily_monic y)
  have hcoeff : ∀ k ≤ n + 2, 0 < (q * h).coeff k := by
    intro k hk
    have hsign := leadingCoeff_mul_coeff_pos_of_roots_neg hrowSplits hrow₀
      (fun r hr ↦ (hrowRoots r hr).2) (by simpa [hrowDeg] using hk)
    simpa [hrowMonic.leadingCoeff] using hsign
  simpa only [q, h] using ⟨hrowDeg, hcoeff, hrowRoots⟩

end RealRooted
