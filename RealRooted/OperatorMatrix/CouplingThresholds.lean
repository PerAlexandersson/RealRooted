module

public import RealRooted.OperatorMatrix.LocalToGlobal

/-!
# Exact coupling thresholds for first-order operator blocks

This module formalizes the scalar ray criterion from issue #2150.  It gives a
square-root-free interface, proves its equivalence with the two-sided radical
inequality, eliminates the ray quantifier on the boundary of the quadratic
parameter cone, and records the dependence on the degree cap.

The bridge identifying this scalar criterion with bounded ordered-PF
preservation is not yet available in the library; the results here are the
unconditional algebraic core of that classification.
-/

@[expose] public section

noncomputable section

namespace RealRooted.OperatorMatrix

/-- The four nonnegative parameters of a diagonal first-order operator
`a I + b theta + X (c I + e (N I - theta))`. -/
structure CouplingDiagonal where
  a : ℝ
  b : ℝ
  c : ℝ
  e : ℝ

/-- The derivative weight `b + e t` on the negative ray `x = -t`. -/
def CouplingDiagonal.derivativeWeight (p : CouplingDiagonal) (t : ℝ) : ℝ :=
  p.b + p.e * t

/-- The diagonal evaluation `a - (c + N e) t` on the negative ray. -/
def CouplingDiagonal.diagonalEval (p : CouplingDiagonal) (N : ℕ) (t : ℝ) : ℝ :=
  p.a - (p.c + N * p.e) * t

/-- The positive quadratic `J = k₁ k₂` in the coupling criterion. -/
def couplingJ (p₁ p₂ : CouplingDiagonal) (t : ℝ) : ℝ :=
  p₁.derivativeWeight t * p₂.derivativeWeight t

/-- The signed quadratic `S = ell₂ k₁ - ell₁ k₂` in the coupling criterion. -/
def couplingS (N : ℕ) (p₁ p₂ : CouplingDiagonal) (t : ℝ) : ℝ :=
  p₂.diagonalEval N t * p₁.derivativeWeight t -
    p₁.diagonalEval N t * p₂.derivativeWeight t

/-- The exact polynomial ray predicate from issue #2150.  The first disjunction
measures violation of `0 ≤ S`; the second measures violation of `S ≤ J`. -/
def CouplingRayCriterion (J S : ℝ → ℝ) (w : ℝ) : Prop :=
  ∀ t, 0 < t →
    (0 ≤ S t ∨ (S t) ^ 2 ≤ 4 * w * t * J t) ∧
      (S t ≤ J t ∨ (J t - S t) ^ 2 ≤ 4 * w * t * J t)

/-- One side of the square-root-free ray criterion for quadratic data. -/
def QuadraticRaySide (j₀ j₁ j₂ p₀ p₁ p₂ w : ℝ) : Prop :=
  ∀ t, 0 < t →
    0 ≤ p₀ + p₁ * t + p₂ * t ^ 2 ∨
      (p₀ + p₁ * t + p₂ * t ^ 2) ^ 2 ≤
        4 * w * t * (j₀ + j₁ * t + j₂ * t ^ 2)

/-- Distance from `s` to the interval `[0, j]`, in the explicit form used by
the boundary coupling formula. -/
def couplingIntervalDistance (s j : ℝ) : ℝ :=
  max 0 (max (-s) (s - j))

private theorem lower_sqrt_iff_square {q s : ℝ} (hq : 0 ≤ q) :
    -2 * Real.sqrt q ≤ s ↔ 0 ≤ s ∨ s ^ 2 ≤ 4 * q := by
  have hsqrt : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  constructor
  · intro h
    by_cases hs : 0 ≤ s
    · exact Or.inl hs
    · right
      nlinarith
  · rintro (hs | hs)
    · nlinarith
    · nlinarith

/-- The polynomial ray predicate is exactly the original two-sided radical
inequality whenever its radicand is nonnegative. -/
theorem couplingRayCriterion_iff_sqrt_bounds (J S : ℝ → ℝ) (w : ℝ)
    (hrad : ∀ t, 0 < t → 0 ≤ w * t * J t) :
    CouplingRayCriterion J S w ↔
      ∀ t, 0 < t →
        -2 * Real.sqrt (w * t * J t) ≤ S t ∧
          S t ≤ J t + 2 * Real.sqrt (w * t * J t) := by
  constructor
  · intro h t ht
    have hsqrt := lower_sqrt_iff_square (s := S t) (hrad t ht)
    have hsqrt' := lower_sqrt_iff_square (hrad t ht) (s := J t - S t)
    have hray := h t ht
    constructor
    · rw [hsqrt]
      simpa [mul_assoc] using hray.1
    · have hu : -2 * Real.sqrt (w * t * J t) ≤ J t - S t := by
        apply hsqrt'.mpr
        rcases hray.2 with hle | hsq
        · exact Or.inl (sub_nonneg.mpr hle)
        · exact Or.inr (by simpa [mul_assoc] using hsq)
      linarith
  · intro h t ht
    have hsqrt := lower_sqrt_iff_square (s := S t) (hrad t ht)
    have hsqrt' := lower_sqrt_iff_square (hrad t ht) (s := J t - S t)
    have hb := h t ht
    constructor
    · simpa [mul_assoc] using hsqrt.mp hb.1
    · have hu : -2 * Real.sqrt (w * t * J t) ≤ J t - S t := by linarith [hb.2]
      rcases hsqrt'.mp hu with hnonneg | hsq
      · exact Or.inl (sub_nonneg.mp hnonneg)
      · exact Or.inr (by simpa [mul_assoc] using hsq)

private theorem quadraticRaySide_of_middle
    {j₀ j₁ j₂ p₀ p₁ p₂ w : ℝ}
    (hw : 0 ≤ w) (hj₀ : 0 ≤ j₀) (hj₂ : 0 ≤ j₂)
    (hp₀ : 0 ≤ p₀) (hp₂ : 0 ≤ p₂)
    (hmiddle : 0 ≤ p₁ ∨ p₁ ^ 2 ≤ 4 * w * j₁) :
    QuadraticRaySide j₀ j₁ j₂ p₀ p₁ p₂ w := by
  intro t ht
  rcases hmiddle with hp₁ | hp₁
  · left
    positivity
  by_cases hp : 0 ≤ p₀ + p₁ * t + p₂ * t ^ 2
  · exact Or.inl hp
  · right
    have ht₀ : 0 ≤ t := ht.le
    have hbound : -(p₀ + p₁ * t + p₂ * t ^ 2) ≤ -p₁ * t := by
      nlinarith [mul_nonneg hp₂ (sq_nonneg t)]
    have hneg : 0 ≤ -(p₀ + p₁ * t + p₂ * t ^ 2) := by linarith
    have hright : 0 ≤ -p₁ * t := hneg.trans hbound
    have hsq := sq_le_sq₀ hneg hright |>.mpr hbound
    nlinarith [mul_nonneg hw (mul_nonneg ht₀ hj₀),
      mul_nonneg hw (mul_nonneg (mul_nonneg ht₀ (sq_nonneg t)) hj₂)]

private theorem quadraticRaySide_middle_of_const_zero
    {j₀ j₁ j₂ p₀ p₁ p₂ w : ℝ}
    (hj₀ : j₀ = 0) (hp₀ : p₀ = 0)
    (hside : QuadraticRaySide j₀ j₁ j₂ p₀ p₁ p₂ w) :
    0 ≤ p₁ ∨ p₁ ^ 2 ≤ 4 * w * j₁ := by
  by_cases hp₁ : 0 ≤ p₁
  · exact Or.inl hp₁
  · right
    let r : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
    have hr : Filter.Tendsto r Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hneg : ∀ᶠ n in Filter.atTop, p₁ + p₂ * r n < 0 := by
      have hlim : Filter.Tendsto (fun n ↦ p₁ + p₂ * r n) Filter.atTop (nhds p₁) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hr)
      exact hlim.eventually (Iio_mem_nhds (lt_of_not_ge hp₁))
    have hineq : ∀ᶠ n in Filter.atTop,
        (p₁ + p₂ * r n) ^ 2 ≤ 4 * w * (j₁ + j₂ * r n) := by
      filter_upwards [hneg] with n hn
      have hrpos : 0 < r n := by positivity
      have hs := hside (r n) hrpos
      rcases hs with hs | hs
      · rw [hp₀] at hs
        have hprod : r n * (p₁ + p₂ * r n) < 0 := mul_neg_of_pos_of_neg hrpos hn
        nlinarith [sq_nonneg (r n)]
      · rw [hj₀, hp₀] at hs
        have hs' : (r n) ^ 2 * (p₁ + p₂ * r n) ^ 2 ≤
            (r n) ^ 2 * (4 * w * (j₁ + j₂ * r n)) := by
          convert hs using 1 <;> ring
        exact le_of_mul_le_mul_left hs' (sq_pos_of_pos hrpos)
    have hlim : Filter.Tendsto
        (fun n ↦ (p₁ + p₂ * r n) ^ 2 - 4 * w * (j₁ + j₂ * r n))
        Filter.atTop (nhds (p₁ ^ 2 - 4 * w * j₁)) := by
      have hleft : Filter.Tendsto (fun n ↦ p₁ + p₂ * r n) Filter.atTop (nhds p₁) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hr)
      have hright : Filter.Tendsto (fun n ↦ 4 * w * (j₁ + j₂ * r n))
          Filter.atTop (nhds (4 * w * j₁)) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_const_nhds.add (tendsto_const_nhds.mul hr))
      exact (hleft.pow 2).sub hright
    exact sub_nonpos.mp (le_of_tendsto hlim (hineq.mono fun _ h ↦ sub_nonpos.mpr h))

private theorem quadraticRaySide_middle_of_quad_zero
    {j₀ j₁ j₂ p₀ p₁ p₂ w : ℝ}
    (hj₂ : j₂ = 0) (hp₂ : p₂ = 0)
    (hside : QuadraticRaySide j₀ j₁ j₂ p₀ p₁ p₂ w) :
    0 ≤ p₁ ∨ p₁ ^ 2 ≤ 4 * w * j₁ := by
  by_cases hp₁ : 0 ≤ p₁
  · exact Or.inl hp₁
  · right
    let r : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
    have hr : Filter.Tendsto r Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hneg : ∀ᶠ n in Filter.atTop, p₁ + p₀ * r n < 0 := by
      have hlim : Filter.Tendsto (fun n ↦ p₁ + p₀ * r n) Filter.atTop (nhds p₁) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hr)
      exact hlim.eventually (Iio_mem_nhds (lt_of_not_ge hp₁))
    have hineq : ∀ᶠ n in Filter.atTop,
        (p₁ + p₀ * r n) ^ 2 ≤ 4 * w * (j₁ + j₀ * r n) := by
      filter_upwards [hneg] with n hn
      have hrpos : 0 < r n := by positivity
      have hinvpos : 0 < (r n)⁻¹ := inv_pos.mpr hrpos
      have hs := hside (r n)⁻¹ hinvpos
      rcases hs with hs | hs
      · rw [hp₂] at hs
        have hprod : (r n)⁻¹ * (p₁ + p₀ * r n) < 0 :=
          mul_neg_of_pos_of_neg hinvpos hn
        have hrinv : (r n)⁻¹ * r n = 1 := inv_mul_cancel₀ (ne_of_gt hrpos)
        nlinarith
      · rw [hj₂, hp₂] at hs
        have hs' : ((r n)⁻¹) ^ 2 * (p₁ + p₀ * r n) ^ 2 ≤
            ((r n)⁻¹) ^ 2 * (4 * w * (j₁ + j₀ * r n)) := by
          convert hs using 1 <;> field_simp [ne_of_gt hrpos] <;> ring
        exact le_of_mul_le_mul_left hs' (sq_pos_of_pos hinvpos)
    have hlim : Filter.Tendsto
        (fun n ↦ (p₁ + p₀ * r n) ^ 2 - 4 * w * (j₁ + j₀ * r n))
        Filter.atTop (nhds (p₁ ^ 2 - 4 * w * j₁)) := by
      have hleft : Filter.Tendsto (fun n ↦ p₁ + p₀ * r n) Filter.atTop (nhds p₁) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hr)
      have hright : Filter.Tendsto (fun n ↦ 4 * w * (j₁ + j₀ * r n))
          Filter.atTop (nhds (4 * w * j₁)) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_const_nhds.add (tendsto_const_nhds.mul hr))
      exact (hleft.pow 2).sub hright
    exact sub_nonpos.mp (le_of_tendsto hlim (hineq.mono fun _ h ↦ sub_nonpos.mpr h))

/-- On a boundary face of `J`, a quadratic violates the interval only through
its middle coefficient.  This is the one-sided form of Theorem 8 in the note. -/
theorem quadraticRaySide_iff_middle_of_boundary
    {j₀ j₁ j₂ p₀ p₁ p₂ w : ℝ}
    (hw : 0 ≤ w) (hj₀ : 0 ≤ j₀) (hj₂ : 0 ≤ j₂)
    (hp₀ : 0 ≤ p₀) (hp₀j : p₀ ≤ j₀) (hp₂ : 0 ≤ p₂) (hp₂j : p₂ ≤ j₂)
    (hboundary : j₀ * j₂ = 0) :
    QuadraticRaySide j₀ j₁ j₂ p₀ p₁ p₂ w ↔
      0 ≤ p₁ ∨ p₁ ^ 2 ≤ 4 * w * j₁ := by
  constructor
  · intro hside
    rcases mul_eq_zero.mp hboundary with hj₀z | hj₂z
    · have hp₀z : p₀ = 0 := le_antisymm (by simpa [hj₀z] using hp₀j) hp₀
      exact quadraticRaySide_middle_of_const_zero hj₀z hp₀z hside
    · have hp₂z : p₂ = 0 := le_antisymm (by simpa [hj₂z] using hp₂j) hp₂
      exact quadraticRaySide_middle_of_quad_zero hj₂z hp₂z hside
  · exact quadraticRaySide_of_middle hw hj₀ hj₂ hp₀ hp₂

/-- Complete polynomial boundary criterion; the issue's nonconstant boundary
branch specializes this theorem with `j₁ > 0`. -/
theorem couplingRayCriterion_quadratic_iff_of_boundary
    {j₀ j₁ j₂ s₀ s₁ s₂ w : ℝ}
    (hw : 0 ≤ w) (hj₀ : 0 ≤ j₀) (hj₂ : 0 ≤ j₂)
    (hs₀ : 0 ≤ s₀) (hs₀j : s₀ ≤ j₀) (hs₂ : 0 ≤ s₂) (hs₂j : s₂ ≤ j₂)
    (hboundary : j₀ * j₂ = 0) :
    CouplingRayCriterion
        (fun t ↦ j₀ + j₁ * t + j₂ * t ^ 2)
        (fun t ↦ s₀ + s₁ * t + s₂ * t ^ 2) w ↔
      (0 ≤ s₁ ∨ s₁ ^ 2 ≤ 4 * w * j₁) ∧
        (s₁ ≤ j₁ ∨ (j₁ - s₁) ^ 2 ≤ 4 * w * j₁) := by
  rw [show CouplingRayCriterion
      (fun t ↦ j₀ + j₁ * t + j₂ * t ^ 2)
      (fun t ↦ s₀ + s₁ * t + s₂ * t ^ 2) w ↔
      QuadraticRaySide j₀ j₁ j₂ s₀ s₁ s₂ w ∧
        QuadraticRaySide j₀ j₁ j₂ (j₀ - s₀) (j₁ - s₁)
          (j₂ - s₂) w by
    simp only [CouplingRayCriterion, QuadraticRaySide]
    constructor
    · intro h
      constructor
      · intro t ht
        exact (h t ht).1
      · intro t ht
        rcases (h t ht).2 with hle | hsq
        · left
          linarith
        · right
          convert hsq using 1; ring
    · rintro ⟨hlower, hupper⟩ t ht
      constructor
      · exact hlower t ht
      · rcases hupper t ht with hnonneg | hsq
        · exact Or.inl (by linarith)
        · exact Or.inr (by convert hsq using 1; ring)]
  rw [quadraticRaySide_iff_middle_of_boundary hw hj₀ hj₂ hs₀ hs₀j
      hs₂ hs₂j hboundary,
    quadraticRaySide_iff_middle_of_boundary hw hj₀ hj₂ (by linarith)
      (by linarith) (by linarith) (by linarith) hboundary]
  simp only [sub_nonneg]

private theorem middle_criterion_iff_distance_sq {s j w : ℝ}
    (hw : 0 ≤ w) (hj : 0 ≤ j) :
    (0 ≤ s ∨ s ^ 2 ≤ 4 * w * j) ∧
        (s ≤ j ∨ (j - s) ^ 2 ≤ 4 * w * j) ↔
      couplingIntervalDistance s j ^ 2 ≤ 4 * w * j := by
  by_cases hs₀ : 0 ≤ s
  · by_cases hsj : s ≤ j
    · have hdist : couplingIntervalDistance s j = 0 := by
        simp only [couplingIntervalDistance]
        rw [max_eq_left (max_le (by linarith) (by linarith))]
      have hnonneg : 0 ≤ 4 * w * j := by positivity
      simp [hs₀, hsj, hdist, hnonneg]
    · have hdist : couplingIntervalDistance s j = s - j := by
        simp only [couplingIntervalDistance]
        rw [max_eq_right (by linarith : -s ≤ s - j),
          max_eq_right (by linarith : 0 ≤ s - j)]
      simp only [hs₀, true_or, hsj, false_or, hdist]
      ring_nf
      simp only [true_and]
  · have hsj : s ≤ j := by linarith
    have hdist : couplingIntervalDistance s j = -s := by
      simp only [couplingIntervalDistance]
      rw [max_eq_left (by linarith : s - j ≤ -s),
        max_eq_right (by linarith : 0 ≤ -s)]
    simp only [hs₀, false_or, hsj, true_or, and_true, hdist]
    ring_nf

/-- On the nonconstant boundary `j₁ > 0`, the least allowed coupling is
the squared distance of `s₁` from `[0, j₁]`, divided by `4j₁`. -/
theorem couplingRayCriterion_quadratic_iff_distance_of_boundary
    {j₀ j₁ j₂ s₀ s₁ s₂ w : ℝ}
    (hw : 0 ≤ w) (hj₀ : 0 ≤ j₀) (hj₁ : 0 < j₁) (hj₂ : 0 ≤ j₂)
    (hs₀ : 0 ≤ s₀) (hs₀j : s₀ ≤ j₀) (hs₂ : 0 ≤ s₂) (hs₂j : s₂ ≤ j₂)
    (hboundary : j₀ * j₂ = 0) :
    CouplingRayCriterion
        (fun t ↦ j₀ + j₁ * t + j₂ * t ^ 2)
        (fun t ↦ s₀ + s₁ * t + s₂ * t ^ 2) w ↔
      couplingIntervalDistance s₁ j₁ ^ 2 / (4 * j₁) ≤ w := by
  rw [couplingRayCriterion_quadratic_iff_of_boundary hw hj₀ hj₂ hs₀ hs₀j
      hs₂ hs₂j hboundary,
    middle_criterion_iff_distance_sq hw hj₁.le,
    div_le_iff₀ (by positivity)]
  simp only [mul_comm, mul_left_comm]

/-- If the middle coefficient of `J` vanishes on its boundary, the ray
criterion has no coupling restriction precisely when `s₁ = 0`. -/
theorem couplingRayCriterion_quadratic_iff_middle_eq_zero
    {j₀ j₂ s₀ s₁ s₂ w : ℝ}
    (hw : 0 ≤ w) (hj₀ : 0 ≤ j₀) (hj₂ : 0 ≤ j₂)
    (hs₀ : 0 ≤ s₀) (hs₀j : s₀ ≤ j₀) (hs₂ : 0 ≤ s₂) (hs₂j : s₂ ≤ j₂)
    (hboundary : j₀ * j₂ = 0) :
    CouplingRayCriterion
        (fun t ↦ j₀ + j₂ * t ^ 2)
        (fun t ↦ s₀ + s₁ * t + s₂ * t ^ 2) w ↔
      s₁ = 0 := by
  rw [show (fun t ↦ j₀ + j₂ * t ^ 2) =
      (fun t ↦ j₀ + 0 * t + j₂ * t ^ 2) by funext t; ring,
    couplingRayCriterion_quadratic_iff_of_boundary hw hj₀ hj₂ hs₀ hs₀j
      hs₂ hs₂j hboundary]
  constructor
  · rintro ⟨hlower, hupper⟩
    rcases hlower with hlower | hlower
    · rcases hupper with hupper | hupper
      · linarith
      · nlinarith [sq_nonneg s₁]
    · nlinarith [sq_nonneg s₁]
  · rintro rfl
    simp

/-- The signed quadratic changes affinely with the degree cap. -/
theorem couplingS_cap_add (N d : ℕ) (p₁ p₂ : CouplingDiagonal) (t : ℝ) :
    couplingS (N + d) p₁ p₂ t = couplingS N p₁ p₂ t +
      d * (p₂.b * p₁.e - p₁.b * p₂.e) * t := by
  simp [couplingS, CouplingDiagonal.diagonalEval,
    CouplingDiagonal.derivativeWeight]
  ring

/-- Proportional derivative weights make the exact ray test independent of the cap. -/
theorem couplingRayCriterion_cap_add_of_proportional (N d : ℕ)
    (p₁ p₂ : CouplingDiagonal) (w : ℝ)
    (hprop : p₂.b * p₁.e = p₁.b * p₂.e) :
    CouplingRayCriterion (couplingJ p₁ p₂) (couplingS (N + d) p₁ p₂) w ↔
      CouplingRayCriterion (couplingJ p₁ p₂) (couplingS N p₁ p₂) w := by
  rw [show couplingS (N + d) p₁ p₂ = couplingS N p₁ p₂ by
    funext t
    rw [couplingS_cap_add, hprop, sub_self, mul_zero, zero_mul, add_zero]]

/-- For `T₁ = theta` and `T₂ = X (N - theta)`, the ray criterion is exactly
`N² ≤ 4uv`. -/
theorem rayCriterion_theta_polar_iff (N : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    CouplingRayCriterion (fun t ↦ t) (fun t ↦ -(N : ℝ) * t) w ↔
      (N : ℝ) ^ 2 ≤ 4 * w := by
  constructor
  · intro h
    have h1 := (h 1 zero_lt_one).1
    rcases h1 with hnonneg | hsq
    · have hN : (0 : ℝ) ≤ N := by positivity
      nlinarith
    · nlinarith
  · intro h t ht
    constructor
    · right
      have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg t)
      nlinarith
    · left
      have hN : (0 : ℝ) ≤ N := by positivity
      nlinarith

/-- Reversing the elementary diagonal operators gives the threshold
`(N - 1)² ≤ 4uv` (with subtraction in `ℝ`). -/
theorem rayCriterion_polar_theta_iff (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hN : 1 ≤ N) :
    CouplingRayCriterion (fun t ↦ t) (fun t ↦ (N : ℝ) * t) w ↔
      ((N : ℝ) - 1) ^ 2 ≤ 4 * w := by
  constructor
  · intro h
    have h1 := (h 1 zero_lt_one).2
    rcases h1 with hle | hsq
    · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have heq : (N : ℝ) = 1 := by linarith
      simp [heq, hw]
    · nlinarith
  · intro h t ht
    constructor
    · left
      positivity
    · by_cases hN : (N : ℝ) ≤ 1
      · exact Or.inl (by nlinarith)
      · right
        have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg t)
        nlinarith

end RealRooted.OperatorMatrix
