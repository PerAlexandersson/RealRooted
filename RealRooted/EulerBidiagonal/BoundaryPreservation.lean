module

public import RealRooted.EulerBidiagonal.Preservation
import RealRooted.PFPolynomial.Closure

/-!
# Closed parameter boundaries for the general Euler step

The strict theorem `IsPFPolynomial.generalStep_of_natDegree_le` needs `κ, a, b > 0` and strictly
positive raising coefficients and comparison defect.  Perturbing the parameters of the operator
`κ(θ+a)(θ+b) + X(u+vθ)` by `ε > 0` and passing to the coefficientwise limit with
`IsPFPolynomial.of_coeff_tendsto` closes these boundaries (issue #2304).

* `IsPFPolynomial.generalStep_of_natDegree_le_of_comparisonDefect_nonpos`: weak parameters
  `κ > 0`, `a, b, u ≥ 0`, `u + v d ≥ 0` and `comparisonDefect ≤ 0` on `t ≤ 0`.
* `EulerBidiagonal.comparisonDefect_nonpos_iff`: the exact quadratic test
  `B ≥ 0 ∨ B² ≤ H v²`, with `B = 2u - (a+b+1)v` and `H = (a-b)² + 2(a+b) + 1`.
* `IsPFPolynomial.generalStep_of_natDegree_le_of_nonneg_or_sq_le`: the same with `κ ≥ 0`.
* `forall_isPFPolynomial_generalStep_neg_iff`: for decreasing raising coefficients
  `u - wk`, preservation in degree `≤ d` holds exactly when `w d ≤ u`.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

namespace EulerBidiagonal

/-- The coefficients of `generalStep` converge when the parameters `κ, a, b, u` converge. -/
theorem tendsto_coeff_generalStep {ι : Type*} {l : Filter ι} {κ' a' b' u' : ι → ℝ}
    {κ a b u : ℝ} (v : ℝ) (p : ℝ[X]) (i : ℕ)
    (hκ : Tendsto κ' l (𝓝 κ)) (ha : Tendsto a' l (𝓝 a)) (hb : Tendsto b' l (𝓝 b))
    (hu : Tendsto u' l (𝓝 u)) :
    Tendsto (fun j => (generalStep (κ' j) (a' j) (b' j) (u' j) v p).coeff i) l
      (𝓝 ((generalStep κ a b u v p).coeff i)) := by
  cases i with
  | zero =>
    simp only [coeff_zero_generalStep]
    exact (hκ.mul ha).mul hb |>.mul_const _
  | succ k =>
    simp only [coeff_generalStep]
    refine Tendsto.add ?_ ?_
    · exact (((hκ.mul (ha.const_add _)).mul (hb.const_add _)).mul_const _)
    · exact (hu.add_const _).mul_const _

/-- The comparison defect is `-(κ² H - 2 κ B t + v² t²) / (4 κ)`. -/
theorem comparisonDefect_eq (κ a b u v t : ℝ) (hκ : κ ≠ 0) :
    -4 * κ * comparisonDefect κ a b u v t =
      κ ^ 2 * ((a - b) ^ 2 + 2 * (a + b) + 1) - 2 * κ * (2 * u - (a + b + 1) * v) * t +
        v ^ 2 * t ^ 2 := by
  unfold comparisonDefect
  field_simp
  ring

/-- Exact test for the sign of the comparison defect on the nonpositive reals:
with `B = 2u - (a+b+1)v` and `H = (a-b)² + 2(a+b) + 1`, it is nonpositive there exactly when
`B ≥ 0` or `B² ≤ H v²`. -/
theorem comparisonDefect_nonpos_iff {κ a b u v : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∀ t ≤ 0, comparisonDefect κ a b u v t ≤ 0) ↔
      0 ≤ 2 * u - (a + b + 1) * v ∨
        (2 * u - (a + b + 1) * v) ^ 2 ≤ ((a - b) ^ 2 + 2 * (a + b) + 1) * v ^ 2 := by
  have hH : 0 ≤ (a - b) ^ 2 + 2 * (a + b) + 1 := by positivity
  generalize hB : 2 * u - (a + b + 1) * v = B
  generalize hHd : (a - b) ^ 2 + 2 * (a + b) + 1 = H at hH
  have key : ∀ t, -4 * κ * comparisonDefect κ a b u v t =
      κ ^ 2 * H - 2 * κ * B * t + v ^ 2 * t ^ 2 := by
    intro t
    rw [comparisonDefect_eq κ a b u v t hκ.ne', hB, hHd]
  have hnonpos : ∀ t, comparisonDefect κ a b u v t ≤ 0 ↔
      0 ≤ κ ^ 2 * H - 2 * κ * B * t + v ^ 2 * t ^ 2 := by
    intro t
    rw [← key]
    constructor <;> intro h <;> nlinarith
  simp only [hnonpos]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hB0, hlt⟩ := hcon
    by_cases hv : v = 0
    · have := h (κ * (H + 1) / (2 * B)) (by
        have : 0 < κ * (H + 1) := by positivity
        exact (div_neg_of_pos_of_neg this (by linarith)).le)
      subst hv
      have h2 : κ * (H + 1) / (2 * B) * (2 * B) = κ * (H + 1) := div_mul_cancel₀ _ (by linarith)
      nlinarith
    · have hv2 : 0 < v ^ 2 := by positivity
      have := h (κ * B / v ^ 2) (by
        exact (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hκ hB0) hv2).le)
      have h2 : κ * B / v ^ 2 * v ^ 2 = κ * B := div_mul_cancel₀ _ hv2.ne'
      nlinarith [mul_pos hκ hκ, sq_nonneg (v ^ 2 * (κ * B / v ^ 2) - κ * B)]
  · rintro (hB0 | hle) t ht
    · nlinarith [mul_nonneg (sq_nonneg κ) hH, mul_nonneg hκ.le hB0, sq_nonneg (v * t),
        mul_nonneg (mul_nonneg hκ.le hB0) (neg_nonneg.mpr ht)]
    · by_cases hv : v = 0
      · subst hv
        have : B = 0 := by nlinarith [sq_nonneg B]
        subst this
        nlinarith [mul_nonneg (sq_nonneg κ) hH]
      · have hv2 : 0 < v ^ 2 := by positivity
        have h1 : 0 ≤ v ^ 2 * (κ ^ 2 * H - 2 * κ * B * t + v ^ 2 * t ^ 2) := by
          nlinarith [sq_nonneg (v ^ 2 * t - κ * B), mul_nonneg (sq_nonneg κ) (sub_nonneg.mpr hle)]
        exact nonneg_of_mul_nonneg_right h1 hv2 |> fun h => by simpa using h

end EulerBidiagonal

/-- The approximating sequence `1 / (j + 1)` is positive and tends to zero. -/
private theorem tendsto_inv_succ_nat :
    Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Closed boundary theorem.**  The degree-local five-parameter Euler step preserves
Pólya-frequency polynomials for weak parameters `a, b, u ≥ 0` and `κ > 0`, provided the
raising coefficients are nonnegative on `0 ≤ k ≤ d` and the comparison defect is nonpositive
on `t ≤ 0`.  Perturbing `a, b, u` by `ε > 0` gives the strict hypotheses of
`IsPFPolynomial.generalStep_of_natDegree_le`, and `IsPFPolynomial.of_coeff_tendsto` passes to
the limit. -/
theorem IsPFPolynomial.generalStep_of_natDegree_le_of_comparisonDefect_nonpos
    {κ a b u v : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hud : 0 ≤ u + v * d)
    (hQ : ∀ t ≤ 0, EulerBidiagonal.comparisonDefect κ a b u v t ≤ 0)
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (EulerBidiagonal.generalStep κ a b u v p) := by
  set e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with he_def
  have he : Tendsto e atTop (𝓝 0) := tendsto_inv_succ_nat
  have hepos : ∀ j, 0 < e j := fun j => by simp only [he_def]; positivity
  have hraise : ∀ k : ℕ, k ≤ d → 0 ≤ u + v * k := by
    intro k hk
    have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk
    rcases le_total 0 v with hv | hv
    · nlinarith [mul_nonneg hv (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · nlinarith [mul_le_mul_of_nonpos_left hk' hv]
  refine IsPFPolynomial.of_coeff_tendsto
    (p := fun j => EulerBidiagonal.generalStep κ (a + e j) (b + e j)
      (u + e j * (1 + max v 0)) v p) (fun j => ?_) (fun i => ?_)
  · have hm : 0 ≤ max v 0 := le_max_right _ _
    refine IsPFPolynomial.generalStep_of_natDegree_le hpdeg hκ (by linarith [hepos j])
      (by linarith [hepos j]) (fun k hk => ?_) (fun t ht => ?_) hp
    · have := hraise k hk
      nlinarith [mul_pos (hepos j) (by linarith : 0 < 1 + max v 0)]
    · have hid : EulerBidiagonal.comparisonDefect κ (a + e j) (b + e j)
          (u + e j * (1 + max v 0)) v t =
          EulerBidiagonal.comparisonDefect κ a b u v t - κ * e j +
            e j * (1 + max v 0 - v) * t := by
        unfold EulerBidiagonal.comparisonDefect
        ring
      have hv : v ≤ max v 0 := le_max_left _ _
      have h1 := hQ t ht
      have h2 : e j * (1 + max v 0 - v) * t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hepos j).le (by linarith)) ht
      have h3 : 0 < κ * e j := mul_pos hκ (hepos j)
      rw [hid]
      linarith
  · refine EulerBidiagonal.tendsto_coeff_generalStep v p i tendsto_const_nhds ?_ ?_ ?_
    · simpa using (tendsto_const_nhds (x := a)).add he
    · simpa using (tendsto_const_nhds (x := b)).add he
    · simpa using (tendsto_const_nhds (x := u)).add (he.mul_const (1 + max v 0))

/-- **Closed boundary criterion.**  The degree-local five-parameter Euler step preserves
Pólya-frequency polynomials of degree at most `d` when `κ, a, b, u ≥ 0`, `u + v d ≥ 0`, and
`B ≥ 0` or `B² ≤ H v²` for `B = 2u - (a+b+1)v`, `H = (a-b)² + 2(a+b) + 1`.  For `κ = 0` this
is the limit `κ + 1/(j+1) → 0` of the case `κ > 0`. -/
theorem IsPFPolynomial.generalStep_of_natDegree_le_of_nonneg_or_sq_le
    {κ a b u v : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hud : 0 ≤ u + v * d)
    (hB : 0 ≤ 2 * u - (a + b + 1) * v ∨
      (2 * u - (a + b + 1) * v) ^ 2 ≤ ((a - b) ^ 2 + 2 * (a + b) + 1) * v ^ 2)
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (EulerBidiagonal.generalStep κ a b u v p) := by
  have hepos : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 1) := fun j => by positivity
  refine IsPFPolynomial.of_coeff_tendsto
    (p := fun j : ℕ => EulerBidiagonal.generalStep (κ + 1 / ((j : ℝ) + 1)) a b u v p)
    (fun j => ?_) (fun i => ?_)
  · exact IsPFPolynomial.generalStep_of_natDegree_le_of_comparisonDefect_nonpos hpdeg
      (by linarith [hepos j]) ha hb hu hud
      ((EulerBidiagonal.comparisonDefect_nonpos_iff (by linarith [hepos j]) ha hb).2 hB) hp
  · refine EulerBidiagonal.tendsto_coeff_generalStep v p i ?_ tendsto_const_nhds
      tendsto_const_nhds tendsto_const_nhds
    simpa using (tendsto_const_nhds (x := κ)).add tendsto_inv_succ_nat

/-- **Decreasing raising coefficients.**  For `κ, a, b, w ≥ 0`, the operator
`κ(θ+a)(θ+b) + X(u - wθ)` preserves Pólya-frequency polynomials of degree at most `d`
exactly when `w d ≤ u`.  Necessity: the image of the PF monomial `X ^ d` has coefficient
`u - w d` at `X ^ (d + 1)`. -/
theorem forall_isPFPolynomial_generalStep_neg_iff {κ a b w u : ℝ} (d : ℕ)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) :
    (∀ p : ℝ[X], p.natDegree ≤ d → IsPFPolynomial p →
      IsPFPolynomial (EulerBidiagonal.generalStep κ a b u (-w) p)) ↔ w * d ≤ u := by
  constructor
  · intro h
    have h1 := (h (X ^ d) (by simp) (isPFPolynomial_X_pow d)).hasNonnegCoeffs (d + 1)
    simp only [EulerBidiagonal.coeff_generalStep, coeff_X_pow] at h1
    simp at h1
    linarith
  · intro hwu p hpdeg hp
    have hwd : 0 ≤ w * d := mul_nonneg hw (Nat.cast_nonneg d)
    refine IsPFPolynomial.generalStep_of_natDegree_le_of_nonneg_or_sq_le hpdeg hκ ha hb
      (by linarith) (by linarith) (Or.inl ?_) hp
    nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) zero_le_one) hw]

end RealRooted
