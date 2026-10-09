import RealRooted.Mathlib.Algebra.LinearRecurrence.Asymptotics

/-!
# Mean and variance asymptotics for three-term polynomial recurrences

For `P (n + 2) = a * P (n + 1) + b * P n` with `a b : ℝ[X]` independent of `n`, let `λ > |ν|`
be the roots of `t² = a(1) t + b(1)`.  The values `P n (1)`, `P n '(1)` and `P n ''(1)` satisfy
scalar (forced) recurrences whose closed forms are derived here, and the mean and variance of the
coefficient distribution of `P n` grow linearly: `μ_n / n → λ'/λ` and `σ_n² / n → λ''/λ + λ'/λ −
(λ'/λ)²`, where `λ(x)` is the dominant root of `t² = a(x) t + b(x)` (Bender's formulas, here in an
algebraic form at `x = 1`).
-/

open Filter Topology
open scoped Polynomial

namespace RealRooted.ThreeTermRecurrence

/-- The coefficient of the dominant root in the value closed form. -/
noncomputable def dominantCoeff (P : ℕ → ℝ[X]) (lam nu : ℝ) : ℝ :=
  ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu)

/-- The coefficient of the second root in the value closed form. -/
noncomputable def companionCoeff (P : ℕ → ℝ[X]) (lam nu : ℝ) : ℝ :=
  (lam * (P 0).eval 1 - (P 1).eval 1) / (lam - nu)

/-- The logarithmic first derivative of a root, given algebraically. -/
noncomputable def rootLogSlope (a b : ℝ[X]) (lam : ℝ) : ℝ :=
  (a.derivative.eval 1 * lam + b.derivative.eval 1) /
    (lam * (2 * lam - a.eval 1))

/-- The quotient `lambda'' / lambda`, given by twice differentiating the root
equation algebraically. -/
noncomputable def rootLogSecond (a b : ℝ[X]) (lam : ℝ) : ℝ :=
  (a.derivative.derivative.eval 1 * lam + b.derivative.derivative.eval 1 +
      2 * a.derivative.eval 1 * (rootLogSlope a b lam * lam) -
      2 * (rootLogSlope a b lam * lam) ^ 2) /
    (lam * (2 * lam - a.eval 1))

/-- The dominant first-derivative mode coefficient. -/
noncomputable def derivativeDominantCoeff (P : ℕ → ℝ[X]) (a b : ℝ[X])
    (lam nu : ℝ) : ℝ :=
  dominantCoeff P lam nu * rootLogSlope a b lam

/-- The companion first-derivative mode coefficient. -/
noncomputable def derivativeCompanionCoeff (P : ℕ → ℝ[X]) (a b : ℝ[X])
    (lam nu : ℝ) : ℝ :=
  companionCoeff P lam nu * rootLogSlope a b nu

/-- The constant part of the dominant first-derivative mode. -/
noncomputable def derivativeDominantConstant (P : ℕ → ℝ[X]) (a b : ℝ[X])
    (lam nu : ℝ) : ℝ :=
  ((P 1).derivative.eval 1 - derivativeDominantCoeff P a b lam nu * lam -
      derivativeCompanionCoeff P a b lam nu * nu -
      nu * (P 0).derivative.eval 1) / (lam - nu)

/-- The constant part of the companion first-derivative mode. -/
noncomputable def derivativeCompanionConstant (P : ℕ → ℝ[X]) (a b : ℝ[X])
    (lam nu : ℝ) : ℝ :=
  (P 0).derivative.eval 1 - derivativeDominantConstant P a b lam nu

/-- The dominant quadratic mode coefficient. -/
noncomputable def secondDominantCoeff (P : ℕ → ℝ[X]) (a b : ℝ[X]) (lam nu : ℝ) : ℝ :=
  dominantCoeff P lam nu * rootLogSlope a b lam ^ 2

/-- The companion quadratic mode coefficient. -/
noncomputable def secondCompanionCoeff (P : ℕ → ℝ[X]) (a b : ℝ[X]) (lam nu : ℝ) : ℝ :=
  companionCoeff P lam nu * rootLogSlope a b nu ^ 2

/-- The linear dominant second-derivative mode coefficient. -/
noncomputable def secondDominantLinear (P : ℕ → ℝ[X]) (a b : ℝ[X]) (lam nu : ℝ) : ℝ :=
  dominantCoeff P lam nu * (rootLogSecond a b lam - rootLogSlope a b lam ^ 2) +
    2 * derivativeDominantConstant P a b lam nu * rootLogSlope a b lam

/-- The linear companion second-derivative mode coefficient. -/
noncomputable def secondCompanionLinear (P : ℕ → ℝ[X]) (a b : ℝ[X]) (lam nu : ℝ) : ℝ :=
  companionCoeff P lam nu * (rootLogSecond a b nu - rootLogSlope a b nu ^ 2) +
    2 * derivativeCompanionConstant P a b lam nu * rootLogSlope a b nu

/-- The constant part of the dominant second-derivative mode. -/
noncomputable def secondDominantConstant (P : ℕ → ℝ[X]) (a b : ℝ[X]) (lam nu : ℝ) : ℝ :=
  ((P 1).derivative.derivative.eval 1 -
      (secondDominantCoeff P a b lam nu + secondDominantLinear P a b lam nu) * lam -
      (secondCompanionCoeff P a b lam nu + secondCompanionLinear P a b lam nu) * nu -
      nu * (P 0).derivative.derivative.eval 1) / (lam - nu)

/-- The constant part of the companion second-derivative mode. -/
noncomputable def secondCompanionConstant (P : ℕ → ℝ[X]) (a b : ℝ[X])
    (lam nu : ℝ) : ℝ :=
  (P 0).derivative.derivative.eval 1 - secondDominantConstant P a b lam nu

/-- The asymptotic mean slope at a dominant root. -/
noncomputable def meanSlope (a b : ℝ[X]) (lam : ℝ) : ℝ := rootLogSlope a b lam

/-- The asymptotic variance slope at a dominant root. -/
noncomputable def varianceSlope (a b : ℝ[X]) (lam : ℝ) : ℝ :=
  rootLogSecond a b lam + rootLogSlope a b lam - rootLogSlope a b lam ^ 2

end RealRooted.ThreeTermRecurrence

namespace RealRooted.ThreeTermRecurrence

private theorem root_sum_product {p q lam nu : ℝ}
    (hLam : lam ^ 2 = p * lam + q) (hNu : nu ^ 2 = p * nu + q)
    (hDistinct : lam ≠ nu) : lam + nu = p ∧ lam * nu = -q := by
  have hfactor : (lam - nu) * (lam + nu - p) = 0 := by
    calc
      (lam - nu) * (lam + nu - p) =
          (lam ^ 2 - p * lam - q) - (nu ^ 2 - p * nu - q) := by ring
      _ = 0 := by rw [hLam, hNu]; ring
  have hsum : lam + nu = p := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact False.elim (hDistinct (sub_eq_zero.mp h))
    · linarith
  constructor
  · exact hsum
  · calc
      lam * nu = lam * (p - lam) := by linear_combination lam * hsum
      _ = -q := by nlinarith [hLam]

private theorem value_closed_form {P : ℕ → ℝ[X]} {a b : ℝ[X]}
    {lam nu : ℝ} (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) :
    ∀ n, (P n).eval 1 = dominantCoeff P lam nu * lam ^ n +
      companionCoeff P lam nu * nu ^ n := by
  let S : ℕ → ℝ := fun n => (P n).eval 1
  have hS : ∀ n, S (n + 2) = a.eval 1 * S (n + 1) + b.eval 1 * S n := by
    intro n
    dsimp [S]
    exact Polynomial.eval_one_recurrence hP n
  obtain ⟨hsum, hprod⟩ :=
    root_sum_product hLam hNu hDistinct
  have h0 : S 0 = dominantCoeff P lam nu + companionCoeff P lam nu := by
    dsimp [S]
    unfold dominantCoeff companionCoeff
    field_simp [hDistinct]
    ring
  have h1 : S 1 = dominantCoeff P lam nu * lam +
      companionCoeff P lam nu * nu := by
    dsimp [S]
    unfold dominantCoeff companionCoeff
    field_simp [hDistinct]
    ring
  have hform := LinearRecurrence.two_mode_solution hS hsum hprod h0 h1
  intro n
  exact hform n

private theorem derivative_closed_form {P : ℕ → ℝ[X]} {a b : ℝ[X]}
    {lam nu : ℝ} (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hLamNe : lam ≠ 0) (hNuNe : nu ≠ 0)
    (hSimple : 2 * lam - a.eval 1 ≠ 0) :
    ∀ n, (P n).derivative.eval 1 =
      (derivativeDominantCoeff P a b lam nu * (n : ℝ) +
          derivativeDominantConstant P a b lam nu) * lam ^ n +
        (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
          derivativeCompanionConstant P a b lam nu) * nu ^ n := by
  let S : ℕ → ℝ := fun n => (P n).eval 1
  let T : ℕ → ℝ := fun n => (P n).derivative.eval 1
  have hS : ∀ n, S n = dominantCoeff P lam nu * lam ^ n +
      companionCoeff P lam nu * nu ^ n := by
    intro n
    exact value_closed_form hP hLam hNu hDistinct n
  obtain ⟨hsum, hprod⟩ := root_sum_product hLam hNu hDistinct
  have hnuSimple : 2 * nu - a.eval 1 ≠ 0 := by
    intro h
    apply hDistinct
    linarith [hsum]
  have hSimple' : lam * 2 - a.eval 1 ≠ 0 := by
    intro h
    apply hSimple
    linarith
  have hnuSimple' : nu * 2 - a.eval 1 ≠ 0 := by
    intro h
    apply hnuSimple
    linarith
  have hT : ∀ n, T (n + 2) = a.eval 1 * T (n + 1) + b.eval 1 * T n +
      a.derivative.eval 1 * S (n + 1) + b.derivative.eval 1 * S n := by
    intro n
    dsimp [S, T]
    rw [Polynomial.derivative_eval_one_recurrence hP n]
    ring
  have hα : derivativeDominantCoeff P a b lam nu * lam *
      (2 * lam - a.eval 1) = dominantCoeff P lam nu *
        (a.derivative.eval 1 * lam + b.derivative.eval 1) := by
    unfold derivativeDominantCoeff rootLogSlope
    field_simp [hLamNe, hSimple']
  have hγ : derivativeCompanionCoeff P a b lam nu * nu *
      (2 * nu - a.eval 1) = companionCoeff P lam nu *
        (a.derivative.eval 1 * nu + b.derivative.eval 1) := by
    unfold derivativeCompanionCoeff rootLogSlope
    field_simp [hNuNe, hnuSimple']
  have hβ : derivativeDominantConstant P a b lam nu =
      ((P 1).derivative.eval 1 - derivativeDominantCoeff P a b lam nu * lam -
        derivativeCompanionCoeff P a b lam nu * nu -
        nu * (P 0).derivative.eval 1) / (lam - nu) := by
    rfl
  have hδ : derivativeCompanionConstant P a b lam nu =
      (P 0).derivative.eval 1 - derivativeDominantConstant P a b lam nu := by
    rfl
  have hinit := LinearRecurrence.two_mode_linear_initial_values hβ hδ hDistinct
  have h0 : T 0 = derivativeDominantConstant P a b lam nu +
      derivativeCompanionConstant P a b lam nu := by
    dsimp [T]
    exact hinit.1
  have h1 : T 1 =
      (derivativeDominantCoeff P a b lam nu +
        derivativeDominantConstant P a b lam nu) * lam +
      (derivativeCompanionCoeff P a b lam nu +
        derivativeCompanionConstant P a b lam nu) * nu := by
    dsimp [T]
    exact hinit.2
  have hform := LinearRecurrence.forced_linear_two_mode_solution hT hsum hprod hS hα hγ h0 h1
  intro n
  exact hform n

private theorem second_derivative_closed_form {P : ℕ → ℝ[X]} {a b : ℝ[X]}
    {lam nu : ℝ} (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hLamNe : lam ≠ 0) (hNuNe : nu ≠ 0)
    (hSimple : 2 * lam - a.eval 1 ≠ 0) :
    ∀ n, (P n).derivative.derivative.eval 1 =
      (secondDominantCoeff P a b lam nu * (n : ℝ) ^ 2 +
          secondDominantLinear P a b lam nu * (n : ℝ) +
          secondDominantConstant P a b lam nu) * lam ^ n +
        (secondCompanionCoeff P a b lam nu * (n : ℝ) ^ 2 +
          secondCompanionLinear P a b lam nu * (n : ℝ) +
          secondCompanionConstant P a b lam nu) * nu ^ n := by
  let S : ℕ → ℝ := fun n => (P n).eval 1
  let T : ℕ → ℝ := fun n => (P n).derivative.eval 1
  let U : ℕ → ℝ := fun n => (P n).derivative.derivative.eval 1
  have hS : ∀ n, S n = dominantCoeff P lam nu * lam ^ n +
      companionCoeff P lam nu * nu ^ n := by
    intro n
    exact value_closed_form hP hLam hNu hDistinct n
  have hT : ∀ n, T n =
      (derivativeDominantCoeff P a b lam nu * (n : ℝ) +
        derivativeDominantConstant P a b lam nu) * lam ^ n +
      (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
        derivativeCompanionConstant P a b lam nu) * nu ^ n := by
    intro n
    exact derivative_closed_form hP hLam hNu hDistinct hLamNe hNuNe hSimple n
  obtain ⟨hsum, hprod⟩ := root_sum_product hLam hNu hDistinct
  have hnuSimple : 2 * nu - a.eval 1 ≠ 0 := by
    intro h
    apply hDistinct
    linarith [hsum]
  have hSimple' : lam * 2 - a.eval 1 ≠ 0 := by
    intro h
    apply hSimple
    linarith
  have hnuSimple' : nu * 2 - a.eval 1 ≠ 0 := by
    intro h
    apply hnuSimple
    linarith
  have hU : ∀ n, U (n + 2) =
      a.eval 1 * U (n + 1) + b.eval 1 * U n +
        a.derivative.derivative.eval 1 * S (n + 1) +
        2 * a.derivative.eval 1 * T (n + 1) +
        b.derivative.derivative.eval 1 * S n + 2 * b.derivative.eval 1 * T n := by
    intro n
    dsimp [S, T, U]
    rw [Polynomial.derivative_derivative_eval_one_recurrence hP n]
    ring
  have hroot1 : rootLogSlope a b lam * lam *
      (2 * lam - a.eval 1) = a.derivative.eval 1 * lam + b.derivative.eval 1 := by
    unfold rootLogSlope
    field_simp [hLamNe, hSimple']
  have hroot2 : rootLogSecond a b lam * lam *
      (2 * lam - a.eval 1) = a.derivative.derivative.eval 1 * lam +
        b.derivative.derivative.eval 1 +
        2 * a.derivative.eval 1 * (rootLogSlope a b lam * lam) -
        2 * (rootLogSlope a b lam * lam) ^ 2 := by
    unfold rootLogSecond
    field_simp [hLamNe, hSimple']
  have hroot1' : rootLogSlope a b nu * nu *
      (2 * nu - a.eval 1) = a.derivative.eval 1 * nu + b.derivative.eval 1 := by
    unfold rootLogSlope
    field_simp [hNuNe, hnuSimple']
  have hroot2' : rootLogSecond a b nu * nu *
      (2 * nu - a.eval 1) = a.derivative.derivative.eval 1 * nu +
        b.derivative.derivative.eval 1 +
        2 * a.derivative.eval 1 * (rootLogSlope a b nu * nu) -
        2 * (rootLogSlope a b nu * nu) ^ 2 := by
    unfold rootLogSecond
    field_simp [hNuNe, hnuSimple']
  have hη : secondDominantCoeff P a b lam nu * lam *
      (2 * lam - a.eval 1) = derivativeDominantCoeff P a b lam nu *
        (a.derivative.eval 1 * lam + b.derivative.eval 1) := by
    unfold secondDominantCoeff derivativeDominantCoeff
    linear_combination dominantCoeff P lam nu * rootLogSlope a b lam * hroot1
  have hθ : secondDominantCoeff P a b lam nu * lam *
      (4 * lam - a.eval 1) + secondDominantLinear P a b lam nu * lam *
      (2 * lam - a.eval 1) =
      dominantCoeff P lam nu *
        (a.derivative.derivative.eval 1 * lam + b.derivative.derivative.eval 1) +
        2 * a.derivative.eval 1 * lam *
          (derivativeDominantCoeff P a b lam nu +
            derivativeDominantConstant P a b lam nu) +
        2 * b.derivative.eval 1 * derivativeDominantConstant P a b lam nu := by
    unfold secondDominantLinear secondDominantCoeff derivativeDominantCoeff
    linear_combination dominantCoeff P lam nu * hroot2 +
      2 * derivativeDominantConstant P a b lam nu * hroot1
  have hζ : secondCompanionCoeff P a b lam nu * nu *
      (2 * nu - a.eval 1) = derivativeCompanionCoeff P a b lam nu *
        (a.derivative.eval 1 * nu + b.derivative.eval 1) := by
    unfold secondCompanionCoeff derivativeCompanionCoeff
    linear_combination companionCoeff P lam nu * rootLogSlope a b nu * hroot1'
  have hξ : secondCompanionCoeff P a b lam nu * nu *
      (4 * nu - a.eval 1) + secondCompanionLinear P a b lam nu * nu *
      (2 * nu - a.eval 1) =
      companionCoeff P lam nu *
        (a.derivative.derivative.eval 1 * nu + b.derivative.derivative.eval 1) +
        2 * a.derivative.eval 1 * nu *
          (derivativeCompanionCoeff P a b lam nu +
            derivativeCompanionConstant P a b lam nu) +
        2 * b.derivative.eval 1 * derivativeCompanionConstant P a b lam nu := by
    unfold secondCompanionLinear secondCompanionCoeff derivativeCompanionCoeff
    linear_combination companionCoeff P lam nu * hroot2' +
      2 * derivativeCompanionConstant P a b lam nu * hroot1'
  have h0 : U 0 = secondDominantConstant P a b lam nu +
      secondCompanionConstant P a b lam nu := by
    dsimp [U]
    unfold secondCompanionConstant
    ring
  have hκ : secondDominantConstant P a b lam nu =
      ((P 1).derivative.derivative.eval 1 -
        (secondDominantCoeff P a b lam nu + secondDominantLinear P a b lam nu) * lam -
        (secondCompanionCoeff P a b lam nu + secondCompanionLinear P a b lam nu) * nu -
        nu * (P 0).derivative.derivative.eval 1) / (lam - nu) := by
    rfl
  have hχ : secondCompanionConstant P a b lam nu =
      (P 0).derivative.derivative.eval 1 - secondDominantConstant P a b lam nu := by
    rfl
  have hinit := LinearRecurrence.two_mode_quadratic_initial_values hκ hχ hDistinct
  have h1 : U 1 =
      (secondDominantCoeff P a b lam nu +
        secondDominantLinear P a b lam nu +
        secondDominantConstant P a b lam nu) * lam +
      (secondCompanionCoeff P a b lam nu +
        secondCompanionLinear P a b lam nu +
        secondCompanionConstant P a b lam nu) * nu := by
    dsimp [U]
    exact hinit.2
  have hform := LinearRecurrence.forced_quadratic_two_mode_solution hU hsum hprod hS hT
    hη hθ hζ hξ h0 h1
  intro n
  exact hform n

/-- Mean asymptotics for a polynomial three-term recurrence with an explicitly
given two-mode closed form. -/
private theorem mean_from_modes
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hDominant : 0 < lam) (hModulus : |nu| < lam)
    (hA : dominantCoeff P lam nu ≠ 0)
    (hValue : ∀ n, (P n).eval 1 =
      dominantCoeff P lam nu * lam ^ n + companionCoeff P lam nu * nu ^ n)
    (hDerivative : ∀ n, (P n).derivative.eval 1 =
      (derivativeDominantCoeff P a b lam nu * (n : ℝ) +
          derivativeDominantConstant P a b lam nu) * lam ^ n +
        (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
          derivativeCompanionConstant P a b lam nu) * nu ^ n) :
    Tendsto (fun n => (P n).derivative.eval 1 /
      ((n : ℝ) * (P n).eval 1)) atTop
      (𝓝 (meanSlope a b lam)) := by
  have hlam : lam ≠ 0 := ne_of_gt hDominant
  have hratio : |nu / lam| < 1 := by
    rw [abs_div, abs_of_pos hDominant]
    apply (div_lt_iff₀ hDominant).2
    simpa only [one_mul] using hModulus
  have hden : Tendsto (fun n : ℕ =>
      dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n)
      atTop (𝓝 (dominantCoeff P lam nu)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (f := atTop) (x := dominantCoeff P lam nu)).add
        ((tendsto_const_nhds (f := atTop) (x := companionCoeff P lam nu)).mul
          (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio))
  have hden_ne : ∀ᶠ n : ℕ in atTop,
      dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n ≠ 0 :=
    hden.eventually_ne hA
  have hsub := LinearRecurrence.linear_ratio_tendsto
    (A := dominantCoeff P lam nu) (B := companionCoeff P lam nu)
    (α := derivativeDominantCoeff P a b lam nu)
    (β := derivativeDominantConstant P a b lam nu)
    (γ := derivativeCompanionCoeff P a b lam nu)
    (δ := derivativeCompanionConstant P a b lam nu) (r := nu / lam) hA hratio
  have hpow : ∀ n : ℕ, lam ^ n ≠ 0 := fun n => pow_ne_zero n hlam
  have hfactor : ∀ n : ℕ,
      (P n).eval 1 = lam ^ n *
        (dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n) := by
    intro n
    rw [hValue n]
    rw [div_pow]
    field_simp [hlam]
  have hfactor' : ∀ n : ℕ,
      (P n).derivative.eval 1 = lam ^ n *
        (((derivativeDominantCoeff P a b lam nu * (n : ℝ) +
            derivativeDominantConstant P a b lam nu)) +
          (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
            derivativeCompanionConstant P a b lam nu) * (nu / lam) ^ n) := by
    intro n
    rw [hDerivative n]
    rw [div_pow]
    field_simp [hlam]
  have hsub' : Tendsto (fun n : ℕ =>
      (P n).derivative.eval 1 / (P n).eval 1 -
        derivativeDominantCoeff P a b lam nu /
          dominantCoeff P lam nu * (n : ℝ)) atTop
      (𝓝 (derivativeDominantConstant P a b lam nu /
        dominantCoeff P lam nu)) := by
    have heq : ∀ᶠ n : ℕ in atTop,
        ((derivativeDominantCoeff P a b lam nu * (n : ℝ) +
            derivativeDominantConstant P a b lam nu) +
          (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
            derivativeCompanionConstant P a b lam nu) * (nu / lam) ^ n) /
            (dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n) -
          derivativeDominantCoeff P a b lam nu /
            dominantCoeff P lam nu * (n : ℝ) =
        (P n).derivative.eval 1 / (P n).eval 1 -
          derivativeDominantCoeff P a b lam nu /
            dominantCoeff P lam nu * (n : ℝ) := by
      filter_upwards [hden_ne] with n hn
      have hp : (P n).eval 1 ≠ 0 := by
        rw [hfactor n]
        exact mul_ne_zero (hpow n) hn
      rw [hfactor' n, hfactor n]
      field_simp [hpow n, hn, hp]
    exact hsub.congr' heq
  have hdiv := LinearRecurrence.tendsto_div_nat_of_tendsto_sub_linear hsub'
  have heq : ∀ᶠ n : ℕ in atTop,
      (P n).derivative.eval 1 / ((n : ℝ) * (P n).eval 1) =
        ((P n).derivative.eval 1 / (P n).eval 1) / (n : ℝ) := by
    filter_upwards [hden_ne, eventually_ge_atTop 1] with n hn hpos
    have hp : (P n).eval 1 ≠ 0 := by
      rw [hfactor n]
      exact mul_ne_zero (hpow n) hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    field_simp [hp, hn']
  have heq' :
      (fun n : ℕ => ((P n).derivative.eval 1 / (P n).eval 1) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (P n).derivative.eval 1 / ((n : ℝ) * (P n).eval 1)) :=
    heq.mono fun _ h => h.symm
  have hlim := hdiv.congr' heq'
  convert hlim using 1
  congr 1
  unfold meanSlope derivativeDominantCoeff
  field_simp [hA]

/-- Variance asymptotics for the same polynomial recurrence and explicit
two-mode value, first-derivative, and second-derivative closed forms. -/
private theorem variance_from_modes
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hDominant : 0 < lam) (hModulus : |nu| < lam)
    (hA : dominantCoeff P lam nu ≠ 0)
    (hValue : ∀ n, (P n).eval 1 =
      dominantCoeff P lam nu * lam ^ n + companionCoeff P lam nu * nu ^ n)
    (hDerivative : ∀ n, (P n).derivative.eval 1 =
      (derivativeDominantCoeff P a b lam nu * (n : ℝ) +
          derivativeDominantConstant P a b lam nu) * lam ^ n +
        (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
          derivativeCompanionConstant P a b lam nu) * nu ^ n)
    (hSecond : ∀ n, (P n).derivative.derivative.eval 1 =
      (secondDominantCoeff P a b lam nu * (n : ℝ) ^ 2 +
          secondDominantLinear P a b lam nu * (n : ℝ) +
          secondDominantConstant P a b lam nu) * lam ^ n +
        (secondCompanionCoeff P a b lam nu * (n : ℝ) ^ 2 +
          secondCompanionLinear P a b lam nu * (n : ℝ) +
          secondCompanionConstant P a b lam nu) * nu ^ n) :
    Tendsto (fun n =>
      ((P n).derivative.derivative.eval 1 / (P n).eval 1 +
          (P n).derivative.eval 1 / (P n).eval 1 -
          ((P n).derivative.eval 1 / (P n).eval 1) ^ 2) / (n : ℝ)) atTop
      (𝓝 (varianceSlope a b lam)) := by
  have hlam : lam ≠ 0 := ne_of_gt hDominant
  have hratio : |nu / lam| < 1 := by
    rw [abs_div, abs_of_pos hDominant]
    apply (div_lt_iff₀ hDominant).2
    simpa only [one_mul] using hModulus
  have hden : Tendsto (fun n : ℕ =>
      dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n)
      atTop (𝓝 (dominantCoeff P lam nu)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (f := atTop) (x := dominantCoeff P lam nu)).add
        ((tendsto_const_nhds (f := atTop) (x := companionCoeff P lam nu)).mul
          (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio))
  have hden_ne : ∀ᶠ n : ℕ in atTop,
      dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n ≠ 0 :=
    hden.eventually_ne hA
  have hpow : ∀ n : ℕ, lam ^ n ≠ 0 := fun n => pow_ne_zero n hlam
  have hfactor : ∀ n : ℕ,
      (P n).eval 1 = lam ^ n *
        (dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n) := by
    intro n
    rw [hValue n, div_pow]
    field_simp [hlam]
  have hfactor' : ∀ n : ℕ,
      (P n).derivative.eval 1 = lam ^ n *
        ((derivativeDominantCoeff P a b lam nu * (n : ℝ) +
            derivativeDominantConstant P a b lam nu) +
          (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
            derivativeCompanionConstant P a b lam nu) * (nu / lam) ^ n) := by
    intro n
    rw [hDerivative n, div_pow]
    field_simp [hlam]
  have hfactor'' : ∀ n : ℕ,
      (P n).derivative.derivative.eval 1 = lam ^ n *
        ((secondDominantCoeff P a b lam nu * (n : ℝ) ^ 2 +
            secondDominantLinear P a b lam nu * (n : ℝ) +
            secondDominantConstant P a b lam nu) +
          (secondCompanionCoeff P a b lam nu * (n : ℝ) ^ 2 +
            secondCompanionLinear P a b lam nu * (n : ℝ) +
            secondCompanionConstant P a b lam nu) * (nu / lam) ^ n) := by
    intro n
    rw [hSecond n, div_pow]
    field_simp [hlam]
  have hquad : secondDominantCoeff P a b lam nu /
      dominantCoeff P lam nu = meanSlope a b lam ^ 2 := by
    unfold secondDominantCoeff meanSlope
    field_simp [hA]
  have hsigma : varianceSlope a b lam =
      secondDominantLinear P a b lam nu / dominantCoeff P lam nu +
        meanSlope a b lam - 2 * meanSlope a b lam *
          (derivativeDominantConstant P a b lam nu /
            dominantCoeff P lam nu) := by
    unfold varianceSlope secondDominantLinear meanSlope
    field_simp [hA]
    ring
  have hvar := LinearRecurrence.variance_ratio_tendsto
    (A := dominantCoeff P lam nu) (B := companionCoeff P lam nu)
    (α := derivativeDominantCoeff P a b lam nu)
    (β := derivativeDominantConstant P a b lam nu)
    (γ := derivativeCompanionCoeff P a b lam nu)
    (δ := derivativeCompanionConstant P a b lam nu)
    (η := secondDominantCoeff P a b lam nu)
    (θ := secondDominantLinear P a b lam nu)
    (κ := secondDominantConstant P a b lam nu)
    (ζ := secondCompanionCoeff P a b lam nu)
    (ξ := secondCompanionLinear P a b lam nu)
    (χ := secondCompanionConstant P a b lam nu)
    (r := nu / lam) (m := meanSlope a b lam)
    (c := derivativeDominantConstant P a b lam nu /
      dominantCoeff P lam nu) (σ := varianceSlope a b lam)
    hA hratio (by
      unfold meanSlope derivativeDominantCoeff
      field_simp [hA]) (by rfl) hquad hsigma
  let N2 : ℕ → ℝ := fun n =>
    ((secondDominantCoeff P a b lam nu * (n : ℝ) ^ 2 +
        secondDominantLinear P a b lam nu * (n : ℝ) +
        secondDominantConstant P a b lam nu) +
      (secondCompanionCoeff P a b lam nu * (n : ℝ) ^ 2 +
        secondCompanionLinear P a b lam nu * (n : ℝ) +
        secondCompanionConstant P a b lam nu) * (nu / lam) ^ n) /
      (dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n)
  let N1 : ℕ → ℝ := fun n =>
    ((derivativeDominantCoeff P a b lam nu * (n : ℝ) +
        derivativeDominantConstant P a b lam nu) +
      (derivativeCompanionCoeff P a b lam nu * (n : ℝ) +
        derivativeCompanionConstant P a b lam nu) * (nu / lam) ^ n) /
      (dominantCoeff P lam nu + companionCoeff P lam nu * (nu / lam) ^ n)
  have hnorm : Tendsto (fun n : ℕ =>
      N2 n + N1 n - N1 n ^ 2 - varianceSlope a b lam * (n : ℝ)) atTop
      (𝓝 (secondDominantConstant P a b lam nu /
        dominantCoeff P lam nu +
        derivativeDominantConstant P a b lam nu /
          dominantCoeff P lam nu -
        (derivativeDominantConstant P a b lam nu /
          dominantCoeff P lam nu) ^ 2)) := by
    simpa only [N1, N2] using hvar
  have hvar' : Tendsto (fun n : ℕ =>
      ((P n).derivative.derivative.eval 1 / (P n).eval 1 +
          (P n).derivative.eval 1 / (P n).eval 1 -
          ((P n).derivative.eval 1 / (P n).eval 1) ^ 2) -
        varianceSlope a b lam * (n : ℝ)) atTop
      (𝓝 (secondDominantConstant P a b lam nu /
        dominantCoeff P lam nu +
        derivativeDominantConstant P a b lam nu /
          dominantCoeff P lam nu -
        (derivativeDominantConstant P a b lam nu /
          dominantCoeff P lam nu) ^ 2)) := by
    have heq : ∀ᶠ n : ℕ in atTop,
        (N2 n + N1 n - N1 n ^ 2 - varianceSlope a b lam * (n : ℝ)) =
        (((P n).derivative.derivative.eval 1 / (P n).eval 1 +
            (P n).derivative.eval 1 / (P n).eval 1 -
            ((P n).derivative.eval 1 / (P n).eval 1) ^ 2) -
          varianceSlope a b lam * (n : ℝ)) := by
      filter_upwards [hden_ne] with n hn
      have hp : (P n).eval 1 ≠ 0 := by
        rw [hfactor n]
        exact mul_ne_zero (hpow n) hn
      dsimp [N1, N2]
      rw [hfactor'' n, hfactor' n, hfactor n]
      field_simp [hpow n, hn, hp]
    exact hnorm.congr' heq
  have hdiv := LinearRecurrence.tendsto_div_nat_of_tendsto_sub_linear hvar'
  exact hdiv

/-- Two distinct roots of `t² = A t + B` sum to `A`, so the dominant root is simple. -/
private theorem two_mul_sub_ne_zero_of_roots {A B lam nu : ℝ}
    (hLam : lam ^ 2 = A * lam + B) (hNu : nu ^ 2 = A * nu + B) (hDistinct : lam ≠ nu) :
    2 * lam - A ≠ 0 := by
  have hsum : lam + nu = A := by
    have h : (lam - nu) * (lam + nu - A) = 0 := by linear_combination hLam - hNu
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hDistinct
    · linarith
  intro h
  exact hDistinct (by linarith)

/-- Mean asymptotics derived from the polynomial recurrence itself. -/
theorem tendsto_derivative_eval_div_nat_mul_eval
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hDominant : 0 < lam) (hModulus : |nu| < lam) (hNuNe : nu ≠ 0)
    (hA : ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu) ≠ 0) :
    Tendsto (fun n => (P n).derivative.eval 1 /
      ((n : ℝ) * (P n).eval 1)) atTop
      (𝓝 (meanSlope a b lam)) := by
  have hLamNe : lam ≠ 0 := ne_of_gt hDominant
  have hSimple := two_mul_sub_ne_zero_of_roots hLam hNu hDistinct
  have hValue := value_closed_form hP hLam hNu hDistinct
  have hDerivative := derivative_closed_form hP hLam hNu hDistinct hLamNe hNuNe hSimple
  exact mean_from_modes hDominant hModulus hA hValue hDerivative

/-- Variance asymptotics derived from the polynomial recurrence itself. -/
theorem tendsto_variance_eval_div_nat
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hDominant : 0 < lam) (hModulus : |nu| < lam) (hNuNe : nu ≠ 0)
    (hA : ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu) ≠ 0) :
    Tendsto (fun n =>
      ((P n).derivative.derivative.eval 1 / (P n).eval 1 +
          (P n).derivative.eval 1 / (P n).eval 1 -
          ((P n).derivative.eval 1 / (P n).eval 1) ^ 2) / (n : ℝ)) atTop
      (𝓝 (varianceSlope a b lam)) := by
  have hLamNe : lam ≠ 0 := ne_of_gt hDominant
  have hSimple := two_mul_sub_ne_zero_of_roots hLam hNu hDistinct
  have hValue := value_closed_form hP hLam hNu hDistinct
  have hDerivative := derivative_closed_form hP hLam hNu hDistinct hLamNe hNuNe hSimple
  have hSecond := second_derivative_closed_form hP hLam hNu hDistinct hLamNe hNuNe hSimple
  exact variance_from_modes hDominant hModulus hA hValue hDerivative hSecond

end RealRooted.ThreeTermRecurrence
