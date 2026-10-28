module

public import Mathlib.Tactic.NormNum
public import RealRooted.DerivativeRecurrence.RootWindow
public import RealRooted.Tactic.Recurrence

/-!
# A049325 recurrence-space certificate

This regression module instantiates the universal defect certificate from RealRooted
issue #1978 for the pure-lag recurrence and first-order lift associated with A049325.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The four pure-lag coefficients for the A049325 certificate. -/
@[simp] def a049325Coeffs : Fin 4 → ℚ[X] :=
  ![16 * X, 16 * X, 6 * X, X]

/-- The A049325 correction polynomial is `X` times its lag characteristic polynomial. -/
theorem a049325_defectCorrection :
    defectCorrection a049325Coeffs 1 (-4) (X * (X + 16)) =
      C X * lagCharacteristic a049325Coeffs := by
  norm_num [defectCorrection, lagCharacteristic, LinearRecurrence.charPoly,
    a049325Coeffs, Fin.sum_univ_succ]
  simp only [← C_mul_X_pow_eq_monomial]
  simp only [map_add, map_mul, map_one, map_ofNat]
  ring

/-- The A049325 pure-lag recurrence and four lift-defect seeds certify its first-order
differential lift. -/
theorem a049325_first_order_of_recurrence (P : ℕ → ℚ[X])
    (hsource : ∀ n, lagDefect a049325Coeffs P n = 0)
    (hseed : ∀ n < 4,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0) (n : ℕ) :
    (n + 4 : ℚ[X]) * P (n + 1) =
      X * (X + 16) * (P n).derivative +
        (4 - 4 * (n : ℚ[X]) + 2 * X) * P n := by
  have hlift : ∀ m,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P m = 0 := by
    rr_replay_lift (hsource) (X) (hseed)
  have hn := hlift n
  simp only [liftDefect, affineIndex] at hn
  linear_combination hn

/-- The `runC, runB, runA` coefficients of `ternaryRunThreeStep`. -/
@[simp] def ternaryRunReplayCoeffs : Fin 3 → ℝ[X] :=
  ![X * (1 - X) ^ 2, 3 * X * (1 - X), 3 * X]

/-- The ternary-run source coefficients have automatic correction factor `3 * X`. -/
example (P : ℕ → ℝ[X])
    (hsource : ∀ n, lagDefect ternaryRunReplayCoeffs P n = 0)
    (hseed : ∀ n < 3,
      liftDefect 1 1 (4 * X - 1) (3 * X) (3 * X * (1 - X)) P n = 0) :
    ∀ n, liftDefect 1 1 (4 * X - 1) (3 * X) (3 * X * (1 - X)) P n = 0 := by
  fail_if_success
    rr_replay_lift (hsource) (3 * X + 1) (hseed)
  rr_replay_lift (hsource) (3 * X) (hseed)

/-- The monic physicists' Hermite recurrence, used to regress the lift-to-row adapter. -/
def hermiteReplay : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => 2 * X * hermiteReplay n - (hermiteReplay n).derivative

/-- The row adapter changes `A * P + B * P'` into the root-window convention
`B * P' + A * P`; for Hermite it recovers `H[n+1] = 2X H[n] - H[n]'`. -/
theorem hermiteReplay_succ (n : ℕ) :
    hermiteReplay (n + 1) =
      2 * X * hermiteReplay n - (hermiteReplay n).derivative := by
  have hlift : ∀ m, liftDefect 0 1 0 (2 * X) (-1) hermiteReplay m = 0 := by
    intro m
    simp [liftDefect, affineIndex, hermiteReplay]
  have hrec : ∀ m,
      hermiteReplay (m + 1) =
        C ((1 : ℚ))⁻¹ * (-1) * (hermiteReplay m).derivative +
          C ((1 : ℚ))⁻¹ * affineIndex 0 (2 * X) m * hermiteReplay m := by
    rr_lift_recurrence (hlift) (fun _ => (1 : ℚ))
      (by simp [affineIndex]) (by simp)
  simpa [affineIndex, sub_eq_add_neg, add_comm] using hrec n

/-- The lift adapter supplies the recurrence premise of the existing root-window theorem;
degree, leading-sign, window propagation, and base-row facts remain explicit. -/
example {P : ℕ → ℝ[X]} {d₁ d₀ A₁ A₀ B : ℝ[X]} {delta : ℕ → ℝ}
    {D₀ : ℕ} (W : ℝ → Prop)
    (hlift : ∀ n, liftDefect d₁ d₀ A₁ A₀ B P n = 0)
    (hdelta : ∀ n, affineIndex d₁ d₀ n = C (delta n))
    (hdelta_ne : ∀ n, delta n ≠ 0)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n)
    (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hB : ∀ n x, W x → (C (delta n)⁻¹ * B).eval x ≤ 0)
    (hW : ∀ n, (P n).Splits → (∀ t ∈ (P n).roots, W t) →
      ∀ t ∈ (P (n + 1)).roots, W t)
    (h₀ : (P 0).Splits) (hW₀ : ∀ t ∈ (P 0).roots, W t)
    (h₀₁ : D₀ = 0 → Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  apply derivativeRecurrence_interlaces_of_window W
  · rr_lift_recurrence (hlift) (delta) (hdelta) (hdelta_ne)
  · exact hdeg
  · exact hpos
  · exact hB
  · exact hW
  · exact h₀
  · exact hW₀
  · exact h₀₁

/-- Replay also works when the source recurrence and seeds begin at a later index. -/
example (P : ℕ → ℚ[X])
    (hsource : ∀ n, 3 ≤ n → lagDefect a049325Coeffs P n = 0)
    (hseed : ∀ n, 3 ≤ n → n < 3 + 4 →
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0) :
    ∀ n, 3 ≤ n →
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0 := by
  exact liftDefect_eq_zero_from_of_lagDefect_eq_zero_from (n₀ := 3) (gamma := X)
    (hsource := hsource) (hfactor := a049325_defectCorrection) (hseed := hseed)

/-- Converse replay uses the affine-leader nonvanishing side condition. -/
example (P : ℕ → ℚ[X])
    (hlift : ∀ n,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0)
    (hseed : lagDefect a049325Coeffs P 0 = 0)
    (hleader : ∀ n, affineIndex (1 : ℚ[X]) 4 (n + 4) ≠ 0) :
    ∀ n, lagDefect a049325Coeffs P n = 0 := by
  rr_replay_source (hlift) (X) (hseed) (hleader)

/-- Converse replay accepts explicit extra source seeds at singular affine leaders. -/
example (P : ℕ → ℚ[X])
    (hlift : ∀ n, 2 ≤ n →
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0)
    (hseed : lagDefect a049325Coeffs P 2 = 0)
    (hexception : ∀ n, 2 ≤ n →
      affineIndex (1 : ℚ[X]) (4 : ℚ[X]) (n + 4) = 0 →
      lagDefect a049325Coeffs P (n + 1) = 0) :
    ∀ n, 2 ≤ n → lagDefect a049325Coeffs P n = 0 := by
  exact lagDefect_eq_zero_from_of_liftDefect_eq_zero_from_of_exceptional (n₀ := 2) (gamma := X)
    (hlift := hlift) (hfactor := a049325_defectCorrection) (hseed := hseed)
    (hexception := hexception)

/-- A changed factor is rejected by certificate replay. -/
example (P : ℕ → ℚ[X])
    (hsource : ∀ n, lagDefect a049325Coeffs P n = 0)
    (hseed : ∀ n < 4,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0) :
    ∀ n, liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0 := by
  fail_if_success
    rr_replay_lift (hsource) (X + 1) (hseed)
  rr_replay_lift (hsource) (X) (hseed)

/-- A seed certificate for a changed derivative coefficient is rejected. -/
example (P : ℕ → ℚ[X])
    (hsource : ∀ n, lagDefect a049325Coeffs P n = 0)
    (hseed : ∀ n < 4,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 15)) P n = 0)
    (hgood : ∀ n < 4,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0) :
    (∀ n, liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0) ∧
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 15)) P 0 = 0 := by
  constructor
  · fail_if_success
      rr_replay_lift (hsource) (X) (hseed)
    rr_replay_lift (hsource) (X) (hgood)
  · exact hseed 0 (by norm_num)

end

end RealRooted
