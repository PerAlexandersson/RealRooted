module

public import RealRooted.ExponentialRows.HermiteAuxiliary
public import RealRooted.Hermite.Gaussian
public import RealRooted.ExponentialRows.ProductInsertion
import RealRooted.ExponentialRows.QuarticRecurrence
import Mathlib.Tactic

/-!
# Gaussian evaluation of auxiliary Hermite rows equals quartic insertion

We prove the identity by the canonical four-lag recurrence, avoiding coefficient
extraction in two formal variables. All complex evaluation parameters are allowed.
Source: the unpublished manuscript associated with RealRooted issue #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- Gaussian evaluation of the auxiliary family has the quartic four-lag recurrence. -/
theorem gaussianEval_hermiteAuxiliary_add_four (β γ c t : ℂ) (n : ℕ) :
    let F := fun k => gaussianEval (c * t) (hermiteAuxiliary β (γ * t) k)
    F (n + 4) = F (n + 3) + 2 * (γ + c * β ^ 2) * (n + 3) * t * F (n + 2) +
      3 * (2 * c * β) * (n + 3) * (n + 2) * t * F (n + 1) +
      4 * c * (n + 3) * (n + 2) * (n + 1) * t * F n := by
  dsimp only
  rw [show n + 4 = (n + 2) + 2 by lia, hermiteAuxiliary_add_two]
  simp only [add_mul, one_mul, mul_assoc, gaussianEval_add, gaussianEval_C_mul,
    gaussianEval_X_mul]
  rw [derivative_hermiteAuxiliary β (γ * t) (n + 1),
    derivative_hermiteAuxiliary β (γ * t) n]
  simp only [gaussianEval_add, gaussianEval_C_mul]
  push_cast
  ring

private lemma gaussianEval_hermiteAuxiliary_two (β q s : ℂ) :
    gaussianEval s (hermiteAuxiliary β q 2) = 1 + 2 * q + 2 * s * β ^ 2 := by
  have hp : hermiteAuxiliary β q 2 = monomial 0 (1 + 2 * q) +
      monomial 1 (2 * β + 2) + monomial 2 (β ^ 2) := by
    simp only [hermiteAuxiliary, hermiteHomogeneous_add_two,
      hermiteHomogeneous_zero, ← C_mul_X_pow_eq_monomial, pow_zero, mul_one,
      map_add, map_mul, map_pow, map_one, map_ofNat]
    rw [hermiteHomogeneous_one]
    ring
  rw [hp]
  simp only [gaussianEval_add, gaussianEval_monomial, hermiteHomogeneous_zero,
    hermiteHomogeneous_one, hermiteHomogeneous_add_two, zero_add,
    mul_one, mul_zero, Nat.cast_one]
  ring

private lemma gaussianEval_hermiteAuxiliary_three (β q s : ℂ) :
    gaussianEval s (hermiteAuxiliary β q 3) =
      1 + 6 * q + 6 * s * β ^ 2 + 12 * s * β := by
  have hp : hermiteAuxiliary β q 3 = monomial 0 (1 + 6 * q) +
      monomial 1 (3 * β + 6 + 6 * β * q) + monomial 2 (3 * β ^ 2 + 6 * β) +
      monomial 3 (β ^ 3) := by
    simp only [hermiteAuxiliary, hermiteHomogeneous_add_two, hermiteHomogeneous_one,
      hermiteHomogeneous_zero, ← C_mul_X_pow_eq_monomial, pow_zero, mul_one,
      map_add, map_mul, map_pow, map_one, map_ofNat]
    rw [hermiteHomogeneous_one]
    ring
  rw [hp]
  simp only [gaussianEval_add, gaussianEval_monomial, hermiteHomogeneous_zero,
    hermiteHomogeneous_one, hermiteHomogeneous_add_two, zero_mul, zero_add,
    mul_one, mul_zero, Nat.cast_one]
  ring

/-- The Gaussian/apolar identity for quartic rows in completed-square coordinates.
This is an equality for every row and every complex `t`, rather than a finite check. -/
theorem gaussianEval_hermiteAuxiliary_eq_insertionRow (β γ c : ℝ) (t : ℂ) (n : ℕ) :
    gaussianEval ((c : ℂ) * t) (hermiteAuxiliary β ((γ : ℂ) * t) n) =
      (insertionRow (markedBlockWeights
        (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)) n).eval₂
          Complex.ofRealHom t := by
  let w := markedBlockWeights
    (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with (_ | _ | _ | _ | n)
    · simp [hermiteAuxiliary, insertionRow_zero]
    · simp [hermiteAuxiliary, insertionRow_succ, markedBlockWeights]
    · rw [gaussianEval_hermiteAuxiliary_two, insertionRow_quartic_two]
      simp only [eval₂_add, eval₂_one, eval₂_mul, eval₂_C, eval₂_X, Complex.ofRealHom_eq_coe]
      push_cast
      ring
    · rw [gaussianEval_hermiteAuxiliary_three, insertionRow_quartic_three]
      simp only [eval₂_add, eval₂_one, eval₂_mul, eval₂_C, eval₂_X, Complex.ofRealHom_eq_coe]
      push_cast
      ring
    · have hg := gaussianEval_hermiteAuxiliary_add_four (β : ℂ) (γ : ℂ) (c : ℂ) t n
      dsimp only at hg
      rw [hg, insertionRow_quartic_add_four]
      rw [ih (n + 3) (by lia), ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
      simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, map_add, map_mul, map_pow,
        Complex.ofRealHom_eq_coe, Complex.ofReal_natCast]
      push_cast
      ring

end RealRooted.ExponentialRows
