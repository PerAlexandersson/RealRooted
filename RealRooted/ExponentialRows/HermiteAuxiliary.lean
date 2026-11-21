module

public import RealRooted.Hermite.Homogeneous
import Mathlib.Tactic

/-!
# Auxiliary Hermite rows for quartic exponential coefficients

We use `Φₙ(η) = Hₙ(1 + βη, q + η)`. The derivative identity encodes insertion
of a marked linear or quadratic block. This is the auxiliary family in the
unpublished manuscript associated with RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- Homogeneous Hermite polynomials evaluated along the affine line `(1 + βη, q + η)`. -/
noncomputable def hermiteAuxiliary (β q : ℂ) (n : ℕ) : ℂ[X] :=
  hermiteHomogeneous (1 + C β * X) (X + C q) n

/-- Evaluating the auxiliary row gives the corresponding scalar homogeneous Hermite value. -/
theorem eval_hermiteAuxiliary (β q η : ℂ) (n : ℕ) :
    (hermiteAuxiliary β q n).eval η = hermiteHomogeneous (1 + β * η) (η + q) n := by
  have hu : (evalRingHom η) (1 + C β * X) = 1 + β * η := by
    change (1 + C β * X).eval η = _
    rw [eval_add, eval_one, eval_mul, eval_C, eval_X]
  have hv : (evalRingHom η) (X + C q) = η + q := by
    change (X + C q).eval η = _
    rw [eval_add, eval_X, eval_C]
  have h := map_hermiteHomogeneous (evalRingHom η) (1 + C β * X) (X + C q) n
  rw [hu, hv] at h
  exact h

/-- The auxiliary family satisfies the quadratic exponential recurrence. -/
theorem hermiteAuxiliary_add_two (β q : ℂ) (n : ℕ) :
    hermiteAuxiliary β q (n + 2) = (1 + C β * X) * hermiteAuxiliary β q (n + 1) +
      C (2 * (n + 1 : ℂ)) * (X + C q) * hermiteAuxiliary β q n := by
  simp [hermiteAuxiliary, hermiteHomogeneous_add_two, map_mul, map_ofNat, map_add, map_one]

/-- Chain rule for homogeneous Hermite polynomials in two polynomial arguments. -/
theorem derivative_hermiteHomogeneous (u v : ℂ[X]) (n : ℕ) :
    (hermiteHomogeneous u v (n + 2)).derivative =
      (n + 2 : ℂ[X]) * u.derivative * hermiteHomogeneous u v (n + 1) +
      ((n + 2 : ℂ[X]) * (n + 1)) * v.derivative * hermiteHomogeneous u v n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteHomogeneous_add_two, derivative_mul, derivative_add]; ring
  | one => simp [hermiteHomogeneous_add_two, derivative_mul, derivative_add]; ring
  | more n ih ih' =>
    rw [hermiteHomogeneous_add_two u v (n + 2)]
    simp only [derivative_add, derivative_mul, derivative_natCast, derivative_ofNat,
      zero_mul, zero_add]
    rw [ih', ih]
    rw [hermiteHomogeneous_add_two u v (n + 1), hermiteHomogeneous_add_two u v n]
    push_cast
    ring

/-- Differentiating an auxiliary row inserts `βz + z²` into its exponential. -/
theorem derivative_hermiteAuxiliary (β q : ℂ) (n : ℕ) :
    (hermiteAuxiliary β q (n + 2)).derivative =
      C ((n + 2 : ℂ) * β) * hermiteAuxiliary β q (n + 1) +
      C ((n + 2 : ℂ) * (n + 1)) * hermiteAuxiliary β q n := by
  have hu : (1 + C β * X : ℂ[X]).derivative = C β := by
    rw [derivative_add, derivative_one, derivative_C_mul, derivative_X, zero_add, mul_one]
  have hv : (X + C q : ℂ[X]).derivative = 1 := derivative_X_add_C q
  have h := derivative_hermiteHomogeneous (1 + C β * X) (X + C q) n
  rw [hu, hv] at h
  simpa only [hermiteAuxiliary, map_mul, map_add, map_natCast, map_ofNat,
    map_one, mul_one, mul_assoc] using h

/-- The auxiliary row has degree at most its row index, including when `β = 0`. -/
theorem natDegree_hermiteAuxiliary_le (β q : ℂ) (n : ℕ) :
    (hermiteAuxiliary β q n).natDegree ≤ n := by
  have hu : (1 + C β * X).natDegree ≤ 1 := by compute_degree
  have hv : (X + C q).natDegree ≤ 1 := by compute_degree
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteAuxiliary]
  | one => simpa [hermiteAuxiliary] using hu
  | more n ih ih' =>
    rw [hermiteAuxiliary_add_two]
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_le).trans ((Nat.add_le_add hu ih').trans (by lia))
    · exact (natDegree_mul_le).trans
        ((Nat.add_le_add (natDegree_C_mul_le _ _ |>.trans hv) ih).trans (by lia))

end RealRooted.ExponentialRows
