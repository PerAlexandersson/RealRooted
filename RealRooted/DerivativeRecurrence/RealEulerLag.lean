module

public import RealRooted.EulerOperator
public import RealRooted.EulerOperator.Shift
public import RealRooted.PFPolynomial
import RealRooted.MultiplierSequence.Laguerre
import RealRooted.MultiplierSequence.ProperPosition
import RealRooted.OperatorMatrix.Directed
import RealRooted.Wronskian.WeakForward

/-!
# Real Euler shifts and weighted derivative lags

For a fixed nonnegative real shift `s`, the decorated state consists of PF inputs
`p ≼ q` and `q ≼ X (θ + s + 1) p`. It is invariant under independently
nonnegative current and lag weights. The equations `B = s A` and
`D = (s + 1) C` recognize the displayed differential recurrence exactly.

Source: *Derivative squared-variable lag invariant*
([source](https://github.com/PerAlexandersson/real-zero-preservers/tree/1bd277e)),
`weyl-operators/notes/derivative-x2-lag-invariant.md`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A nonnegative real Euler shift preserves the PF cone. -/
theorem IsPFPolynomial.eulerShift_of_nonneg {p : ℝ[X]} (hp : IsPFPolynomial p)
    {s : ℝ} (hs : 0 ≤ s) : IsPFPolynomial (eulerShift s p) := by
  simpa only [diagonalOperator_natCast_add_eq_eulerShift] using
    (isPFMultiplierSequence_natCast_add hs).diagonalOperator_isPF hp

/-- Nonnegative real Euler shifts preserve directed PF pairs, including zero inputs. -/
theorem eulerShift_orderedPF {s : ℝ} (hs : 0 ≤ s) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    IsPFPolynomial (eulerShift s p) ∧ IsPFPolynomial (eulerShift s q) ∧
      Interl (eulerShift s p) (eulerShift s q) := by
  refine ⟨hp.eulerShift_of_nonneg hs, hq.eulerShift_of_nonneg hs, ?_⟩
  rcases hpq with rfl | rfl | hstrict
  · simp only [eulerShift_zero_polynomial]
    exact interl_zero_left _
  · simp only [eulerShift_zero_polynomial]
    exact interl_zero_right _
  · exact eulerShift_interl_of_nonneg hs hstrict

/-- Every PF polynomial precedes its nonnegative real Euler shift. -/
theorem IsPFPolynomial.interl_eulerShift {p : ℝ[X]} (hp : IsPFPolynomial p)
    {s : ℝ} (hs : 0 ≤ s) : Interl p (eulerShift s p) := by
  exact interl_add_right_of_common_left_of_nonneg hp.interl_theta
    (hp.interl_self.C_mul_right_of_nonneg hs) (theta_preserves_pf hp).hasNonnegCoeffs
    (hasNonnegCoeffs_C_mul hs hp.hasNonnegCoeffs)

/-- A shifted Euler image precedes its decorated image. -/
theorem IsPFPolynomial.interl_eulerShift_X_eulerShift {p : ℝ[X]}
    (hp : IsPFPolynomial p) {s : ℝ} (hs : 0 ≤ s) :
    Interl (eulerShift s p) (X * eulerShift (s + 1) p) := by
  have hcomm : eulerShift s (X * p) = X * eulerShift (s + 1) p := by
    simp only [eulerShift, derivative_mul, derivative_X, one_mul, map_add, map_one]
    ring
  rw [← hcomm]
  exact (eulerShift_orderedPF hs hp hp.X_mul
    ((interl_iff_interl_X_mul hp hp).mp hp.interl_self)).2.2

/-- The decorated PF state for a fixed real Euler shift. -/
def EulerLagState (s : ℝ) (p q : ℝ[X]) : Prop :=
  IsPFPolynomial p ∧ IsPFPolynomial q ∧ Interl p q ∧
    Interl q (X * eulerShift (s + 1) p)

/-- A decorated Euler state is closed under nonnegative current and lag weights. -/
theorem EulerLagState.step {s a b : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p q : ℝ[X]} (h : EulerLagState s p q) :
    EulerLagState s q
      (C a * eulerShift s q + C b * (X * eulerShift (s + 1) p)) := by
  obtain ⟨hp, hq, hpq, hdecor⟩ := h
  have hs1 : 0 ≤ s + 1 := by linarith
  have hT := hq.eulerShift_of_nonneg hs
  have hU := (hp.eulerShift_of_nonneg hs1).X_mul
  have hnn := (hasNonnegCoeffs_C_mul ha hT.hasNonnegCoeffs).add
    (hasNonnegCoeffs_C_mul hb hU.hasNonnegCoeffs)
  have hleft := interl_nonneg_combo_right_of_common_left_of_pf
    (hq.interl_eulerShift hs) hdecor hT hU ha hb
  refine ⟨hq, ?_, hleft, ?_⟩
  · by_cases hq0 : q = 0
    · simpa [hq0] using (IsPFPolynomial.of_C_nonneg hb).mul hU
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnn
    by_cases hr : C a * eulerShift s q + C b * (X * eulerShift (s + 1) p) = 0
    · exact Or.inl hr
    · exact Or.inr (hleft.toStrictInterl_of_ne hq0 hr).2.1.2
  · exact interl_add_left_of_common_right_of_nonneg
      ((hq.interl_eulerShift_X_eulerShift hs).C_mul_left_of_nonneg ha)
      (((eulerShift_orderedPF hs1 hp hq hpq).2.2.mul_X_both).C_mul_left_of_nonneg hb)
      (hasNonnegCoeffs_C_mul ha hT.hasNonnegCoeffs)
      (hasNonnegCoeffs_C_mul hb hU.hasNonnegCoeffs)

/-- Arbitrary nonnegative weights preserve the decorated state along the recurrence. -/
theorem EulerLagState.all {s : ℝ} (hs : 0 ≤ s) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) {P : ℕ → ℝ[X]}
    (hstart : EulerLagState s (P 0) (P 1))
    (hrec : ∀ n, P (n + 2) = C (a n) * eulerShift s (P (n + 1)) +
      C (b n) * (X * eulerShift (s + 1) (P n))) :
    ∀ n, EulerLagState s (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by lia, hrec n]
    exact ih.step hs (ha n) (hb n)

/-- The coefficient equations give the exact current and lag operator identity. -/
theorem eulerLag_recognizer (s A B C₀ D : ℝ) (hB : B = s * A)
    (hD : D = (s + 1) * C₀) (p q : ℝ[X]) :
    C A * theta q + C B * q + C C₀ * X * theta p + C D * X * p =
      C A * eulerShift s q + C C₀ * (X * eulerShift (s + 1) p) := by
  simp only [hB, hD, eulerShift, theta, map_mul, map_add, map_one]
  ring

private theorem eulerLagState_one {s : ℝ} (hs : 0 ≤ s) : EulerLagState s 1 1 := by
  refine ⟨IsPFPolynomial.one, IsPFPolynomial.one, IsPFPolynomial.one.interl_self, ?_⟩
  have hx := (interl_iff_interl_X_mul IsPFPolynomial.one IsPFPolynomial.one).mp
    IsPFPolynomial.one.interl_self
  simpa [eulerShift, mul_comm] using hx.C_mul_right_of_nonneg (show 0 ≤ s + 1 by linarith)

example : EulerLagState (1 / 2 : ℝ) 1 (C (1 / 2 : ℝ) * (1 + C 3 * X)) := by
  convert (eulerLagState_one (s := (1 / 2 : ℝ)) (by norm_num)).step
    (by norm_num) zero_le_one zero_le_one using 1
  ext n
  rcases n with _ | _ | n <;> norm_num [coeff_X_mul, coeff_mul_X, coeff_one]

example {p q : ℝ[X]} (s : ℝ) (hs : s = 0 ∨ s = 1 ∨ s = 2)
    (h : EulerLagState s p q) :
    EulerLagState s q (eulerShift s q + X * eulerShift (s + 1) p) := by
  have hs0 : 0 ≤ s := by rcases hs with rfl | rfl | rfl <;> norm_num
  simpa using h.step hs0 zero_le_one zero_le_one

example {s : ℝ} (hs : 0 ≤ s) {p q : ℝ[X]} (h : EulerLagState s p q) :
    EulerLagState s q 0 := by
  simpa using h.step hs le_rfl le_rfl

example {s a b : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    EulerLagState s 0 (C a * eulerShift s 0 + C b * (X * eulerShift (s + 1) 0)) := by
  exact (show EulerLagState s 0 0 from
    ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, interl_zero_left _, interl_zero_left _⟩).step
      hs ha hb

example : C (1 : ℝ) * eulerShift (1 / 2 : ℝ) 1 +
    C (1 : ℝ) * (X * eulerShift (1 / 2 + 1 : ℝ) 1) =
      C (1 / 2 : ℝ) * (1 + C 3 * X) := by
  ext n
  rcases n with _ | _ | n <;> norm_num [coeff_X_mul, coeff_mul_X, coeff_one]

example : eulerShift (1 / 2 : ℝ) (C (1 / 2) * (1 + C 3 * X)) +
    X * eulerShift (1 / 2 + 1 : ℝ) 1 = C (1 / 4 : ℝ) * (1 + C 15 * X) := by
  ext n
  rcases n with _ | _ | n <;> norm_num [coeff_X_mul, coeff_mul_X, coeff_one]

example {s : ℝ} (hs : s < 0) : ¬ IsPFPolynomial (eulerShift s 1) := by
  intro h
  have := h.hasNonnegCoeffs 0
  simp only [coeff_eulerShift, Nat.cast_zero, zero_add, coeff_one_zero, mul_one] at this
  exact (not_le_of_gt hs) this

example : ¬ Interl (X ^ 2 + 4 * X + 3 : ℝ[X]) (X ^ 2 + 4 * X) := by
  intro h
  have hp : HasPosLeadingCoeff (X ^ 2 + 4 * X + 3 : ℝ[X]) := by
    change 0 < (X ^ 2 + 4 * X + 3 : ℝ[X]).coeff
      (X ^ 2 + 4 * X + 3 : ℝ[X]).natDegree
    rw [show (X ^ 2 + 4 * X + 3 : ℝ[X]).natDegree = 2 by compute_degree!]
    norm_num [coeff_X]
  have hq : HasPosLeadingCoeff (X ^ 2 + 4 * X : ℝ[X]) := by
    change 0 < (X ^ 2 + 4 * X : ℝ[X]).coeff
      (X ^ 2 + 4 * X : ℝ[X]).natDegree
    rw [show (X ^ 2 + 4 * X : ℝ[X]).natDegree = 2 by compute_degree!]
    norm_num [coeff_X]
  have hw := wronskian_eval_nonneg_of_strictInterl hq hp
    (h.toStrictInterl_of_ne hp.ne_zero hq.ne_zero) (-3)
  norm_num [Polynomial.wronskian, derivative_add, derivative_mul, derivative_pow] at hw

end RealRooted
