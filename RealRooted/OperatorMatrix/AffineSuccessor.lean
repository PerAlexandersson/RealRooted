module

public import RealRooted.EulerOperator
public import RealRooted.PFPolynomial
import RealRooted.OperatorMatrix.Directed
import RealRooted.Wronskian.WeakForward

/-!
# Affine PF successors

For nonnegative coefficients, an affine combination of the identity, Euler derivative,
ordinary derivative and multiplication by `X` sends every PF input to a PF successor
exactly when its ordinary derivative coefficient vanishes. The obstruction already
occurs on `X`; degree-zero inputs impose no such restriction.

Source: *Affine PF successor derivative boundary*
([source](https://github.com/PerAlexandersson/real-zero-preservers/tree/f7e16ee)),
`weyl-operators/notes/affine-successor-derivative-boundary.md`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- An affine combination of the identity, Euler derivative, derivative and `X`. -/
def affinePFStep (a α δ ξ : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a * p + C α * theta p + C δ * p.derivative + C ξ * X * p

/-- A PF polynomial following `X` has zero constant term. -/
theorem eval_zero_eq_zero_of_interl_X {q : ℝ[X]} (hq : IsPFPolynomial q)
    (h : Interl (X : ℝ[X]) q) : q.eval 0 = 0 := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hw := wronskian_eval_nonneg_of_strictInterl
    (hq.hasNonnegCoeffs.pos_leadingCoeff hq0)
    (isPFPolynomial_X.hasNonnegCoeffs.pos_leadingCoeff X_ne_zero)
    (h.toStrictInterl_of_ne X_ne_zero hq0) 0
  have hn := hq.hasNonnegCoeffs.eval_nonneg (show (0 : ℝ) ≤ 0 from le_rfl)
  simp only [Polynomial.wronskian, eval_sub, eval_mul, eval_X, derivative_X,
    zero_mul, one_mul, zero_sub] at hw
  linarith

/-- Without an ordinary derivative term, nonnegative affine steps are PF successors. -/
theorem IsPFPolynomial.interl_affinePFStep {p : ℝ[X]} (hp : IsPFPolynomial p)
    {a α ξ : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) :
    IsPFPolynomial (affinePFStep a α 0 ξ p) ∧ Interl p (affinePFStep a α 0 ξ p) := by
  have hθ := theta_preserves_pf hp
  have hnn : HasNonnegCoeffs (affinePFStep a α 0 ξ p) := by
    simpa [affinePFStep, mul_assoc] using
      ((hasNonnegCoeffs_C_mul ha hp.hasNonnegCoeffs).add
        (hasNonnegCoeffs_C_mul hα hθ.hasNonnegCoeffs)).add
        (hasNonnegCoeffs_C_mul hξ hp.X_mul.hasNonnegCoeffs)
  have hedge : Interl p (affinePFStep a α 0 ξ p) := by
    simpa [affinePFStep, mul_assoc] using
      interl_add_right_of_common_left_of_nonneg
        (interl_nonneg_combo_right_of_common_left_of_pf hp.interl_self hp.interl_theta
          hp hθ ha hα)
        (((interl_iff_interl_X_mul hp hp).mp hp.interl_self).C_mul_right_of_nonneg hξ)
        ((hasNonnegCoeffs_C_mul ha hp.hasNonnegCoeffs).add
          (hasNonnegCoeffs_C_mul hα hθ.hasNonnegCoeffs))
        (hasNonnegCoeffs_C_mul hξ hp.X_mul.hasNonnegCoeffs)
  refine ⟨?_, hedge⟩
  by_cases hp0 : p = 0
  · simpa [affinePFStep, hp0, theta] using IsPFPolynomial.zero
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnn
  by_cases hout : affinePFStep a α 0 ξ p = 0
  · exact Or.inl hout
  · exact Or.inr (hedge.toStrictInterl_of_ne hp0 hout).2.1.2

/-- At every positive degree cap, universal PF succession excludes a derivative term. -/
theorem affinePFStep_through_iff {a α δ ξ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (h : 0 ≤ a ∧ 0 ≤ α ∧ 0 ≤ δ ∧ 0 ≤ ξ) :
    (∀ p : ℝ[X], IsPFPolynomial p → p.natDegree ≤ N →
      IsPFPolynomial (affinePFStep a α δ ξ p) ∧
        Interl p (affinePFStep a α δ ξ p)) ↔ δ = 0 := by
  constructor
  · intro hall
    obtain ⟨hpf, hedge⟩ := hall X isPFPolynomial_X (by simpa using hN)
    have hz := eval_zero_eq_zero_of_interl_X hpf hedge
    simpa [affinePFStep, theta] using hz
  · rintro rfl p hp _
    exact hp.interl_affinePFStep h.1 h.2.1 h.2.2.2

/-- The unrestricted affine PF successor criterion. -/
theorem affinePFStep_all_iff {a α δ ξ : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ α ∧ 0 ≤ δ ∧ 0 ≤ ξ) :
    (∀ p : ℝ[X], IsPFPolynomial p →
      IsPFPolynomial (affinePFStep a α δ ξ p) ∧
        Interl p (affinePFStep a α δ ξ p)) ↔ δ = 0 := by
  constructor
  · intro hall
    exact (affinePFStep_through_iff (N := 1) le_rfl h).mp (fun p hp _ ↦ hall p hp)
  · rintro rfl p hp
    exact hp.interl_affinePFStep h.1 h.2.1 h.2.2.2

/-- Degree-zero inputs admit arbitrary nonnegative derivative coefficients. -/
theorem affinePFStep_cap_zero {a α δ ξ : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ α ∧ 0 ≤ δ ∧ 0 ≤ ξ)
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ 0) :
    IsPFPolynomial (affinePFStep a α δ ξ p) ∧ Interl p (affinePFStep a α δ ξ p) := by
  have hd : p.derivative = 0 := derivative_eq_zero.mpr (by lia)
  simpa [affinePFStep, hd] using hp.interl_affinePFStep h.1 h.2.1 h.2.2.2

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (affinePFStep 0 1 0 1 p) ∧ Interl p (affinePFStep 0 1 0 1 p) := by
  exact hp.interl_affinePFStep le_rfl zero_le_one zero_le_one

example : ¬ (IsPFPolynomial (affinePFStep 1 0 1 0 X) ∧
    Interl X (affinePFStep 1 0 1 0 X)) := by
  rintro ⟨hp, hi⟩
  have := eval_zero_eq_zero_of_interl_X hp hi
  norm_num [affinePFStep, theta] at this

example : ¬ (IsPFPolynomial (affinePFStep 1 0 1 1 X) ∧
    Interl X (affinePFStep 1 0 1 1 X)) := by
  rintro ⟨hp, hi⟩
  have := eval_zero_eq_zero_of_interl_X hp hi
  norm_num [affinePFStep, theta] at this

example : IsPFPolynomial (affinePFStep 1 1 1 1 1) ∧
    Interl 1 (affinePFStep 1 1 1 1 1) := by
  exact affinePFStep_cap_zero ⟨zero_le_one, zero_le_one, zero_le_one, zero_le_one⟩
    IsPFPolynomial.one (by simp)

end RealRooted
