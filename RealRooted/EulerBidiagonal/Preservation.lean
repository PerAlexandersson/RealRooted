module

public import RealRooted.PFPolynomial.PreserverClosure
public import RealRooted.EulerBidiagonal
public import RealRooted.EulerBidiagonal.PairStep
public import RealRooted.MultiplierSequence.Bidiagonal

/-!
# Degree-local Pólya-frequency preservers for Euler bidiagonal operators

The closure argument is the finite-polynomial strict-to-weak transfer behind
Brändén, *Linear transformations preserving the Pólya frequency property*,
Corollary 3.5, arXiv:math/0403364, in its degree-local form from
`RealRooted.PFPolynomial.PreserverClosure`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The Euler bidiagonal step preserves Pólya-frequency polynomials. -/
theorem IsPFPolynomial.eulerBidiagonal_step {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (EulerBidiagonal.step a b p) := by
  have hT : ∀ {q : ℝ[X]}, IsNegativeSimple q ->
      q.natDegree ≤ p.natDegree ->
      IsPFPolynomial (EulerBidiagonal.stepLinearMap a b q) := by
    intro q hq _
    simpa only [EulerBidiagonal.stepLinearMap_apply] using
      (EulerBidiagonal.mapsNegativeSimpleBySucc_step ha hb hab hq).1.isPFPolynomial
  have h := isPFPolynomial_map_of_isNegativeSimple_of_natDegree_le
    (EulerBidiagonal.stepLinearMap a b) hT hp le_rfl
  simpa only [EulerBidiagonal.stepLinearMap_apply] using h

/-- The Euler step is the coefficient-bidiagonal operator with weights
`(k + a) (k + b)` and `1`. -/
theorem EulerBidiagonal.step_eq_bidiagonalOperator (a b : ℝ) (p : ℝ[X]) :
    EulerBidiagonal.step a b p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + a) * ((k : ℝ) + b))
        (fun _ => 1) p := by
  ext (_ | k)
  · simp [EulerBidiagonal.coeff_step]
  · simp [EulerBidiagonal.coeff_step, coeff_bidiagonalOperator_succ]

/-- The Euler bidiagonal weights form a degree-bounded Pólya-frequency
preserver at every degree. -/
theorem bidiagonalPFPreserver_eulerBidiagonal (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b) (d : ℕ) :
    BidiagonalPFPreserver
      (fun k => ((k : ℝ) + a) * ((k : ℝ) + b)) (fun _ => 1) d := by
  intro p hp hdeg
  rw [← EulerBidiagonal.step_eq_bidiagonalOperator]
  exact IsPFPolynomial.eulerBidiagonal_step ha hb hab hp

/-- The degree-local five-parameter Euler step preserves Pólya-frequency
polynomials under the hypotheses used by its negative-simple certificate. -/
theorem IsPFPolynomial.generalStep_of_natDegree_le
    {κ a b u v : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k ≤ d, 0 < u + v * k)
    (hQ : ∀ t ≤ 0, EulerBidiagonal.comparisonDefect κ a b u v t < 0)
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (EulerBidiagonal.generalStep κ a b u v p) := by
  have hT : ∀ {q : ℝ[X]}, IsNegativeSimple q ->
      q.natDegree ≤ d ->
      IsPFPolynomial (EulerBidiagonal.generalStepLinearMap κ a b u v q) := by
    intro q hq hqdeg
    have hqstep := EulerBidiagonal.isNegativeSimple_generalStep_of_natDegree
      κ a b u v q q.natDegree hq rfl hκ ha hb
      (fun k hk => hell k (hk.trans hqdeg)) hQ
    simpa only [EulerBidiagonal.generalStepLinearMap_apply] using hqstep.1.isPFPolynomial
  have h := isPFPolynomial_map_of_isNegativeSimple_of_natDegree_le
    (EulerBidiagonal.generalStepLinearMap κ a b u v) hT hp hpdeg
  simpa only [EulerBidiagonal.generalStepLinearMap_apply] using h

end RealRooted
