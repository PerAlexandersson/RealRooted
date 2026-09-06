import Mathlib.Algebra.MvPolynomial.Monad
import RealRooted.MultivariateStability

/-!
# Same-phase stability

Leake--Ryder same-phase stability is the real-rootedness of every univariate
restriction obtained by putting the variables on one ray with nonnegative
coordinate weights.  Zero weights are included; they are needed for induced
subgraph specializations.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Restrict a real multivariate polynomial to `z i = wt i * X`. -/
def commonPhaseRestriction {sigma : Type*} (wt : sigma → ℝ)
    (P : MvPolynomial sigma ℝ) : ℝ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (wt i) * Polynomial.X) P

/-- A real multivariate polynomial is same-phase stable when every
nonnegative common-phase restriction is real-rooted. -/
def SamePhaseStable {sigma : Type*} (P : MvPolynomial sigma ℝ) : Prop :=
  ∀ wt : sigma → ℝ, (∀ i, 0 ≤ wt i) → (commonPhaseRestriction wt P).Splits

/-- Scale each variable of a multivariate polynomial by a real scalar. -/
def coordinateScale {sigma : Type*} (a : sigma → ℝ)
    (P : MvPolynomial sigma ℝ) : MvPolynomial sigma ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C (a i) * MvPolynomial.X i) P

@[simp] theorem commonPhaseRestriction_C {sigma : Type*} (a : ℝ)
    (wt : sigma → ℝ) :
    commonPhaseRestriction wt (MvPolynomial.C a) = Polynomial.C a := by
  simp [commonPhaseRestriction]

@[simp] theorem commonPhaseRestriction_X {sigma : Type*} (i : sigma)
    (wt : sigma → ℝ) :
    commonPhaseRestriction wt (MvPolynomial.X i) =
      Polynomial.C (wt i) * Polynomial.X := by
  simp [commonPhaseRestriction]

@[simp] theorem commonPhaseRestriction_eval {sigma : Type*}
    (wt : sigma → ℝ) (P : MvPolynomial sigma ℝ) (x : ℝ) :
    (commonPhaseRestriction wt P).eval x =
      MvPolynomial.eval (fun i => wt i * x) P := by
  unfold commonPhaseRestriction
  change Polynomial.evalRingHom x
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (wt i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have hC : (Polynomial.evalRingHom x).comp Polynomial.C =
      RingHom.id ℝ := by
    ext r
    simp
  rw [hC]
  rfl

theorem commonPhaseRestriction_coordinateScale {sigma : Type*}
    (a wt : sigma → ℝ) (P : MvPolynomial sigma ℝ) :
    commonPhaseRestriction wt (coordinateScale a P) =
      commonPhaseRestriction (fun i => a i * wt i) P := by
  unfold coordinateScale commonPhaseRestriction
  change MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (wt i) * Polynomial.X)
      (MvPolynomial.bind₁
        (fun i => MvPolynomial.C (a i) * MvPolynomial.X i) P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext i
  simp
  ring

/-- Nonnegative coordinate scaling preserves same-phase stability, including
zero scaling factors. -/
theorem SamePhaseStable.coordinateScale {sigma : Type*}
    {P : MvPolynomial sigma ℝ} (hP : SamePhaseStable P)
    {a : sigma → ℝ} (ha : ∀ i, 0 ≤ a i) :
    SamePhaseStable (coordinateScale a P) := by
  intro wt hwt
  rw [commonPhaseRestriction_coordinateScale]
  exact hP (fun i => a i * wt i) fun i => mul_nonneg (ha i) (hwt i)

end RealRooted
