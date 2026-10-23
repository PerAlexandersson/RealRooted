import RealRooted.OperatorMatrix.Composition
import RealRooted.OperatorMatrix.OneThetaX
import RealRooted.ObreschkoffConverse.Derivative

/-!
# The Euler-derivative lag operator matrices

This file develops the structural operator-matrix proof for polynomial families
satisfying `P (n + 2) = theta (P (n + 1)) + X * theta (P n)`.  It proves
ordered-PF preservation for the factors `[[0, I], [X, theta]]` and
`[[0, theta], [X theta, theta]]`, then obtains their dense product by composition.
-/

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix.EulerDerivativeLag

/-- The identity-top factor `U = [[0, I], [X, theta]]`. -/
def identityTop : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  !![0, Letter.one.linearMap; Letter.x.linearMap, Letter.theta.linearMap]

/-- The theta-top factor `V = [[0, theta], [X theta, theta]]`. -/
def thetaTop : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  !![0, Letter.theta.linearMap;
    Letter.x.linearMap * Letter.theta.linearMap, Letter.theta.linearMap]

/-- The fixed dense two-step matrix, displayed in structural Weyl normal form. -/
def twoStep : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  !![Letter.x.linearMap * Letter.theta.linearMap, Letter.theta.linearMap;
    Letter.x.linearMap *
        (Letter.theta.linearMap * Letter.theta.linearMap + Letter.theta.linearMap),
      Letter.x.linearMap * Letter.theta.linearMap +
        Letter.theta.linearMap * Letter.theta.linearMap]

/-- The Euler and multiplication operators satisfy `theta X = X theta + X`. -/
theorem theta_mul_x :
    Letter.theta.linearMap * Letter.x.linearMap =
      Letter.x.linearMap * Letter.theta.linearMap + Letter.x.linearMap := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.add_apply, Letter.linearMap_theta,
    Letter.linearMap_x, RealRooted.theta, derivative_mul, derivative_X, one_mul]
  ring

/-- The dense two-step matrix is the product `U * V` in action order. -/
theorem twoStep_eq_mul : twoStep = identityTop * thetaTop := by
  have hone : Letter.one.linearMap = (1 : Module.End ℝ ℝ[X]) := by
    apply LinearMap.ext
    intro p
    rfl
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [twoStep, identityTop, thetaTop, Matrix.mul_apply, Fin.sum_univ_two, hone]
  · simp [twoStep, identityTop, thetaTop, Matrix.mul_apply, Fin.sum_univ_two, hone]
  · simp [twoStep, identityTop, thetaTop, Matrix.mul_apply, Fin.sum_univ_two,
      ← mul_assoc, theta_mul_x, add_mul, mul_add]
  · simp [twoStep, identityTop, thetaTop, Matrix.mul_apply, Fin.sum_univ_two]

/-- The identity-top factor sends `(p,q)` to `(q, theta q + Xp)`. -/
theorem apply_identityTop_pair (p q : ℝ[X]) :
    apply identityTop ![p, q] = ![q, RealRooted.theta q + X * p] := by
  funext i
  fin_cases i <;>
    simp [apply, identityTop, Fin.sum_univ_two, Letter.linearMap_one,
      Letter.linearMap_x, Letter.linearMap_theta, add_comm]

/-- The theta-top factor sends `(p,q)` to `(theta q, theta q + X theta p)`. -/
theorem apply_thetaTop_pair (p q : ℝ[X]) :
    apply thetaTop ![p, q] =
      ![RealRooted.theta q, RealRooted.theta q + X * RealRooted.theta p] := by
  funext i
  fin_cases i <;>
    simp [apply, thetaTop, Fin.sum_univ_two, Module.End.mul_apply,
      Letter.linearMap_x, Letter.linearMap_theta, add_comm]

/-- One application of the dense matrix advances any family satisfying the Euler-derivative
lag recurrence by two indices. -/
theorem apply_twoStep_pair_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (n : ℕ) :
    apply twoStep ![P n, P (n + 1)] = ![P (n + 2), P (n + 3)] := by
  have hnext :
      RealRooted.theta (P (n + 2)) + X * RealRooted.theta (P (n + 1)) = P (n + 3) := by
    simpa [Nat.add_assoc] using (hrec (n + 1)).symm
  rw [twoStep_eq_mul, apply_mul, apply_thetaTop_pair, ← hrec n,
    apply_identityTop_pair, hnext]

/-- The identity-top factor preserves every zero-aware ordered PF pair. -/
theorem preservesOrderedPFPair_identityTop :
    PreservesOrderedPFPair 0 Letter.one.linearMap
      Letter.x.linearMap Letter.theta.linearMap := by
  intro p q hp hq hpq
  have hXp : IsPFPolynomial (X * p) := hp.X_mul
  have hthetaQ : IsPFPolynomial (RealRooted.theta q) := theta_preserves_pf hq
  have hqXp : Interl q (X * p) :=
    (interl_iff_interl_X_mul hp hq).mp hpq
  have hqthetaQ : Interl q (RealRooted.theta q) := hq.interl_theta
  have hinterl : Interl q (X * p + RealRooted.theta q) :=
    interl_add_right_of_common_left_of_nonneg hqXp hqthetaQ
      hXp.hasNonnegCoeffs hthetaQ.hasNonnegCoeffs
  have hbottom : IsPFPolynomial (X * p + RealRooted.theta q) := by
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    · exact hXp.hasNonnegCoeffs.add hthetaQ.hasNonnegCoeffs
    by_cases hq0 : q = 0
    · subst q
      simpa [RealRooted.theta] using hXp.eq_zero_or_splits
    by_cases hzero : X * p + RealRooted.theta q = 0
    · exact Or.inl hzero
    · exact Or.inr (hinterl.toStrictInterl_of_ne hq0 hzero).2.1.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Letter.linearMap_one, LinearMap.zero_apply, zero_add] using hq
  · simpa only [Letter.linearMap_x, Letter.linearMap_theta, LinearMap.zero_apply,
      zero_add] using hbottom
  · simpa only [Letter.linearMap_one, Letter.linearMap_x, Letter.linearMap_theta,
      LinearMap.zero_apply, zero_add] using hinterl

/-- The matrix `identityTop` preserves ordered PF vectors. -/
theorem preservesOrderedPF_identityTop : PreservesOrderedPF identityTop := by
  rw [preservesOrderedPF_two_two_iff]
  simpa [identityTop] using preservesOrderedPFPair_identityTop

/-- The theta-top factor preserves every zero-aware ordered PF pair. -/
theorem preservesOrderedPFPair_thetaTop :
    PreservesOrderedPFPair 0 Letter.theta.linearMap
      (Letter.x.linearMap * Letter.theta.linearMap) Letter.theta.linearMap := by
  intro p q hp hq hpq
  have hpder : IsPFPolynomial p.derivative := hp.derivative
  have hqder : IsPFPolynomial q.derivative := hq.derivative
  have hder : Interl p.derivative q.derivative := derivativePreservesInterl hpq
  have hqderThetaP : Interl q.derivative (X * p.derivative) :=
    (interl_iff_interl_X_mul hpder hqder).mp hder
  have hbaseBottom : IsPFPolynomial (X * p.derivative + q.derivative) := by
    simpa only [add_comm] using hqder.add_of_interl hpder.X_mul hqderThetaP
  have hbaseInterl : Interl q.derivative (X * p.derivative + q.derivative) :=
    interl_add_right_of_common_left_of_nonneg hqderThetaP hqder.interl_self
      hpder.X_mul.hasNonnegCoeffs hqder.hasNonnegCoeffs
  have hbottom := hbaseBottom.X_mul
  have hinterl := hbaseInterl.mul_X_both
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Letter.linearMap_theta, LinearMap.zero_apply, zero_add] using
      theta_preserves_pf hq
  · simpa only [Letter.linearMap_theta, Letter.linearMap_x, Module.End.mul_apply,
      RealRooted.theta, mul_add, LinearMap.zero_apply, zero_add] using hbottom
  · simpa only [Letter.linearMap_theta, Letter.linearMap_x, Module.End.mul_apply,
      RealRooted.theta, mul_add, LinearMap.zero_apply, zero_add] using hinterl

/-- The matrix `thetaTop` preserves ordered PF vectors. -/
theorem preservesOrderedPF_thetaTop : PreservesOrderedPF thetaTop := by
  rw [preservesOrderedPF_two_two_iff]
  simpa [thetaTop] using preservesOrderedPFPair_thetaTop

/-- The dense two-step matrix preserves ordered PF vectors by its exact factorization. -/
theorem preservesOrderedPF_twoStep : PreservesOrderedPF twoStep := by
  rw [twoStep_eq_mul]
  exact preservesOrderedPF_identityTop.mul preservesOrderedPF_thetaTop

end RealRooted.OperatorMatrix.EulerDerivativeLag
