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

/-- The phase-shifted two-step product, acting first by `identityTop` and then by
`thetaTop`. -/
def shiftedTwoStep : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  thetaTop * identityTop

/-- The dense two-step matrix with every entry in left-normal Weyl form. -/
def twoStepLeftNormal : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  !![(LinearMap.mulLeft ℝ (X ^ 2)).comp Polynomial.derivative,
      (LinearMap.mulLeft ℝ X).comp Polynomial.derivative;
    (LinearMap.mulLeft ℝ (X ^ 3)).comp
        (Polynomial.derivative.comp Polynomial.derivative) +
      (LinearMap.mulLeft ℝ (2 * X ^ 2)).comp Polynomial.derivative,
    (LinearMap.mulLeft ℝ (X ^ 2)).comp
        (Polynomial.derivative.comp Polynomial.derivative) +
      (LinearMap.mulLeft ℝ (X ^ 2 + X)).comp Polynomial.derivative]

/-- The Euler and multiplication operators satisfy `theta X = X theta + X`. -/
theorem theta_mul_x :
    Letter.theta.linearMap * Letter.x.linearMap =
      Letter.x.linearMap * Letter.theta.linearMap + Letter.x.linearMap := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.add_apply, Letter.linearMap_theta,
    Letter.linearMap_x, RealRooted.theta, derivative_mul, derivative_X, one_mul]
  ring

/-- The basic Weyl relation `D X = X D + I` on real polynomials. -/
theorem derivative_mul_x :
    (Polynomial.derivative : Module.End ℝ ℝ[X]) * Letter.x.linearMap =
      Letter.x.linearMap * Polynomial.derivative + Letter.one.linearMap := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.add_apply, Letter.linearMap_x,
    Letter.linearMap_one, derivative_mul, derivative_X, one_mul]
  ring

/-- The multiplication-divisor correction `(theta - I) X = X theta`. -/
theorem theta_sub_one_mul_x :
    (Letter.theta.linearMap - Letter.one.linearMap) * Letter.x.linearMap =
      Letter.x.linearMap * Letter.theta.linearMap := by
  have hone : Letter.one.linearMap = (1 : Module.End ℝ ℝ[X]) := by
    apply LinearMap.ext
    intro p
    rfl
  rw [hone, sub_mul, one_mul, theta_mul_x, add_sub_cancel_right]

/-- The three elementary right factors of the lag operator `X theta`. -/
inductive FactorLabel where
  | identity
  | euler
  | x
  deriving DecidableEq, Repr

/-- The right factor selected by a lag-factor label. -/
def FactorLabel.rightFactor : FactorLabel → Module.End ℝ ℝ[X]
  | .identity => Letter.one.linearMap
  | .euler => Letter.theta.linearMap
  | .x => Letter.x.linearMap

/-- The left quotient paired with a lag-factor label. -/
def FactorLabel.leftQuotient : FactorLabel → Module.End ℝ ℝ[X]
  | .identity => Letter.x.linearMap * Letter.theta.linearMap
  | .euler => Letter.x.linearMap
  | .x => Letter.theta.linearMap - Letter.one.linearMap

/-- The mixed transition from a source lag factor to a target lag factor. -/
def transition (source target : FactorLabel) :
    Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  !![0, target.rightFactor; source.leftQuotient, Letter.theta.linearMap]

/-- The recurrence state decorated by the right factor of a lag label. -/
def decoratedState (P : ℕ → ℝ[X]) (n : ℕ) (label : FactorLabel) : Fin 2 → ℝ[X] :=
  ![label.rightFactor (P n), P (n + 1)]

/-- The identity label exposes the original adjacent pair. -/
@[simp] theorem decoratedState_identity (P : ℕ → ℝ[X]) (n : ℕ) :
    decoratedState P n .identity = ![P n, P (n + 1)] := by
  funext i
  fin_cases i <;> simp [decoratedState, FactorLabel.rightFactor, Letter.linearMap_one]

/-- The Euler label decorates the left coordinate by `theta`. -/
@[simp] theorem decoratedState_euler (P : ℕ → ℝ[X]) (n : ℕ) :
    decoratedState P n .euler = ![RealRooted.theta (P n), P (n + 1)] := by
  funext i
  fin_cases i <;> simp [decoratedState, FactorLabel.rightFactor, Letter.linearMap_theta]

/-- Every registered label gives an exact right factorization of the lag `X theta`. -/
theorem lag_eq_leftQuotient_mul_rightFactor (label : FactorLabel) :
    Letter.x.linearMap * Letter.theta.linearMap =
      label.leftQuotient * label.rightFactor := by
  cases label with
  | identity =>
      have hone : Letter.one.linearMap = (1 : Module.End ℝ ℝ[X]) := by
        apply LinearMap.ext
        intro p
        rfl
      simp [FactorLabel.leftQuotient, FactorLabel.rightFactor, hone]
  | euler => rfl
  | x =>
      simpa [FactorLabel.leftQuotient, FactorLabel.rightFactor] using
        theta_sub_one_mul_x.symm

/-- The preserving edge from the Euler label to the identity label is `identityTop`. -/
theorem transition_euler_identity :
    transition .euler .identity = identityTop := rfl

/-- The preserving edge from the identity label to the Euler label is `thetaTop`. -/
theorem transition_identity_euler :
    transition .identity .euler = thetaTop := rfl

/-- A mixed transition sends `(p,q)` to `(B_target q, K_source p + theta q)`. -/
theorem apply_transition_pair (source target : FactorLabel) (p q : ℝ[X]) :
    apply (transition source target) ![p, q] =
      ![target.rightFactor q, source.leftQuotient p + RealRooted.theta q] := by
  funext i
  fin_cases i <;>
    simp [apply, transition, Fin.sum_univ_two, Letter.linearMap_theta]

/-- Every registered mixed transition advances its correspondingly decorated recurrence
state by one rank. -/
theorem apply_transition_decoratedState_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (n : ℕ) (source target : FactorLabel) :
    apply (transition source target) (decoratedState P n source) =
      decoratedState P (n + 1) target := by
  have hfactor :
      source.leftQuotient (source.rightFactor (P n)) = X * RealRooted.theta (P n) := by
    have h := congrArg (fun T : Module.End ℝ ℝ[X] => T (P n))
      (lag_eq_leftQuotient_mul_rightFactor source)
    simpa [Module.End.mul_apply, Letter.linearMap_x, Letter.linearMap_theta] using h.symm
  have hindex : 1 + (n + 1) = n + 2 := by lia
  calc
    apply (transition source target) (decoratedState P n source) =
        ![target.rightFactor (P (n + 1)),
          source.leftQuotient (source.rightFactor (P n)) + RealRooted.theta (P (n + 1))] := by
      simpa only [decoratedState] using
        apply_transition_pair source target (source.rightFactor (P n)) (P (n + 1))
    _ = decoratedState P (n + 1) target := by
      funext i
      fin_cases i
      · rfl
      · simpa [decoratedState, hfactor, hindex, add_comm] using (hrec n).symm

/-- The structural and left-normal displays of the dense matrix agree exactly. -/
theorem twoStep_eq_leftNormal : twoStep = twoStepLeftNormal := by
  apply Matrix.ext
  intro i j
  apply LinearMap.ext
  intro p
  fin_cases i <;> fin_cases j <;>
    simp [twoStep, twoStepLeftNormal, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, Letter.linearMap_x,
      Letter.linearMap_theta, RealRooted.theta, derivative_mul, derivative_X] <;>
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

/-- Powers of the dense matrix generate every even/odd pair of a family satisfying the
Euler-derivative lag recurrence. -/
theorem apply_twoStep_pow_pair_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (m n : ℕ) :
    apply (twoStep ^ m) ![P n, P (n + 1)] =
      ![P (n + 2 * m), P (n + 2 * m + 1)] := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, apply_mul, apply_twoStep_pair_of_recurrence P hrec n]
      have heven : (n + 2) + 2 * m = n + 2 * (m + 1) := by ring
      have hodd : (n + 2) + 2 * m + 1 = n + 2 * (m + 1) + 1 := by ring
      simpa [heven, hodd] using ih (n := n + 2)

/-- The phase-shifted product advances an Euler-decorated recurrence state by two ranks. -/
theorem apply_shiftedTwoStep_decoratedState_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (n : ℕ) :
    apply shiftedTwoStep (decoratedState P n .euler) =
      decoratedState P (n + 2) .euler := by
  rw [shiftedTwoStep, apply_mul, ← transition_euler_identity,
    apply_transition_decoratedState_of_recurrence P hrec n .euler .identity,
    ← transition_identity_euler,
    apply_transition_decoratedState_of_recurrence P hrec (n + 1) .identity .euler]

/-- Powers of the phase-shifted product generate every even-rank Euler-decorated state. -/
theorem apply_shiftedTwoStep_pow_decoratedState_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (m n : ℕ) :
    apply (shiftedTwoStep ^ m) (decoratedState P n .euler) =
      decoratedState P (n + 2 * m) .euler := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, apply_mul, apply_shiftedTwoStep_decoratedState_of_recurrence P hrec n]
      have hindex : (n + 2) + 2 * m = n + 2 * (m + 1) := by ring
      simpa [hindex] using ih (n := n + 2)

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

/-- The phase-shifted two-step product preserves ordered PF vectors. -/
theorem preservesOrderedPF_shiftedTwoStep : PreservesOrderedPF shiftedTwoStep := by
  exact preservesOrderedPF_thetaTop.mul preservesOrderedPF_identityTop

/-- The mixed edge from the Euler label to the identity label preserves ordered PF vectors. -/
theorem preservesOrderedPF_transition_euler_identity :
    PreservesOrderedPF (transition .euler .identity) := by
  rw [transition_euler_identity]
  exact preservesOrderedPF_identityTop

/-- The mixed edge from the identity label to the Euler label preserves ordered PF vectors. -/
theorem preservesOrderedPF_transition_identity_euler :
    PreservesOrderedPF (transition .identity .euler) := by
  rw [transition_identity_euler]
  exact preservesOrderedPF_thetaTop

private theorem not_interl_X_mul_X_add_one_X :
    ¬ Interl (X * (X + 1) : ℝ[X]) X := by
  intro hinterl
  have hdegrees :=
    (hinterl.toStrictInterl_of_ne
      (mul_ne_zero X_ne_zero (by
        simpa only [C_1] using (X_add_C_ne_zero (1 : ℝ)))) X_ne_zero).natDegree_bounds
  have hleft : (X * (X + 1) : ℝ[X]).natDegree = 2 := by
    compute_degree!
  rw [hleft, natDegree_X] at hdegrees
  norm_num at hdegrees

private theorem not_interl_of_left_root_sign_pos {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    {r : ℝ} (hr : f.IsRoot r) (hsign : 0 < g.eval r * f.derivative.eval r) :
    ¬ Interl f g := by
  intro hinterl
  have hnonpos :=
    (hinterl.toStrictInterl_of_ne hf0 hg0).eval_mul_derivative_nonpos_of_left_root
      (hf.hasNonnegCoeffs.pos_leadingCoeff hf0)
      (hg.hasNonnegCoeffs.pos_leadingCoeff hg0) hr
  exact (not_lt_of_ge hnonpos) hsign

/-- A transition whose source label is `X` cannot preserve ordered PF vectors. -/
theorem not_preservesOrderedPF_transition_x_source (target : FactorLabel) :
    ¬ PreservesOrderedPF (transition .x target) := by
  intro hpreserves
  have hseed : IsOrderedPF ![(1 : ℝ[X]), 0] := by
    rw [isOrderedPF_pair_iff]
    exact ⟨IsPFPolynomial.one, IsPFPolynomial.zero, interl_zero_right 1⟩
  have himage := hpreserves ![(1 : ℝ[X]), 0] hseed
  rw [apply_transition_pair, isOrderedPF_pair_iff] at himage
  have hcoeff := himage.2.1.hasNonnegCoeffs 0
  norm_num [FactorLabel.leftQuotient, Letter.linearMap_one,
    Letter.linearMap_theta, RealRooted.theta] at hcoeff

/-- A transition whose target label is `X` cannot preserve ordered PF vectors. -/
theorem not_preservesOrderedPF_transition_x_target (source : FactorLabel) :
    ¬ PreservesOrderedPF (transition source .x) := by
  intro hpreserves
  have hseed : IsOrderedPF ![(0 : ℝ[X]), X + 1] := by
    rw [isOrderedPF_pair_iff]
    exact ⟨IsPFPolynomial.zero, isPFPolynomial_X_add_one, interl_zero_left (X + 1)⟩
  have himage := hpreserves ![(0 : ℝ[X]), X + 1] hseed
  rw [apply_transition_pair, isOrderedPF_pair_iff] at himage
  apply not_interl_X_mul_X_add_one_X
  simpa [FactorLabel.rightFactor, Letter.linearMap_x, Letter.linearMap_theta,
    RealRooted.theta] using himage.2.2

/-- The identity-to-identity transition fails on a linear/quadratic ordered PF pair. -/
theorem not_preservesOrderedPF_transition_identity_identity :
    ¬ PreservesOrderedPF (transition .identity .identity) := by
  intro hpreserves
  have hp : IsPFPolynomial (X + C 2 : ℝ[X]) :=
    isPFPolynomial_X_add_C (by norm_num)
  have hp3 : IsPFPolynomial (X + C 3 : ℝ[X]) :=
    isPFPolynomial_X_add_C (by norm_num)
  have hq : IsPFPolynomial ((X + C 2) * (X + C 3) : ℝ[X]) := hp.mul hp3
  have hpq : Interl (X + C 2 : ℝ[X]) ((X + C 2) * (X + C 3)) := by
    have hbase : StrictInterl (1 : ℝ[X]) (X + C 3) :=
      (interlaces_one_linear (natDegree_X_add_C 3)).toStrictInterl
    have hcommon := hbase.mul_common_factor
      (X_add_C_ne_zero 2) (Polynomial.Splits.X_add_C 2)
    simpa only [mul_one] using hcommon.toInterl
  have hseed : IsOrderedPF ![(X + C 2 : ℝ[X]), (X + C 2) * (X + C 3)] := by
    rw [isOrderedPF_pair_iff]
    exact ⟨hp, hq, hpq⟩
  have himage := hpreserves ![(X + C 2 : ℝ[X]), (X + C 2) * (X + C 3)] hseed
  rw [apply_transition_pair, isOrderedPF_pair_iff] at himage
  rw [show C (2 : ℝ) = (2 : ℝ[X]) from map_ofNat C 2,
    show C (3 : ℝ) = (3 : ℝ[X]) from map_ofNat C 3] at himage
  have hf : IsPFPolynomial (6 + 5 * X + X ^ 2 : ℝ[X]) := by
    convert himage.1 using 1
    simp [FactorLabel.rightFactor, Letter.linearMap_one]
    ring
  have hg : IsPFPolynomial (5 * X + 3 * X ^ 2 : ℝ[X]) := by
    convert himage.2.1 using 1
    simp [FactorLabel.leftQuotient, Module.End.mul_apply, Letter.linearMap_x,
      Letter.linearMap_theta, RealRooted.theta, derivative_mul]
    ring
  have hsign :
      0 < (5 * X + 3 * X ^ 2 : ℝ[X]).eval (-2) *
        (6 + 5 * X + X ^ 2 : ℝ[X]).derivative.eval (-2) := by
    norm_num
  have hf0 : (6 + 5 * X + X ^ 2 : ℝ[X]) ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    norm_num at hsign
  have hg0 : (5 * X + 3 * X ^ 2 : ℝ[X]) ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    norm_num at hsign
  apply not_interl_of_left_root_sign_pos hf hg hf0 hg0 (r := -2)
  · norm_num [Polynomial.IsRoot.def]
  · exact hsign
  convert himage.2.2 using 1 <;>
    simp [FactorLabel.rightFactor, FactorLabel.leftQuotient, Module.End.mul_apply,
      Letter.linearMap_one, Letter.linearMap_x, Letter.linearMap_theta,
      RealRooted.theta, derivative_mul] <;> ring

/-- The Euler-to-Euler transition fails on a quadratic/quadratic ordered PF pair. -/
theorem not_preservesOrderedPF_transition_euler_euler :
    ¬ PreservesOrderedPF (transition .euler .euler) := by
  intro hpreserves
  have hp2 : IsPFPolynomial (X + C 2 : ℝ[X]) :=
    isPFPolynomial_X_add_C (by norm_num)
  have hp3 : IsPFPolynomial (X + C 3 : ℝ[X]) :=
    isPFPolynomial_X_add_C (by norm_num)
  have hp : IsPFPolynomial ((X + C 2) * (X + C 3) : ℝ[X]) := hp2.mul hp3
  have hq : IsPFPolynomial (X * (X + C 2) : ℝ[X]) := isPFPolynomial_X.mul hp2
  have hpq : Interl ((X + C 2) * (X + C 3) : ℝ[X]) (X * (X + C 2)) := by
    have hlin : StrictInterl (X + C 3 : ℝ[X]) X := by
      simpa only [map_zero, add_zero] using
        (StrictInterl.X_add_C_iff (a := 0) (b := 3)).2 (by norm_num)
    have hcommon := hlin.mul_common_factor
      (by simpa using (X_add_C_ne_zero (2 : ℝ)))
      (Polynomial.Splits.X_add_C 2)
    simpa only [mul_comm] using hcommon.toInterl
  have hseed : IsOrderedPF ![((X + C 2) * (X + C 3) : ℝ[X]), X * (X + C 2)] := by
    rw [isOrderedPF_pair_iff]
    exact ⟨hp, hq, hpq⟩
  have himage := hpreserves ![((X + C 2) * (X + C 3) : ℝ[X]), X * (X + C 2)] hseed
  rw [apply_transition_pair, isOrderedPF_pair_iff] at himage
  rw [show C (2 : ℝ) = (2 : ℝ[X]) from map_ofNat C 2,
    show C (3 : ℝ) = (3 : ℝ[X]) from map_ofNat C 3] at himage
  have hf : IsPFPolynomial (2 * X + 2 * X ^ 2 : ℝ[X]) := by
    convert himage.1 using 1
    simp [FactorLabel.rightFactor, Letter.linearMap_theta,
      RealRooted.theta, derivative_mul]
    ring
  have hg : IsPFPolynomial (8 * X + 7 * X ^ 2 + X ^ 3 : ℝ[X]) := by
    convert himage.2.1 using 1
    simp [FactorLabel.leftQuotient, Letter.linearMap_x, RealRooted.theta,
      derivative_mul]
    ring
  have hsign :
      0 < (8 * X + 7 * X ^ 2 + X ^ 3 : ℝ[X]).eval (-1) *
        (2 * X + 2 * X ^ 2 : ℝ[X]).derivative.eval (-1) := by
    norm_num
  have hf0 : (2 * X + 2 * X ^ 2 : ℝ[X]) ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    norm_num at hsign
  have hg0 : (8 * X + 7 * X ^ 2 + X ^ 3 : ℝ[X]) ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    norm_num at hsign
  apply not_interl_of_left_root_sign_pos hf hg hf0 hg0 (r := -1)
  · norm_num [Polynomial.IsRoot.def]
  · exact hsign
  convert himage.2.2 using 1 <;>
    simp [FactorLabel.rightFactor, FactorLabel.leftQuotient, Letter.linearMap_x,
      Letter.linearMap_theta, RealRooted.theta, derivative_mul] <;> ring

/-- Among the nine mixed transitions, exactly the two alternating identity/Euler edges
preserve ordered PF vectors. -/
theorem preservesOrderedPF_transition_iff (source target : FactorLabel) :
    PreservesOrderedPF (transition source target) ↔
      (source = .euler ∧ target = .identity) ∨
        (source = .identity ∧ target = .euler) := by
  constructor
  · intro hpreserves
    cases source with
    | identity =>
        cases target with
        | identity =>
            exact (not_preservesOrderedPF_transition_identity_identity hpreserves).elim
        | euler => exact Or.inr ⟨rfl, rfl⟩
        | x => exact (not_preservesOrderedPF_transition_x_target .identity hpreserves).elim
    | euler =>
        cases target with
        | identity => exact Or.inl ⟨rfl, rfl⟩
        | euler => exact (not_preservesOrderedPF_transition_euler_euler hpreserves).elim
        | x => exact (not_preservesOrderedPF_transition_x_target .euler hpreserves).elim
    | x => exact (not_preservesOrderedPF_transition_x_source target hpreserves).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact preservesOrderedPF_transition_euler_identity
    · exact preservesOrderedPF_transition_identity_euler

/-- The dense two-step matrix preserves ordered PF vectors by its exact factorization. -/
theorem preservesOrderedPF_twoStep : PreservesOrderedPF twoStep := by
  rw [twoStep_eq_mul]
  exact preservesOrderedPF_identityTop.mul preservesOrderedPF_thetaTop

/-- The initial pair `(1,X)` is an ordered PF vector. -/
theorem isOrderedPF_one_X : IsOrderedPF ![(1 : ℝ[X]), X] := by
  rw [isOrderedPF_pair_iff]
  have hX : IsPFPolynomial X := by
    simpa only [mul_one] using IsPFPolynomial.one.X_mul
  have hinterl : Interl (1 : ℝ[X]) X := by
    simpa only [mul_one] using
      (interl_iff_interl_X_mul IsPFPolynomial.one IsPFPolynomial.one).mp
        IsPFPolynomial.one.interl_self
  exact ⟨IsPFPolynomial.one, hX, hinterl⟩

/-- The phase-shifted initial pair `(0,X)` is an ordered PF vector. -/
theorem isOrderedPF_zero_X : IsOrderedPF ![(0 : ℝ[X]), X] := by
  rw [isOrderedPF_pair_iff]
  exact ⟨IsPFPolynomial.zero, isPFPolynomial_X, interl_zero_left X⟩

/-- Initial values `(1,X)` make the rank-zero Euler-decorated state equal to `(0,X)`. -/
theorem isOrderedPF_euler_seed_one_X (P : ℕ → ℝ[X])
    (hzero : P 0 = 1) (hone : P 1 = X) :
    IsOrderedPF (decoratedState P 0 .euler) := by
  simpa [hzero, hone, RealRooted.theta] using isOrderedPF_zero_X

/-- An ordered-PF seed remains ordered at every even/odd state of the two-step orbit. -/
theorem isOrderedPF_even_odd_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF ![P 0, P 1]) (m : ℕ) :
    IsOrderedPF ![P (2 * m), P (2 * m + 1)] := by
  have hpres : IsOrderedPF (apply (twoStep ^ m) ![P 0, P 1]) :=
    (preservesOrderedPF_twoStep.pow m) _ hseed
  rw [apply_twoStep_pow_pair_of_recurrence P hrec m 0] at hpres
  simpa using hpres

/-- An ordered Euler-decorated seed remains ordered at every even rank of the shifted
two-step orbit. -/
theorem isOrderedPF_euler_even_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF (decoratedState P 0 .euler)) (m : ℕ) :
    IsOrderedPF (decoratedState P (2 * m) .euler) := by
  have hpres : IsOrderedPF
      (apply (shiftedTwoStep ^ m) (decoratedState P 0 .euler)) :=
    (preservesOrderedPF_shiftedTwoStep.pow m) _ hseed
  rw [apply_shiftedTwoStep_pow_decoratedState_of_recurrence P hrec m 0] at hpres
  simpa using hpres

/-- The shifted phase exposes every odd-indexed original adjacent pair. -/
theorem isOrderedPF_odd_even_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF (decoratedState P 0 .euler)) (m : ℕ) :
    IsOrderedPF ![P (2 * m + 1), P (2 * m + 2)] := by
  have heuler := isOrderedPF_euler_even_of_recurrence P hrec hseed m
  have hnext : IsOrderedPF
      (apply (transition .euler .identity) (decoratedState P (2 * m) .euler)) :=
    preservesOrderedPF_transition_euler_identity _ heuler
  rw [apply_transition_decoratedState_of_recurrence P hrec (2 * m) .euler .identity]
    at hnext
  simpa [Nat.add_assoc] using hnext

/-- The two-step orbit exposes every even-indexed adjacent interlacing edge. -/
theorem interl_even_odd_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF ![P 0, P 1]) (m : ℕ) :
    Interl (P (2 * m)) (P (2 * m + 1)) :=
  (isOrderedPF_even_odd_of_recurrence P hrec hseed m).2 0 1 (by decide)

/-- The shifted two-step orbit exposes every odd-indexed adjacent interlacing edge. -/
theorem interl_odd_even_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF (decoratedState P 0 .euler)) (m : ℕ) :
    Interl (P (2 * m + 1)) (P (2 * m + 2)) :=
  (isOrderedPF_odd_even_of_recurrence P hrec hseed m).2 0 1 (by decide)

/-- The two rotated phases together expose every original adjacent interlacing edge. -/
theorem interl_adjacent_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hidentity : IsOrderedPF ![P 0, P 1])
    (heuler : IsOrderedPF (decoratedState P 0 .euler)) (n : ℕ) :
    Interl (P n) (P (n + 1)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact interl_even_odd_of_recurrence P hrec hidentity m
  · simpa [Nat.add_assoc] using interl_odd_even_of_recurrence P hrec heuler m

/-- Every adjacent pair interlaces for a recurrence family with initial values `(1,X)`. -/
theorem interl_adjacent_of_recurrence_one_X (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hzero : P 0 = 1) (hone : P 1 = X) (n : ℕ) :
    Interl (P n) (P (n + 1)) := by
  apply interl_adjacent_of_recurrence P hrec
  · simpa [hzero, hone] using isOrderedPF_one_X
  · exact isOrderedPF_euler_seed_one_X P hzero hone

/-- Every row of a family in the two-step orbit is a PF polynomial. -/
theorem isPFPolynomial_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF ![P 0, P 1]) (n : ℕ) : IsPFPolynomial (P n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact (isOrderedPF_even_odd_of_recurrence P hrec hseed m).1 0
  · exact (isOrderedPF_even_odd_of_recurrence P hrec hseed m).1 1

/-- Every row of a family in the two-step orbit splits over the reals. -/
theorem splits_of_recurrence (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hseed : IsOrderedPF ![P 0, P 1]) (n : ℕ) : (P n).Splits :=
  (isPFPolynomial_of_recurrence P hrec hseed n).eq_zero_or_splits.elim
    (fun h => h ▸ Splits.zero) id

/-- The initial values `P 0 = 1` and `P 1 = X` supply the ordered seed needed by the orbit
theorem. -/
theorem isPFPolynomial_of_recurrence_one_X (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hzero : P 0 = 1) (hone : P 1 = X) (n : ℕ) : IsPFPolynomial (P n) := by
  apply isPFPolynomial_of_recurrence P hrec
  simpa [hzero, hone] using isOrderedPF_one_X

/-- Every recurrence family with initial values `(1,X)` splits in every row. -/
theorem splits_of_recurrence_one_X (P : ℕ → ℝ[X])
    (hrec : ∀ k, P (k + 2) = RealRooted.theta (P (k + 1)) + X * RealRooted.theta (P k))
    (hzero : P 0 = 1) (hone : P 1 = X) (n : ℕ) : (P n).Splits := by
  apply splits_of_recurrence P hrec
  simpa [hzero, hone] using isOrderedPF_one_X

end RealRooted.OperatorMatrix.EulerDerivativeLag
