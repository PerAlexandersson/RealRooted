module

public import RealRooted.OperatorMatrix.CouplingThresholds
public import RealRooted.OperatorMatrix.Bounded
public import RealRooted.EulerOperator
import RealRooted.OperatorMatrix.Directed
import RealRooted.ReciprocalShift.ProperPosition
import RealRooted.EulerOperator.Polar
import RealRooted.Mathlib.Algebra.QuadraticDiscriminant

/-!
# Bounded coupled first-order operators

We realize the diagonal data of `CouplingThresholds` as linear polynomial operators, prove
that both output coordinates are PF throughout the nonnegative parameter cone, and bound
output degrees by `N + 1`. The remaining directed comparison is isolated by the bounded
pair predicate. We also identify the scalar ray test with its two nonnegative quadratics.
These algebraic and coordinatewise results do not assert the operator/ray equivalence.

Source: unpublished manuscript, `independent-coupled-operators.md`, Sections 8--10, at
revision `d86187d` of `real-zero-preservers`; RealRooted issue #2150.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- All four coefficients of a coupling diagonal are nonnegative. -/
def CouplingDiagonal.Nonneg (p : CouplingDiagonal) : Prop :=
  0 ≤ p.a ∧ 0 ≤ p.b ∧ 0 ≤ p.c ∧ 0 ≤ p.e

/-- The operator `a I + b theta + X (c I + e (N I - theta))` in left normal form. -/
def CouplingDiagonal.linearMap (p : CouplingDiagonal) (N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  LinearMap.mulLeft ℝ (C p.a + C (p.c + N * p.e) * X) +
    (LinearMap.mulLeft ℝ (C p.b * X - C p.e * X ^ 2)).comp Polynomial.derivative

/-- Left normal form of a coupling diagonal. -/
theorem CouplingDiagonal.linearMap_apply (p : CouplingDiagonal) (N : ℕ) (q : ℝ[X]) :
    p.linearMap N q = (C p.a + C (p.c + N * p.e) * X) * q +
      (C p.b * X - C p.e * X ^ 2) * q.derivative := rfl

/-- Euler/polar form of a coupling diagonal, suitable for coefficient and cone arguments. -/
theorem CouplingDiagonal.linearMap_eq (p : CouplingDiagonal) (N : ℕ) (q : ℝ[X]) :
    p.linearMap N q = C p.a * q + C p.b * theta q +
      C p.c * (X * q) + C p.e * (X * polarTheta N q) := by
  simp only [linearMap_apply, theta, polarTheta, map_add, map_mul]
  ring

/-- The constant coefficient of a diagonal output has no derivative contribution. -/
@[simp]
theorem CouplingDiagonal.coeff_linearMap_zero (p : CouplingDiagonal) (N : ℕ) (q : ℝ[X]) :
    (p.linearMap N q).coeff 0 = p.a * q.coeff 0 := by
  simp [linearMap_eq, theta]

/-- The two nonzero bands in the coefficient action, including the degree-cap cancellation. -/
theorem CouplingDiagonal.coeff_linearMap_succ (p : CouplingDiagonal) (N k : ℕ)
    (q : ℝ[X]) :
    (p.linearMap N q).coeff (k + 1) =
      (p.a + p.b * ((k : ℝ) + 1)) * q.coeff (k + 1) +
        (p.c + p.e * ((N : ℝ) - k)) * q.coeff k := by
  simp only [linearMap_eq, coeff_add, coeff_C_mul, coeff_theta, coeff_X_mul,
    coeff_polarTheta, Nat.cast_add, Nat.cast_one]
  ring

/-- The nonnegative parameter cone preserves coefficientwise nonnegativity through the cap. -/
theorem CouplingDiagonal.hasNonnegCoeffs_linearMap {p : CouplingDiagonal} (hp : p.Nonneg)
    {N : ℕ} {q : ℝ[X]} (hq : HasNonnegCoeffs q) (hqN : q.natDegree ≤ N) :
    HasNonnegCoeffs (p.linearMap N q) := by
  rw [linearMap_eq]
  exact (((hasNonnegCoeffs_C_mul hp.1 hq).add
    (hasNonnegCoeffs_C_mul hp.2.1 hq.theta)).add
    (hasNonnegCoeffs_C_mul hp.2.2.1 hq.X_mul)).add
    (hasNonnegCoeffs_C_mul hp.2.2.2 (hq.polarTheta hqN).X_mul)

/-- Every diagonal raises degree by at most one, including zero and cancelled outputs. -/
theorem CouplingDiagonal.natDegree_linearMap_le (p : CouplingDiagonal) (N : ℕ) (q : ℝ[X]) :
    (p.linearMap N q).natDegree ≤ q.natDegree + 1 := by
  have hpolar : (polarTheta N q).natDegree ≤ q.natDegree := by
    exact (natDegree_sub_le _ _).trans
      (max_le (natDegree_C_mul_le _ _) (natDegree_theta_le q))
  have hX (r : ℝ[X]) : (X * r).natDegree ≤ r.natDegree + 1 := by
    simpa [Nat.add_comm] using (natDegree_mul_le (p := (X : ℝ[X])) (q := r))
  rw [linearMap_eq]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      exact max_le ((natDegree_C_mul_le _ _).trans (Nat.le_succ _))
        ((natDegree_C_mul_le _ _).trans ((natDegree_theta_le q).trans (Nat.le_succ _)))
    · exact (natDegree_C_mul_le _ _).trans (hX q)
  · exact (natDegree_C_mul_le _ _).trans ((hX _).trans (Nat.add_le_add_right hpolar 1))

/-- On the negative ray, the derivative multiplier is `-t` times the derivative weight. -/
theorem CouplingDiagonal.eval_linearMap_neg (p : CouplingDiagonal) (N : ℕ) (q : ℝ[X])
    (t : ℝ) :
    (p.linearMap N q).eval (-t) =
      p.diagonalEval N t * q.eval (-t) - t * p.derivativeWeight t * q.derivative.eval (-t) := by
  simp only [linearMap_apply, eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_pow,
    diagonalEval, derivativeWeight]
  ring

/-- Reflection of the Euler comparison supplies the zero-aware polar comparison. -/
private theorem polar_interl_self {N : ℕ} {q : ℝ[X]} (hq : IsPFPolynomial q)
    (hqN : q.natDegree ≤ N) : Interl (polarTheta N q) q := by
  have hr : IsPFPolynomial (reciprocalShift N q) := hq.reciprocalShift hqN
  have hrN : (reciprocalShift N q).natDegree ≤ N :=
    natDegree_reflect_le.trans (max_le le_rfl hqN)
  have h := reciprocalShift_reverses_interl hr (theta_preserves_pf hr) hrN
    ((natDegree_theta_le _).trans hrN) hr.interl_theta
  change Interl (reciprocalShift N (theta (reciprocalShift N q)))
    (reciprocalShift N (reciprocalShift N q)) at h
  rw [← polarTheta_eq_reciprocalShift_theta_reciprocalShift N q hqN] at h
  simpa only [reciprocalShift, reflect_reflect] using h

/-- A nonnegative coupling diagonal lies between its input and its `X` multiple in directed
proper position. Neither comparison requires a nonzero derivative weight. -/
theorem CouplingDiagonal.interl_linearMap {p : CouplingDiagonal} (hp : p.Nonneg)
    {N : ℕ} {q : ℝ[X]} (hq : IsPFPolynomial q) (hqN : q.natDegree ≤ N) :
    Interl q (p.linearMap N q) ∧ Interl (p.linearMap N q) (X * q) := by
  have hpolar := polarTheta_preserves_pf hq hqN
  have hqp : Interl q (X * polarTheta N q) :=
    (interl_iff_interl_X_mul hpolar hq).mp (polar_interl_self hq hqN)
  have hqX : Interl q (X * q) := (interl_iff_interl_X_mul hq hq).mp hq.interl_self
  have h₁ := hasNonnegCoeffs_C_mul hp.1 hq.hasNonnegCoeffs
  have h₂ := hasNonnegCoeffs_C_mul hp.2.1 (theta_preserves_pf hq).hasNonnegCoeffs
  have h₃ := hasNonnegCoeffs_C_mul hp.2.2.1 hq.X_mul.hasNonnegCoeffs
  have h₄ := hasNonnegCoeffs_C_mul hp.2.2.2 hpolar.X_mul.hasNonnegCoeffs
  rw [linearMap_eq]
  constructor
  · exact interl_add_right_of_common_left_of_nonneg
      (interl_add_right_of_common_left_of_nonneg
        (interl_add_right_of_common_left_of_nonneg
          (hq.interl_self.C_mul_right_of_nonneg hp.1)
          (hq.interl_theta.C_mul_right_of_nonneg hp.2.1) h₁ h₂)
        (hqX.C_mul_right_of_nonneg hp.2.2.1) (h₁.add h₂) h₃)
      (hqp.C_mul_right_of_nonneg hp.2.2.2) ((h₁.add h₂).add h₃) h₄
  · exact interl_add_left_of_common_right_of_nonneg
      (interl_add_left_of_common_right_of_nonneg
        (interl_add_left_of_common_right_of_nonneg
          (hqX.C_mul_left_of_nonneg hp.1)
          (hq.interl_theta_X_mul.C_mul_left_of_nonneg hp.2.1) h₁ h₂)
        (hq.X_mul.interl_self.C_mul_left_of_nonneg hp.2.2.1) (h₁.add h₂) h₃)
      ((polar_interl_self hq hqN).mul_X_both.C_mul_left_of_nonneg hp.2.2.2)
      ((h₁.add h₂).add h₃) h₄

/-- Every nonnegative coupling diagonal preserves PF polynomials through its cap. -/
theorem CouplingDiagonal.isPFPolynomial_linearMap {p : CouplingDiagonal} (hp : p.Nonneg)
    {N : ℕ} {q : ℝ[X]} (hq : IsPFPolynomial q) (hqN : q.natDegree ≤ N) :
    IsPFPolynomial (p.linearMap N q) := by
  by_cases hq0 : q = 0
  · simp [hq0, IsPFPolynomial.zero]
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (p.hasNonnegCoeffs_linearMap hp hq.hasNonnegCoeffs hqN)
  rcases (p.interl_linearMap hp hq hqN).1 with h | h | h
  · exact False.elim (hq0 h)
  · exact Or.inl h
  · exact Or.inr h.2.1.2

/-- The coupled block, with inputs `(g,f)` and outputs `(T₂g+vf,uXg+T₁f)`. -/
def couplingMatrix (N : ℕ) (p₁ p₂ : CouplingDiagonal) (u v : ℝ) :
    Fin 2 → Fin 2 → ℝ[X] →ₗ[ℝ] ℝ[X] :=
  ![![p₂.linearMap N, LinearMap.mulLeft ℝ (C v)],
    ![LinearMap.mulLeft ℝ (C u * X), p₁.linearMap N]]

/-- Coordinate PF preservation is automatic in the nonnegative cone, with no coupling inequality.
The separate directed output comparison is the nontrivial part of the exact threshold theorem. -/
theorem coupling_outputs_isPFPolynomial {N : ℕ} {p₁ p₂ : CouplingDiagonal}
    (hp₁ : p₁.Nonneg) (hp₂ : p₂.Nonneg) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    {g f : ℝ[X]} (hg : IsPFPolynomial g) (hf : IsPFPolynomial f) (hgf : Interl g f)
    (hgN : g.natDegree ≤ N) (hfN : f.natDegree ≤ N) :
    IsPFPolynomial (p₂.linearMap N g + C v * f) ∧
      IsPFPolynomial (C u * X * g + p₁.linearMap N f) := by
  have hGnn := (p₂.hasNonnegCoeffs_linearMap hp₂ hg.hasNonnegCoeffs hgN).add
    (hasNonnegCoeffs_C_mul hv hf.hasNonnegCoeffs)
  have hFnn := (hasNonnegCoeffs_C_mul hu hg.X_mul.hasNonnegCoeffs).add
    (p₁.hasNonnegCoeffs_linearMap hp₁ hf.hasNonnegCoeffs hfN)
  constructor
  · by_cases hg0 : g = 0
    · simpa [hg0] using (IsPFPolynomial.of_C_nonneg hv).mul hf
    have hright := interl_add_left_of_common_right_of_nonneg
      (p₂.interl_linearMap hp₂ hg hgN).2
      (((interl_iff_interl_X_mul hg hf).mp hgf).C_mul_left_of_nonneg hv)
      (p₂.hasNonnegCoeffs_linearMap hp₂ hg.hasNonnegCoeffs hgN)
      (hasNonnegCoeffs_C_mul hv hf.hasNonnegCoeffs)
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hGnn
    rcases hright with h | h | h
    · exact Or.inl h
    · exact False.elim (mul_ne_zero X_ne_zero hg0 h)
    · exact Or.inr h.1.2
  · by_cases hf0 : f = 0
    · simpa [hf0, mul_assoc] using (IsPFPolynomial.of_C_nonneg hu).mul hg.X_mul
    have hleft := interl_add_right_of_common_left_of_nonneg
      (((interl_iff_interl_X_mul hg hf).mp hgf).C_mul_right_of_nonneg hu)
      (p₁.interl_linearMap hp₁ hf hfN).1
      (hasNonnegCoeffs_C_mul hu hg.X_mul.hasNonnegCoeffs)
      (p₁.hasNonnegCoeffs_linearMap hp₁ hf.hasNonnegCoeffs hfN)
    rw [mul_assoc]
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hFnn
    rcases hleft with h | h | h
    · exact False.elim (hf0 h)
    · exact Or.inl (by simpa [mul_assoc] using h)
    · exact Or.inr (by simpa [mul_assoc] using h.2.1.2)

/-- Both coupled outputs satisfy the required successor cap, even when a leading term cancels. -/
theorem natDegree_coupling_outputs_le {N : ℕ} (p₁ p₂ : CouplingDiagonal) (u v : ℝ)
    {g f : ℝ[X]} (hgN : g.natDegree ≤ N) (hfN : f.natDegree ≤ N) :
    (p₂.linearMap N g + C v * f).natDegree ≤ N + 1 ∧
      (C u * X * g + p₁.linearMap N f).natDegree ≤ N + 1 := by
  have hgX : (C u * X * g).natDegree ≤ N + 1 := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_mul_le (p := (X : ℝ[X])) (q := g)).trans
        (by simpa [Nat.add_comm] using Nat.add_le_add_right hgN 1))
  exact ⟨(natDegree_add_le _ _).trans (max_le
    ((p₂.natDegree_linearMap_le N g).trans (Nat.add_le_add_right hgN 1))
    ((natDegree_C_mul_le _ _).trans (hfN.trans (Nat.le_succ _)))),
    (natDegree_add_le _ _).trans (max_le hgX
      ((p₁.natDegree_linearMap_le N f).trans (Nat.add_le_add_right hfN 1)))⟩

/-- For this nonnegative block, bounded preservation asks precisely for directed output order;
coordinatewise PF is already a theorem. This is a reduction, not a scalar ray classification. -/
theorem preservesOrderedPFUpTo_couplingMatrix_iff {N : ℕ} {p₁ p₂ : CouplingDiagonal}
    (hp₁ : p₁.Nonneg) (hp₂ : p₂.Nonneg) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    PreservesOrderedPFUpTo N (couplingMatrix N p₁ p₂ u v) ↔
      ∀ g f, IsPFPolynomial g → IsPFPolynomial f → Interl g f →
        g.natDegree ≤ N → f.natDegree ≤ N →
        Interl (p₂.linearMap N g + C v * f) (C u * X * g + p₁.linearMap N f) := by
  rw [PreservesOrderedPFUpTo.two_two_iff]
  constructor
  · intro h g f hg hf hgf hgN hfN
    exact (h g f hg hf hgf hgN hfN).2.2
  · intro h g f hg hf hgf hgN hfN
    exact ⟨(coupling_outputs_isPFPolynomial hp₁ hp₂ hu hv hg hf hgf hgN hfN).1,
      (coupling_outputs_isPFPolynomial hp₁ hp₂ hu hv hg hf hgf hgN hfN).2,
      h g f hg hf hgf hgN hfN⟩

/-- The derivative weight is nonnegative on the positive ray. -/
theorem CouplingDiagonal.derivativeWeight_nonneg {p : CouplingDiagonal} (hp : p.Nonneg)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ p.derivativeWeight t :=
  add_nonneg hp.2.1 (mul_nonneg hp.2.2.2 ht)

/-- An active nonnegative diagonal has strictly positive derivative weight on the positive ray. -/
theorem CouplingDiagonal.derivativeWeight_pos {p : CouplingDiagonal} (hp : p.Nonneg)
    (hactive : 0 < p.b + p.e) {t : ℝ} (ht : 0 < t) : 0 < p.derivativeWeight t := by
  by_cases hb : p.b = 0
  · have he : 0 < p.e := by simpa [hb] using hactive
    simpa [derivativeWeight, hb] using mul_pos he ht
  · have hbpos : 0 < p.b := lt_of_le_of_ne hp.2.1 (Ne.symm hb)
    exact add_pos_of_pos_of_nonneg hbpos (mul_nonneg hp.2.2.2 ht.le)

/-- The ray quadratic `J` is positive when both diagonal derivative terms are active. -/
theorem couplingJ_pos {p₁ p₂ : CouplingDiagonal} (hp₁ : p₁.Nonneg) (hp₂ : p₂.Nonneg)
    (h₁ : 0 < p₁.b + p₁.e) (h₂ : 0 < p₂.b + p₂.e) {t : ℝ} (ht : 0 < t) :
    0 < couplingJ p₁ p₂ t :=
  mul_pos (p₁.derivativeWeight_pos hp₁ h₁ ht) (p₂.derivativeWeight_pos hp₂ h₂ ht)

/-- Expansion of the positive ray quadratic in the manuscript's coefficients. -/
theorem couplingJ_eq (p₁ p₂ : CouplingDiagonal) (t : ℝ) :
    couplingJ p₁ p₂ t = p₁.b * p₂.b +
      (p₁.b * p₂.e + p₂.b * p₁.e) * t + p₁.e * p₂.e * t ^ 2 := by
  simp only [couplingJ, CouplingDiagonal.derivativeWeight]
  ring

/-- Expansion of the signed ray quadratic, with the exact degree-cap contribution. -/
theorem couplingS_eq (N : ℕ) (p₁ p₂ : CouplingDiagonal) (t : ℝ) :
    couplingS N p₁ p₂ t = p₂.a * p₁.b - p₁.a * p₂.b +
      (p₂.a * p₁.e - p₁.a * p₂.e + p₁.c * p₂.b - p₂.c * p₁.b +
        N * (p₂.b * p₁.e - p₁.b * p₂.e)) * t +
      (p₁.c * p₂.e - p₂.c * p₁.e) * t ^ 2 := by
  simp only [couplingS, CouplingDiagonal.derivativeWeight, CouplingDiagonal.diagonalEval]
  ring

/-- Elimination of a positive scalar from a quadratic with nonnegative end coefficients. -/
private theorem quadratic_nonneg_pos_iff {A B C₀ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C₀) :
    (∀ r : ℝ, 0 < r → 0 ≤ A + B * r + C₀ * r ^ 2) ↔
      0 ≤ B ∨ B ^ 2 ≤ 4 * A * C₀ := by
  constructor
  · intro h
    by_cases hB : 0 ≤ B
    · exact Or.inl hB
    right
    have hd := discrim_le_zero (a := C₀) (b := B) (c := A) (fun r => by
      by_cases hr : 0 < r
      · nlinarith [h r hr]
      · have hBr : 0 ≤ B * r :=
          mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hB) (le_of_not_gt hr)
        nlinarith [mul_nonneg hC (sq_nonneg r)])
    dsimp [discrim] at hd
    nlinarith
  · rintro (hB | hB) r hr
    · positivity
    · have hd : discrim C₀ B A ≤ 0 := by dsimp [discrim]; nlinarith
      have h := Quadratic.nonneg_of_nonneg_of_discrim_nonpos hC hA hd r
      nlinarith

/-- The square-root-free coupling test is equivalent to the two ray quadratics of the block
classification. This is scalar quantifier elimination; it does not assume or prove the
operator-preservation classification. The equivalence includes zero couplings and weights. -/
theorem couplingRayCriterion_iff_quadratic_nonneg {N : ℕ} {p₁ p₂ : CouplingDiagonal}
    (hp₁ : p₁.Nonneg) (hp₂ : p₂.Nonneg) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    CouplingRayCriterion (couplingJ p₁ p₂) (couplingS N p₁ p₂) (u * v) ↔
      ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r →
        0 ≤ u * t * p₂.derivativeWeight t + couplingS N p₁ p₂ t * r +
          v * p₁.derivativeWeight t * r ^ 2 ∧
        0 ≤ u * t * p₂.derivativeWeight t +
          (couplingJ p₁ p₂ t - couplingS N p₁ p₂ t) * r +
          v * p₁.derivativeWeight t * r ^ 2 := by
  have hside (t : ℝ) (ht : 0 < t) (B : ℝ) :
      (∀ r : ℝ, 0 < r → 0 ≤ u * t * p₂.derivativeWeight t + B * r +
        v * p₁.derivativeWeight t * r ^ 2) ↔
        0 ≤ B ∨ B ^ 2 ≤ 4 * (u * v) * t * couplingJ p₁ p₂ t := by
    rw [quadratic_nonneg_pos_iff
      (mul_nonneg (mul_nonneg hu ht.le) (p₂.derivativeWeight_nonneg hp₂ ht.le))
      (mul_nonneg hv (p₁.derivativeWeight_nonneg hp₁ ht.le))]
    have heq : 4 * (u * t * p₂.derivativeWeight t) * (v * p₁.derivativeWeight t) =
        4 * (u * v) * t * couplingJ p₁ p₂ t := by
      simp only [couplingJ]
      ring
    rw [heq]
  constructor
  · intro h t ht r hr
    have hs := h t ht
    exact ⟨(hside t ht _).mpr hs.1 r hr,
      (hside t ht _).mpr (by simpa only [sub_nonneg] using hs.2) r hr⟩
  · intro h t ht
    exact ⟨(hside t ht _).mp (fun r hr => (h t ht r hr).1),
      by simpa only [sub_nonneg] using
        (hside t ht _).mp (fun r hr => (h t ht r hr).2)⟩

end RealRooted.OperatorMatrix
