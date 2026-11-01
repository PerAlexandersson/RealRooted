module

public import RealRooted.PFPolynomial
import RealRooted.AffineProperPosition
import RealRooted.OperatorMatrix.Directed
import RealRooted.FiniteFreeRootCount
import RealRooted.FiniteMemory.Defect

/-!
# A three-coordinate cubic transition

This module packages the ordered Pólya-frequency triple preserved by the
transition `(q, p, r) ↦ (αq + p, r, γr + wXq)`.  It also records the
polynomial certificate that turns a cubic recurrence into the recurrence of
each every-third subsequence.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Three Pólya-frequency polynomials in pairwise directed interlacing order. -/
@[expose] def IsOrderedPFTriple (q p r : ℝ[X]) : Prop :=
  IsPFPolynomial q ∧ IsPFPolynomial p ∧ IsPFPolynomial r ∧
    Interl q p ∧ Interl q r ∧ Interl p r

/-- The cubic transition preserves every ordered Pólya-frequency triple. -/
@[expose] def PreservesCubicTransition (α γ w : ℝ) : Prop :=
  ∀ q p r : ℝ[X], IsOrderedPFTriple q p r →
    IsOrderedPFTriple (C α * q + p) r (C γ * r + C w * (X * q))

/-- Nonnegative parameters make the three-coordinate cubic transition preserve
ordered Pólya-frequency triples, including triples and outputs with zero coordinates. -/
theorem preservesCubicTransition_of_nonneg {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hw : 0 ≤ w) :
    PreservesCubicTransition α γ w := by
  intro q p r h
  rcases h with ⟨hq, hp, hr, hqp, hqr, hpr⟩
  have hqXq : Interl q (X * q) :=
    interl_mul_X_of_interl hq.interl_self hq.hasNonnegCoeffs hq.hasNonnegCoeffs
  have hpXq : Interl p (X * q) :=
    interl_mul_X_of_interl hqp hq.hasNonnegCoeffs hp.hasNonnegCoeffs
  have hrXq : Interl r (X * q) :=
    interl_mul_X_of_interl hqr hq.hasNonnegCoeffs hr.hasNonnegCoeffs
  have hαq : IsPFPolynomial (C α * q) :=
    (IsPFPolynomial.of_C_nonneg hα).mul hq
  have hγr : IsPFPolynomial (C γ * r) :=
    (IsPFPolynomial.of_C_nonneg hγ).mul hr
  have hwXq : IsPFPolynomial (C w * (X * q)) :=
    (IsPFPolynomial.of_C_nonneg hw).mul hq.X_mul
  have hA_pf : IsPFPolynomial (C α * q + p) :=
    hαq.add_of_interl hp (hqp.C_mul_left_of_nonneg hα)
  have hC_pf : IsPFPolynomial (C γ * r + C w * (X * q)) :=
    hγr.add_of_interl hwXq
      ((hrXq.C_mul_left_of_nonneg hγ).C_mul_right_of_nonneg hw)
  have hAr : Interl (C α * q + p) r :=
    interl_add_left_of_common_right_of_nonneg
      (hqr.C_mul_left_of_nonneg hα) hpr hαq.hasNonnegCoeffs hp.hasNonnegCoeffs
  have hAXq : Interl (C α * q + p) (X * q) :=
    interl_add_left_of_common_right_of_nonneg
      (hqXq.C_mul_left_of_nonneg hα) hpXq hαq.hasNonnegCoeffs hp.hasNonnegCoeffs
  have hAC : Interl (C α * q + p) (C γ * r + C w * (X * q)) :=
    interl_add_right_of_common_left_of_nonneg
      (hAr.C_mul_right_of_nonneg hγ) (hAXq.C_mul_right_of_nonneg hw)
      hγr.hasNonnegCoeffs hwXq.hasNonnegCoeffs
  have hrC : Interl r (C γ * r + C w * (X * q)) :=
    interl_add_right_of_common_left_of_nonneg
      (hr.interl_self.C_mul_right_of_nonneg hγ) (hrXq.C_mul_right_of_nonneg hw)
      hγr.hasNonnegCoeffs hwXq.hasNonnegCoeffs
  exact ⟨hA_pf, hr, hC_pf, hAr, hAC, hrC⟩

/-- The three-coordinate cubic transition preserves all ordered PF triples
exactly when all three scalar parameters are nonnegative. -/
theorem preservesCubicTransition_iff_nonneg (α γ w : ℝ) :
    PreservesCubicTransition α γ w ↔ 0 ≤ α ∧ 0 ≤ γ ∧ 0 ≤ w := by
  constructor
  · intro h
    have h100 : IsOrderedPFTriple (1 : ℝ[X]) 0 0 :=
      ⟨IsPFPolynomial.one, IsPFPolynomial.zero, IsPFPolynomial.zero,
        interl_zero_right 1, interl_zero_right 1, interl_zero_left 0⟩
    have h001 : IsOrderedPFTriple (0 : ℝ[X]) 0 1 :=
      ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, IsPFPolynomial.one,
        interl_zero_left 0, interl_zero_left 1, interl_zero_left 1⟩
    have hout100 := h 1 0 0 h100
    have hout001 := h 0 0 1 h001
    refine ⟨?_, ?_, ?_⟩
    · simpa [IsOrderedPFTriple] using hout100.1.hasNonnegCoeffs 0
    · simpa [IsOrderedPFTriple] using hout001.2.2.1.hasNonnegCoeffs 0
    · simpa [IsOrderedPFTriple] using hout100.2.2.1.hasNonnegCoeffs 1
  · rintro ⟨hα, hγ, hw⟩
    exact preservesCubicTransition_of_nonneg hα hγ hw

/-- A state for the three-coordinate cubic transition. -/
structure CubicTransitionState where
  /-- The auxiliary coordinate feeding the delayed `X` term. -/
  q : ℝ[X]
  /-- The first row coordinate. -/
  p : ℝ[X]
  /-- The second row coordinate. -/
  r : ℝ[X]

/-- One step of the three-coordinate cubic transition. -/
def cubicTransitionStep (α γ w : ℝ) (S : CubicTransitionState) :
    CubicTransitionState where
  q := C α * S.q + S.p
  p := S.r
  r := C γ * S.r + C w * (X * S.q)

/-- The last coordinate after two transitions, allowing the parameters to vary. -/
theorem cubicTransitionStep_two_r (α0 γ0 w0 α1 γ1 w1 : ℝ)
    (S : CubicTransitionState) :
    (cubicTransitionStep α1 γ1 w1 (cubicTransitionStep α0 γ0 w0 S)).r =
      C (γ1 * γ0) * S.r + C (γ1 * w0 + w1 * α0) * (X * S.q) +
        C w1 * (X * S.p) := by
  simp [cubicTransitionStep]
  ring

/-- In an ordered PF state, its middle coordinate precedes the last coordinate
after two transitions with independently varying nonnegative parameters. -/
theorem interl_cubicTransitionStep_two_r_of_nonneg
    {α0 γ0 w0 α1 γ1 w1 : ℝ} {S : CubicTransitionState}
    (hα0 : 0 ≤ α0) (hγ0 : 0 ≤ γ0) (hw0 : 0 ≤ w0)
    (hγ1 : 0 ≤ γ1) (hw1 : 0 ≤ w1)
    (hS : IsOrderedPFTriple S.q S.p S.r) :
    Interl S.p
      (cubicTransitionStep α1 γ1 w1 (cubicTransitionStep α0 γ0 w0 S)).r := by
  have hpXq : Interl S.p (X * S.q) :=
    interl_mul_X_of_interl hS.2.2.2.1 hS.1.hasNonnegCoeffs hS.2.1.hasNonnegCoeffs
  have hpXp : Interl S.p (X * S.p) :=
    interl_mul_X_of_interl hS.2.1.interl_self
      hS.2.1.hasNonnegCoeffs hS.2.1.hasNonnegCoeffs
  have hfirst :
      Interl S.p (C (γ1 * γ0) * S.r + C (γ1 * w0 + w1 * α0) * (X * S.q)) :=
    interl_add_right_of_common_left_of_nonneg
      (hS.2.2.2.2.2.C_mul_right_of_nonneg (mul_nonneg hγ1 hγ0))
      (hpXq.C_mul_right_of_nonneg
        (add_nonneg (mul_nonneg hγ1 hw0) (mul_nonneg hw1 hα0)))
      (hasNonnegCoeffs_C_mul (mul_nonneg hγ1 hγ0) hS.2.2.1.hasNonnegCoeffs)
      (hasNonnegCoeffs_C_mul
        (add_nonneg (mul_nonneg hγ1 hw0) (mul_nonneg hw1 hα0))
        hS.1.X_mul.hasNonnegCoeffs)
  rw [cubicTransitionStep_two_r]
  exact interl_add_right_of_common_left_of_nonneg hfirst
    (hpXp.C_mul_right_of_nonneg hw1)
    ((hasNonnegCoeffs_C_mul (mul_nonneg hγ1 hγ0) hS.2.2.1.hasNonnegCoeffs).add
      (hasNonnegCoeffs_C_mul
        (add_nonneg (mul_nonneg hγ1 hw0) (mul_nonneg hw1 hα0))
        hS.1.X_mul.hasNonnegCoeffs))
    (hasNonnegCoeffs_C_mul hw1 hS.2.1.X_mul.hasNonnegCoeffs)

/-- The state after `n` transitions from `(1, γ, γ²)`. -/
def cubicTransitionIterate (α γ w : ℝ) : ℕ → CubicTransitionState
  | 0 => ⟨1, C γ, C (γ ^ 2)⟩
  | n + 1 => cubicTransitionStep α γ w (cubicTransitionIterate α γ w n)

/-- The scalar family projected from the cubic transition, with initial value one. -/
def cubicTransitionFamily (α γ w : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (cubicTransitionIterate α γ w n).p

/-- Every state in the nonnegative-parameter orbit is an ordered PF triple. -/
theorem cubicTransitionIterate_isOrderedPFTriple {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hw : 0 ≤ w) (n : ℕ) :
    IsOrderedPFTriple (cubicTransitionIterate α γ w n).q
      (cubicTransitionIterate α γ w n).p
      (cubicTransitionIterate α γ w n).r := by
  induction n with
  | zero =>
      exact ⟨IsPFPolynomial.one, IsPFPolynomial.of_C_nonneg hγ,
        IsPFPolynomial.of_C_nonneg (sq_nonneg γ), interl_C_C 1 γ,
        interl_C_C 1 (γ ^ 2), interl_C_C γ (γ ^ 2)⟩
  | succ n ih =>
      simpa [cubicTransitionIterate, cubicTransitionStep] using
        preservesCubicTransition_of_nonneg hα hγ hw _ _ _ ih

/-- The projected family has the initial values `1`, `γ`, and `γ²`. -/
theorem cubicTransitionFamily_initial (α γ w : ℝ) :
    cubicTransitionFamily α γ w 0 = 1 ∧
      cubicTransitionFamily α γ w 1 = C γ ∧
      cubicTransitionFamily α γ w 2 = C (γ ^ 2) := by
  simp [cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep, map_pow]

/-- The projected family satisfies the constant-coefficient cubic recurrence. -/
theorem cubicTransitionFamily_recurrence (α γ w : ℝ) (n : ℕ) :
    cubicTransitionFamily α γ w (n + 3) =
      C (α + γ) * cubicTransitionFamily α γ w (n + 2) -
      C (α * γ) * cubicTransitionFamily α γ w (n + 1) +
      C w * X * cubicTransitionFamily α γ w n := by
  cases n with
  | zero =>
      simp [cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep]
      ring
  | succ n =>
      simp [cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep]
      ring

private lemma cubicTransitionIterate_coeff_zero (α γ w : ℝ) (n : ℕ) :
    (cubicTransitionIterate α γ w n).p.coeff 0 = γ ^ (n + 1) ∧
      (cubicTransitionIterate α γ w n).r.coeff 0 = γ ^ (n + 2) := by
  induction n with
  | zero =>
      constructor
      · simp [cubicTransitionIterate]
      · simp only [cubicTransitionIterate, coeff_C_zero, Nat.zero_add]
  | succ n ih =>
      simp [cubicTransitionIterate, cubicTransitionStep, ih, pow_succ]
      ring

/-- The constant coefficient of the `n`th row is `γⁿ`. -/
theorem cubicTransitionFamily_coeff_zero (α γ w : ℝ) (n : ℕ) :
    (cubicTransitionFamily α γ w n).coeff 0 = γ ^ n := by
  cases n with
  | zero => simp [cubicTransitionFamily]
  | succ n =>
      exact (cubicTransitionIterate_coeff_zero α γ w n).1

/-- Every row of the nonnegative-parameter cubic family is PF. -/
theorem cubicTransitionFamily_isPFPolynomial {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hw : 0 ≤ w) (n : ℕ) :
    IsPFPolynomial (cubicTransitionFamily α γ w n) := by
  cases n with
  | zero => exact IsPFPolynomial.one
  | succ n => exact (cubicTransitionIterate_isOrderedPFTriple hα hγ hw n).2.1

/-- Positive `γ` makes every row nonzero. -/
theorem cubicTransitionFamily_ne_zero_of_pos {α γ w : ℝ} (hγ : 0 < γ) (n : ℕ) :
    cubicTransitionFamily α γ w n ≠ 0 := by
  intro hzero
  have hcoeff := cubicTransitionFamily_coeff_zero α γ w n
  rw [hzero] at hcoeff
  simp at hcoeff
  exact (pow_pos hγ n).ne' hcoeff.symm

/-- Under nonnegative parameters and positive `γ`, every root of every row is negative. -/
theorem cubicTransitionFamily_roots_neg {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 < γ) (hw : 0 ≤ w) (n : ℕ) :
    ∀ x ∈ (cubicTransitionFamily α γ w n).roots, x < 0 := by
  apply (cubicTransitionFamily_isPFPolynomial hα hγ.le hw n).roots_neg_of_coeff_zero_ne
  rw [cubicTransitionFamily_coeff_zero]
  exact (pow_pos hγ n).ne'

private lemma cubicTransitionIterate_ne_zero {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 < γ) (hw : 0 ≤ w) (n : ℕ) :
    (cubicTransitionIterate α γ w n).q ≠ 0 ∧
      (cubicTransitionIterate α γ w n).p ≠ 0 ∧
      (cubicTransitionIterate α γ w n).r ≠ 0 := by
  induction n with
  | zero => simp [cubicTransitionIterate, hγ.ne']
  | succ n ih =>
      have h := cubicTransitionIterate_isOrderedPFTriple hα hγ.le hw n
      simp only [cubicTransitionIterate, cubicTransitionStep]
      refine ⟨add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        (hasNonnegCoeffs_C_mul hα h.1.hasNonnegCoeffs) h.2.1.hasNonnegCoeffs ih.2.1,
        ih.2.2, ?_⟩
      rw [add_comm]
      exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        (hasNonnegCoeffs_C_mul hw h.1.X_mul.hasNonnegCoeffs)
        (hasNonnegCoeffs_C_mul hγ.le h.2.2.1.hasNonnegCoeffs)
        (mul_ne_zero (C_ne_zero.mpr hγ.ne') ih.2.2)

private lemma cubicTransitionStep_natDegree {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 < γ) (hw : 0 < w) {S : CubicTransitionState}
    (hS : IsOrderedPFTriple S.q S.p S.r) (hne : S.q ≠ 0 ∧ S.p ≠ 0 ∧ S.r ≠ 0) :
    (cubicTransitionStep α γ w S).q.natDegree = S.p.natDegree ∧
      (cubicTransitionStep α γ w S).p.natDegree = S.r.natDegree ∧
      (cubicTransitionStep α γ w S).r.natDegree = S.q.natDegree + 1 := by
  have hqp : S.q.natDegree ≤ S.p.natDegree :=
    (hS.2.2.2.1.toStrictInterl_of_ne hne.1 hne.2.1).natDegree_le
  have hqr : S.r.natDegree ≤ S.q.natDegree + 1 :=
    (hS.2.2.2.2.1.toStrictInterl_of_ne hne.1 hne.2.2).natDegree_le_succ
  have hqstep : (C α * S.q + S.p).natDegree = S.p.natDegree := by
    rcases hα.eq_or_lt with rfl | hαpos
    · simp
    · rw [(hasNonnegCoeffs_C_mul hαpos.le hS.1.hasNonnegCoeffs).natDegree_add_eq_max
          hS.2.1.hasNonnegCoeffs (mul_ne_zero (C_ne_zero.mpr hαpos.ne') hne.1) hne.2.1,
        natDegree_C_mul hαpos.ne', max_eq_right hqp]
  have hrstep : (C γ * S.r + C w * (X * S.q)).natDegree = S.q.natDegree + 1 := by
    rw [(hasNonnegCoeffs_C_mul hγ.le hS.2.2.1.hasNonnegCoeffs).natDegree_add_eq_max
        (hasNonnegCoeffs_C_mul hw.le hS.1.X_mul.hasNonnegCoeffs)
        (mul_ne_zero (C_ne_zero.mpr hγ.ne') hne.2.2)
        (mul_ne_zero (C_ne_zero.mpr hw.ne') (mul_ne_zero X_ne_zero hne.1)),
      natDegree_C_mul hγ.ne', natDegree_C_mul hw.ne',
      natDegree_mul X_ne_zero hne.1, natDegree_X, max_eq_right (by lia)]
    lia
  exact ⟨by simpa [cubicTransitionStep] using hqstep, rfl,
    by simpa [cubicTransitionStep] using hrstep⟩

/-- For positive `γ` and `w`, the three state degrees are
`n / 3`, `(n + 1) / 3`, and `(n + 2) / 3`. -/
theorem cubicTransitionIterate_natDegree {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 < γ) (hw : 0 < w) (n : ℕ) :
    (cubicTransitionIterate α γ w n).q.natDegree = n / 3 ∧
      (cubicTransitionIterate α γ w n).p.natDegree = (n + 1) / 3 ∧
      (cubicTransitionIterate α γ w n).r.natDegree = (n + 2) / 3 := by
  induction n with
  | zero => simp [cubicTransitionIterate]
  | succ n ih =>
      have hstep := cubicTransitionStep_natDegree hα hγ hw
        (cubicTransitionIterate_isOrderedPFTriple hα hγ.le hw.le n)
        (cubicTransitionIterate_ne_zero hα hγ hw.le n)
      simp only [cubicTransitionIterate]
      refine ⟨hstep.1.trans ih.2.1, hstep.2.1.trans ih.2.2, ?_⟩
      rw [hstep.2.2, ih.1]
      simp [Nat.add_assoc]

/-- For positive `γ` and `w`, the `n`th row has degree `⌊n / 3⌋`. -/
theorem cubicTransitionFamily_natDegree {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 < γ) (hw : 0 < w) (n : ℕ) :
    (cubicTransitionFamily α γ w n).natDegree = n / 3 := by
  cases n with
  | zero => simp [cubicTransitionFamily]
  | succ n => exact (cubicTransitionIterate_natDegree hα hγ hw n).2.1

private lemma cubicTransitionIterate_zero_weight (α γ : ℝ) (n : ℕ) :
    (cubicTransitionIterate α γ 0 n).p = C (γ ^ (n + 1)) ∧
      (cubicTransitionIterate α γ 0 n).r = C (γ ^ (n + 2)) := by
  induction n with
  | zero => simp [cubicTransitionIterate, map_pow]
  | succ n ih =>
      simp only [cubicTransitionIterate, cubicTransitionStep]
      constructor
      · simpa [Nat.add_assoc] using ih.2
      · rw [ih.2, ← map_mul]
        simp [pow_succ, Nat.add_assoc, mul_comm]

/-- At weight zero the scalar family is the geometric sequence `γⁿ`. -/
theorem cubicTransitionFamily_zero_weight (α γ : ℝ) (n : ℕ) :
    cubicTransitionFamily α γ 0 n = C (γ ^ n) := by
  cases n with
  | zero => simp [cubicTransitionFamily]
  | succ n => exact (cubicTransitionIterate_zero_weight α γ n).1

/-- Consecutive rows of the cubic family are in directed weak interlacing order. -/
theorem cubicTransitionFamily_interl_add_one {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hw : 0 ≤ w) (n : ℕ) :
    Interl (cubicTransitionFamily α γ w n)
      (cubicTransitionFamily α γ w (n + 1)) := by
  cases n with
  | zero =>
      simpa [cubicTransitionFamily, cubicTransitionIterate] using interl_C_C 1 γ
  | succ n =>
      have h := cubicTransitionIterate_isOrderedPFTriple hα hγ hw n
      simpa [cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep] using
        h.2.2.2.2.2

/-- Rows at distance two in the cubic family are in directed weak interlacing order. -/
theorem cubicTransitionFamily_interl_add_two {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hw : 0 ≤ w) (n : ℕ) :
    Interl (cubicTransitionFamily α γ w n)
      (cubicTransitionFamily α γ w (n + 2)) := by
  cases n with
  | zero =>
      convert interl_C_C 1 (γ ^ 2) using 1 <;>
        simp [cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep]
  | succ n =>
      let S := cubicTransitionIterate α γ w n
      have h := cubicTransitionIterate_isOrderedPFTriple hα hγ hw n
      have hpXq : Interl S.p (X * S.q) :=
        interl_mul_X_of_interl h.2.2.2.1 h.1.hasNonnegCoeffs h.2.1.hasNonnegCoeffs
      have hout : Interl S.p (C γ * S.r + C w * (X * S.q)) :=
        interl_add_right_of_common_left_of_nonneg
          (h.2.2.2.2.2.C_mul_right_of_nonneg hγ) (hpXq.C_mul_right_of_nonneg hw)
          (hasNonnegCoeffs_C_mul hγ h.2.2.1.hasNonnegCoeffs)
          (hasNonnegCoeffs_C_mul hw h.1.X_mul.hasNonnegCoeffs)
      simpa [S, cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep] using hout

/-- Rows at distance three in the cubic family are in directed weak interlacing order. -/
theorem cubicTransitionFamily_interl_add_three {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hw : 0 ≤ w) (n : ℕ) :
    Interl (cubicTransitionFamily α γ w n)
      (cubicTransitionFamily α γ w (n + 3)) := by
  cases n with
  | zero =>
      have honeX : Interl (1 : ℝ[X]) X := by
        simpa using (interl_mul_X_of_interl IsPFPolynomial.one.interl_self
          IsPFPolynomial.one.hasNonnegCoeffs IsPFPolynomial.one.hasNonnegCoeffs)
      have hout : Interl (1 : ℝ[X]) (C (γ ^ 3) + C w * X) :=
        interl_add_right_of_common_left_of_nonneg (interl_C_C 1 (γ ^ 3))
          (by simpa using honeX.C_mul_right_of_nonneg hw)
          (hasNonnegCoeffs_C (by positivity))
          (hasNonnegCoeffs_C_mul hw hasNonnegCoeffs_X)
      convert hout using 1
      · simp [cubicTransitionFamily]
      · simp [cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep]
        ring
  | succ n =>
      let S := cubicTransitionIterate α γ w n
      have h := cubicTransitionIterate_isOrderedPFTriple hα hγ hw n
      have hpXq : Interl S.p (X * S.q) :=
        interl_mul_X_of_interl h.2.2.2.1 h.1.hasNonnegCoeffs h.2.1.hasNonnegCoeffs
      have hpXp : Interl S.p (X * S.p) :=
        interl_mul_X_of_interl h.2.1.interl_self
          h.2.1.hasNonnegCoeffs h.2.1.hasNonnegCoeffs
      have hfirst :
          Interl S.p (C (γ ^ 2) * S.r + C (w * (α + γ)) * (X * S.q)) :=
        interl_add_right_of_common_left_of_nonneg
          (h.2.2.2.2.2.C_mul_right_of_nonneg (sq_nonneg γ))
          (hpXq.C_mul_right_of_nonneg (mul_nonneg hw (add_nonneg hα hγ)))
          (hasNonnegCoeffs_C_mul (sq_nonneg γ) h.2.2.1.hasNonnegCoeffs)
          (hasNonnegCoeffs_C_mul (mul_nonneg hw (add_nonneg hα hγ))
            h.1.X_mul.hasNonnegCoeffs)
      have hout :
          Interl S.p
            (C (γ ^ 2) * S.r + C (w * (α + γ)) * (X * S.q) + C w * (X * S.p)) :=
        interl_add_right_of_common_left_of_nonneg hfirst
          (hpXp.C_mul_right_of_nonneg hw)
          ((hasNonnegCoeffs_C_mul (sq_nonneg γ) h.2.2.1.hasNonnegCoeffs).add
            (hasNonnegCoeffs_C_mul (mul_nonneg hw (add_nonneg hα hγ))
              h.1.X_mul.hasNonnegCoeffs))
          (hasNonnegCoeffs_C_mul hw h.2.1.X_mul.hasNonnegCoeffs)
      convert hout using 1
      · simp [S, cubicTransitionFamily]
      · simp [S, cubicTransitionFamily, cubicTransitionIterate, cubicTransitionStep]
        ring

/-- Consecutive rows in every residue class modulo three interlace in the
ordinary one-degree-gap sense. -/
theorem cubicTransitionFamily_residue_interlaces {α γ w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 < γ) (hw : 0 < w) {j : ℕ} (hj : j < 3) (n : ℕ) :
    Interlaces (cubicTransitionFamily α γ w (3 * n + j))
      (cubicTransitionFamily α γ w (3 * (n + 1) + j)) := by
  have hinterl := cubicTransitionFamily_interl_add_three hα hγ.le hw.le (3 * n + j)
  have hstrict := hinterl.toStrictInterl_of_ne
    (cubicTransitionFamily_ne_zero_of_pos hγ (3 * n + j))
    (cubicTransitionFamily_ne_zero_of_pos hγ (3 * n + j + 3))
  have hdegree :
      (cubicTransitionFamily α γ w (3 * n + j)).natDegree + 1 =
        (cubicTransitionFamily α γ w (3 * n + j + 3)).natDegree := by
    rw [cubicTransitionFamily_natDegree hα hγ hw,
      cubicTransitionFamily_natDegree hα hγ hw]
    simp [Nat.mul_add_div (by norm_num : 0 < 3), Nat.div_eq_of_lt hj]
  convert hstrict.toInterlaces hdegree using 1
  congr 1
  lia

/-- The residual of the cubic recurrence
`H (n + 3) = p H (n + 2) - q H (n + 1) + u H n`. -/
@[expose] def cubicResidual {R : Type*} [Ring R]
    (p q u : R) (H : ℕ → R) (n : ℕ) : R :=
  H (n + 3) - p * H (n + 2) + q * H (n + 1) - u * H n

/-- Explicit factor certificate for replacing a cubic characteristic polynomial
by the characteristic polynomial governing every-third subsequences. -/
theorem cubicCharacteristic_mul_certificate {R : Type*} [CommRing R]
    (p q u z : R) :
    (z ^ 3 - p * z ^ 2 + q * z - u) *
        (z ^ 6 + p * z ^ 5 + (p ^ 2 - q) * z ^ 4 + (p * q - 2 * u) * z ^ 3 +
          (q ^ 2 - p * u) * z ^ 2 + q * u * z + u ^ 2) =
      z ^ 9 - (p ^ 3 - 3 * p * q + 3 * u) * z ^ 6 +
        (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * z ^ 3 - u ^ 3 := by
  ring

/-- The seven shifted cubic residuals combine to the residual of the
every-third recurrence. -/
theorem cubicResidual_gap_three {R : Type*} [CommRing R]
    (p q u : R) (H : ℕ → R) (m : ℕ) :
    H (m + 9) - (p ^ 3 - 3 * p * q + 3 * u) * H (m + 6) +
          (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * H (m + 3) - u ^ 3 * H m =
      cubicResidual p q u H (m + 6) + p * cubicResidual p q u H (m + 5) +
        (p ^ 2 - q) * cubicResidual p q u H (m + 4) +
        (p * q - 2 * u) * cubicResidual p q u H (m + 3) +
        (q ^ 2 - p * u) * cubicResidual p q u H (m + 2) +
        q * u * cubicResidual p q u H (m + 1) + u ^ 2 * cubicResidual p q u H m := by
  simp only [cubicResidual]
  ring

/-- Every solution of a cubic recurrence satisfies the induced gap-three recurrence. -/
theorem cubicRecurrence_gap_three {R : Type*} [CommRing R]
    (p q u : R) (H : ℕ → R)
    (hrec : ∀ n, H (n + 3) = p * H (n + 2) - q * H (n + 1) + u * H n)
    (m : ℕ) :
    H (m + 9) = (p ^ 3 - 3 * p * q + 3 * u) * H (m + 6) -
      (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * H (m + 3) + u ^ 3 * H m := by
  have hzero (n : ℕ) : cubicResidual p q u H n = 0 := by
    rw [cubicResidual, hrec]
    ring
  have h := cubicResidual_gap_three p q u H m
  simp only [hzero, mul_zero, add_zero] at h
  linear_combination h

/-- Each fixed-residue subsequence of a cubic recurrence satisfies the same
cubic recurrence with the cubed characteristic roots. -/
theorem cubicRecurrence_residue_three {R : Type*} [CommRing R]
    (p q u : R) (H : ℕ → R)
    (hrec : ∀ n, H (n + 3) = p * H (n + 2) - q * H (n + 1) + u * H n)
    (j n : ℕ) :
    H (3 * (n + 3) + j) =
      (p ^ 3 - 3 * p * q + 3 * u) * H (3 * (n + 2) + j) -
      (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) * H (3 * (n + 1) + j) +
      u ^ 3 * H (3 * n + j) := by
  convert cubicRecurrence_gap_three p q u H hrec (3 * n + j) using 1 <;> congr 1 <;> lia

/-- The fixed-residue subsequences of `cubicTransitionFamily` satisfy the
explicit cubic recurrence obtained from the characteristic certificate. -/
theorem cubicTransitionFamily_residue_recurrence (α γ w : ℝ) (j n : ℕ) :
    let p : ℝ[X] := C (α + γ)
    let q : ℝ[X] := C (α * γ)
    let u : ℝ[X] := C w * X
    cubicTransitionFamily α γ w (3 * (n + 3) + j) =
      (p ^ 3 - 3 * p * q + 3 * u) *
          cubicTransitionFamily α γ w (3 * (n + 2) + j) -
        (q ^ 3 - 3 * p * q * u + 3 * u ^ 2) *
          cubicTransitionFamily α γ w (3 * (n + 1) + j) +
        u ^ 3 * cubicTransitionFamily α γ w (3 * n + j) := by
  dsimp only
  apply cubicRecurrence_residue_three
  intro k
  simpa only [mul_assoc] using cubicTransitionFamily_recurrence α γ w k

end RealRooted
