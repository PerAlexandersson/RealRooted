module

public import RealRooted.EulerOperator.Darboux.NegativeRoots
public import RealRooted.EulerOperator
import RealRooted.AffineDerivative
import RealRooted.EulerOperator.Polar.Adjacent
import RealRooted.EulerOperator.Polar.Pencil
import RealRooted.Interlacing.OuterDifference
import RealRooted.MaWang.CriticalSign
import RealRooted.WagnerRightSum
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Wronskian.PolarLaguerre

/-!
# Operators for lag-two Eulerian recurrences

The auxiliary operator is
`H_d = (d + 1 - theta) (theta + 1)`.  The successor operator is

`A_{a,b}^{(d)} p = (a + b theta) p + X (a + bd - b theta) p`.

This module proves the two operator comparisons used by the simultaneous
interlacing induction for positive lag-two Eulerian recurrences.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The auxiliary operator `H_d = (d + 1 - theta) (theta + 1)`. -/
def lagTwoEulerCore (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  polarTheta (d + 1) (thetaPlusOne p)

/-- The first-order Euler successor in a lag-two recurrence. -/
def lagTwoEulerStep (d : ℕ) (a b : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a * p + C b * theta p +
    X * (C (a + b * d) * p - C b * theta p)

@[simp]
theorem coeff_lagTwoEulerCore (d k : ℕ) (p : ℝ[X]) :
    (lagTwoEulerCore d p).coeff k =
      ((d : ℝ) + 1 - k) * ((k : ℝ) + 1) * p.coeff k := by
  simp [lagTwoEulerCore]
  ring

@[simp]
theorem coeff_lagTwoEulerStep_zero (d : ℕ) (a b : ℝ) (p : ℝ[X]) :
    (lagTwoEulerStep d a b p).coeff 0 = a * p.coeff 0 := by
  simp [lagTwoEulerStep, coeff_theta]

@[simp]
theorem coeff_lagTwoEulerStep_succ (d k : ℕ) (a b : ℝ) (p : ℝ[X]) :
    (lagTwoEulerStep d a b p).coeff (k + 1) =
      (a + b * (k + 1)) * p.coeff (k + 1) +
        (a + b * d - b * k) * p.coeff k := by
  unfold lagTwoEulerStep
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_theta,
    coeff_X_mul]
  push_cast
  ring

/-- Expansion of the auxiliary operator in ordinary derivatives. -/
theorem lagTwoEulerCore_eq (d : ℕ) (p : ℝ[X]) :
    lagTwoEulerCore d p =
      C ((d : ℝ) + 1) * p + C ((d : ℝ) - 1) * (X * p.derivative) -
        X ^ 2 * p.derivative.derivative := by
  simp [lagTwoEulerCore, polarTheta, thetaPlusOne, theta, derivative_mul]
  ring

/-- Decomposition of the successor into the three branches used in the
root-sign proof. -/
theorem lagTwoEulerStep_eq (d : ℕ) (a b : ℝ) (p : ℝ[X]) :
    lagTwoEulerStep d a b p =
      C a * (thetaPlusOne p + X * polarTheta (d + 1) p) +
        C (b - a) *
          (X * (C (d : ℝ) * p + (1 - X) * p.derivative)) := by
  simp [lagTwoEulerStep, thetaPlusOne, polarTheta, theta]
  ring

/-- Evaluation of the successor at a root of its input. -/
theorem lagTwoEulerStep_eval_isRoot {d : ℕ} {a b r : ℝ} {p : ℝ[X]}
    (hr : p.IsRoot r) :
    (lagTwoEulerStep d a b p).eval r =
      b * r * (1 - r) * p.derivative.eval r := by
  simp [lagTwoEulerStep, theta, hr.eq_zero]
  ring

/-- The auxiliary operator is the derivative of its polar branch. -/
theorem lagTwoEulerCore_eq_derivative_X_mul_polarTheta (d : ℕ) (p : ℝ[X]) :
    lagTwoEulerCore d p = (X * polarTheta (d + 1) p).derivative := by
  rw [lagTwoEulerCore, polarTheta_thetaPlusOne_comm, thetaPlusOne_eq_derivative_X_mul]

/-- The auxiliary operator has the same degree as a degree-`d` input. -/
theorem natDegree_lagTwoEulerCore {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree = d) (hp0 : p ≠ 0) :
    (lagTwoEulerCore d p).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_lagTwoEulerCore, coeff_eq_zero_of_natDegree_lt (hp ▸ hk), mul_zero]
  · rw [coeff_lagTwoEulerCore]
    have htop : p.coeff d ≠ 0 := by
      rw [← hp, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp0
    have hleft : (0 : ℝ) < (d : ℝ) + 1 - d := by
      norm_num
    exact mul_ne_zero (mul_ne_zero hleft.ne' (by positivity)) htop

/-- The successor has degree `d + 1` when `a > 0`. -/
theorem natDegree_lagTwoEulerStep {d : ℕ} {a b : ℝ} {p : ℝ[X]}
    (hp : p.natDegree = d) (hp_pos : HasPosLeadingCoeff p) (ha : 0 < a) :
    (lagTwoEulerStep d a b p).natDegree = d + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
    rw [coeff_lagTwoEulerStep_succ,
      coeff_eq_zero_of_natDegree_lt (by rw [hp]; lia),
      coeff_eq_zero_of_natDegree_lt (by rw [hp]; lia)]
    ring
  · rw [coeff_lagTwoEulerStep_succ,
      coeff_eq_zero_of_natDegree_lt (by simp [hp])]
    have htop : 0 < p.coeff d := by
      simpa [HasPosLeadingCoeff, leadingCoeff, hp] using hp_pos
    simpa using (mul_pos ha htop).ne'

/-- The successor has nonnegative coefficients on a degree-`d` nonnegative input. -/
theorem HasNonnegCoeffs.lagTwoEulerStep {d : ℕ} {a b : ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hpdeg : p.natDegree = d)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    HasNonnegCoeffs (lagTwoEulerStep d a b p) := by
  intro k
  cases k with
  | zero =>
      rw [coeff_lagTwoEulerStep_zero]
      exact mul_nonneg ha (hp 0)
  | succ k =>
      rw [coeff_lagTwoEulerStep_succ]
      by_cases hk : k ≤ d
      · have hb : 0 ≤ b := ha.trans hab
        have hleft : 0 ≤ a + b * (k + 1) := by positivity
        have hright : 0 ≤ a + b * d - b * k := by
          have hkreal : (k : ℝ) ≤ d := by exact_mod_cast hk
          nlinarith
        exact add_nonneg (mul_nonneg hleft (hp (k + 1)))
          (mul_nonneg hright (hp k))
      · have hdk : d < k := lt_of_not_ge hk
        rw [coeff_eq_zero_of_natDegree_lt (by rw [hpdeg]; lia),
          coeff_eq_zero_of_natDegree_lt (by rw [hpdeg]; lia)]
        norm_num

/-- The auxiliary operator has nonnegative coefficients in its degree box. -/
theorem HasNonnegCoeffs.lagTwoEulerCore_nonneg {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hpdeg : p.natDegree ≤ d) :
    HasNonnegCoeffs (lagTwoEulerCore d p) :=
  (hp.thetaPlusOne).polarTheta
    ((natDegree_thetaPlusOne_le p).trans (hpdeg.trans (Nat.le_succ d)))

private theorem simpleNegRooted_thetaPlusOne {d : ℕ} {p : ℝ[X]}
    (hp : SimpleNegRooted p d) :
    SimpleNegRooted (thetaPlusOne p) d := by
  have hpf : IsPFPolynomial p :=
    IsPFPolynomial.of_realRooted_nonneg hp.nonneg hp.splits
  have hthetaPF : IsPFPolynomial (thetaPlusOne p) :=
    thetaPlusOne_preserves_pf hpf
  have hdegree : (thetaPlusOne p).natDegree = d := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_thetaPlusOne_le p).trans_eq hp.natDegree_eq
    · rw [coeff_thetaPlusOne]
      have htop : p.coeff d ≠ 0 := by
        rw [← hp.natDegree_eq, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hp.pos.ne_zero
      exact mul_ne_zero (by positivity) htop
  have hXpSimple : HasSimpleRoots (X * p) := by
    apply hp.simple.X_mul
    intro hroot
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero] at hroot
    exact hp.coeff_zero_pos.ne' hroot
  have hder : StrictInterl (thetaPlusOne p) (X * p) := by
    rw [thetaPlusOne_eq_derivative_X_mul]
    apply (derivative_interlaces_of_natDegree_ne_zero
      (Splits.X.mul hp.splits) ?_).toStrictInterl
    rw [natDegree_mul X_ne_zero hp.pos.ne_zero, natDegree_X, hp.natDegree_eq]
    lia
  have hno : ∀ r, ¬ ((thetaPlusOne p).IsRoot r ∧ (X * p).IsRoot r) := by
    intro r hr
    have hne := hXpSimple.eval_derivative_ne_zero hr.2
    rw [← thetaPlusOne_eq_derivative_X_mul] at hne
    exact hne hr.1.eq_zero
  have hsimple : HasSimpleRoots (thetaPlusOne p) :=
    (hder.hasSimpleRoots_of_no_common_root hno).1
  refine ⟨hdegree,
    hthetaPF.hasNonnegCoeffs.pos_leadingCoeff hsimple.ne_zero,
    hthetaPF.hasNonnegCoeffs, ?_, hder.1.2, hsimple⟩
  simpa [coeff_thetaPlusOne] using hp.coeff_zero_pos

private theorem simpleNegRooted_polarTheta_succ {d : ℕ} {p : ℝ[X]}
    (hd : 0 < d) (hp : SimpleNegRooted p d) :
    SimpleNegRooted (polarTheta (d + 1) p) d := by
  have hpf : IsPFPolynomial p :=
    IsPFPolynomial.of_realRooted_nonneg hp.nonneg hp.splits
  have hpolarPF : IsPFPolynomial (polarTheta (d + 1) p) :=
    polarTheta_preserves_pf hpf (by rw [hp.natDegree_eq]; lia)
  have hshift : 2 ≤ (reciprocalShift (d + 1) p).natDegree := by
    have hcoeff : (reciprocalShift (d + 1) p).coeff (d + 1) ≠ 0 := by
      simpa using hp.coeff_zero_pos.ne'
    exact (by lia : 2 ≤ d + 1).trans (le_natDegree_of_ne_zero hcoeff)
  have hinter : StrictInterl (polarTheta (d + 1) p) p :=
    strictInterl_polarTheta_self hpf (by rw [hp.natDegree_eq]; lia) hshift
  have hno : ∀ r, ¬ ((polarTheta (d + 1) p).IsRoot r ∧ p.IsRoot r) := by
    intro r hr
    have hrneg := hp.isRoot_neg hr.2
    have heval : (polarTheta (d + 1) p).eval r =
        -(r * p.derivative.eval r) := by
      simp [polarTheta, theta, hr.2.eq_zero]
    have hder := hp.simple.eval_derivative_ne_zero hr.2
    rw [hr.1.eq_zero] at heval
    exact mul_ne_zero hrneg.ne hder (neg_eq_zero.mp heval.symm)
  have hsimple : HasSimpleRoots (polarTheta (d + 1) p) :=
    (hinter.hasSimpleRoots_of_no_common_root hno).1
  have hdegree : (polarTheta (d + 1) p).natDegree = d := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_polarTheta, coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ hk),
        mul_zero]
    · rw [coeff_polarTheta]
      have htop : p.coeff d ≠ 0 := by
        rw [← hp.natDegree_eq, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hp.pos.ne_zero
      have hfactor : (0 : ℝ) < (d + 1 : ℕ) - d := by
        push_cast
        norm_num
      exact mul_ne_zero hfactor.ne' htop
  refine ⟨hdegree,
    hpolarPF.hasNonnegCoeffs.pos_leadingCoeff hsimple.ne_zero,
    hpolarPF.hasNonnegCoeffs, ?_, hinter.1.2, hsimple⟩
  rw [coeff_polarTheta]
  simpa [Nat.cast_add, Nat.cast_one] using
    mul_pos (show (0 : ℝ) < d + 1 by positivity) hp.coeff_zero_pos

/-- The auxiliary operator preserves simple negative roots. -/
protected theorem SimpleNegRooted.lagTwoEulerCore {d : ℕ} {p : ℝ[X]}
    (hp : SimpleNegRooted p d) :
    SimpleNegRooted (lagTwoEulerCore d p) d := by
  have htheta := simpleNegRooted_thetaPlusOne hp
  cases d with
  | zero =>
      have hder : (thetaPlusOne p).derivative = 0 :=
        derivative_eq_zero.mpr htheta.natDegree_eq
      have heq : RealRooted.lagTwoEulerCore 0 p = thetaPlusOne p := by
        change polarTheta 1 (thetaPlusOne p) = thetaPlusOne p
        unfold polarTheta theta
        rw [hder]
        simp
      rw [heq]
      exact htheta
  | succ d =>
      exact simpleNegRooted_polarTheta_succ (by lia) htheta

/-- Applying the auxiliary operators at adjacent degrees preserves a strict
pair of simple negative-rooted polynomials. -/
theorem StrictInterl.lagTwoEulerCore_adjacent {d : ℕ} {p q : ℝ[X]}
    (hp : SimpleNegRooted p d) (hq : SimpleNegRooted q (d + 1))
    (hpq : StrictInterl p q) :
    StrictInterl (lagTwoEulerCore d p) (lagTwoEulerCore (d + 1) q) := by
  have hpf : IsPFPolynomial p :=
    IsPFPolynomial.of_realRooted_nonneg hp.nonneg hp.splits
  have hqf : IsPFPolynomial q :=
    IsPFPolynomial.of_realRooted_nonneg hq.nonneg hq.splits
  have hpTheta := simpleNegRooted_thetaPlusOne hp
  have hqTheta := simpleNegRooted_thetaPlusOne hq
  have htheta : StrictInterl (thetaPlusOne p) (thetaPlusOne q) :=
    (hpq.toInterl.thetaPlusOne).toStrictInterl_of_ne
      hpTheta.pos.ne_zero hqTheta.pos.ne_zero
  exact strictInterl_polarTheta_adjacent
    (thetaPlusOne_preserves_pf hpf) (thetaPlusOne_preserves_pf hqf) htheta
    hpTheta.natDegree_eq hqTheta.natDegree_eq
    hpTheta.coeff_zero_pos.ne' hqTheta.coeff_zero_pos.ne'

private def lagTwoEulerBridge (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (d : ℝ) * p + (1 - X) * p.derivative

private theorem lagTwoEulerBridge_eq (d : ℕ) (p : ℝ[X]) :
    lagTwoEulerBridge d p = polarTheta d p + p.derivative := by
  simp [lagTwoEulerBridge, polarTheta, theta]
  ring

private theorem coeff_lagTwoEulerBridge (d k : ℕ) (p : ℝ[X]) :
    (lagTwoEulerBridge d p).coeff k =
      ((d : ℝ) - k) * p.coeff k + ((k : ℝ) + 1) * p.coeff (k + 1) := by
  unfold lagTwoEulerBridge
  rw [show (1 - X) * p.derivative = p.derivative - X * p.derivative by ring]
  change (C (d : ℝ) * p + (p.derivative - theta p)).coeff k = _
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_derivative, coeff_theta]
  ring

private theorem lagTwoEulerBridge_data {d : ℕ} {p : ℝ[X]}
    (hd : 2 ≤ d) (hp : SimpleNegRooted p d) :
    SimpleNegRooted (lagTwoEulerBridge d p) (d - 1) ∧
      StrictInterl (lagTwoEulerBridge d p) p ∧
      ∀ r, (lagTwoEulerBridge d p).IsRoot r → ¬ p.IsRoot r := by
  have hpf : IsPFPolynomial p :=
    IsPFPolynomial.of_realRooted_nonneg hp.nonneg hp.splits
  have hshift : 2 ≤ (reciprocalShift d p).natDegree := by
    have hcoeff : (reciprocalShift d p).coeff d ≠ 0 := by
      simpa using hp.coeff_zero_pos.ne'
    exact hd.trans (le_natDegree_of_ne_zero hcoeff)
  have hpolar : StrictInterl (polarTheta d p) p :=
    strictInterl_polarTheta_self hpf (by rw [hp.natDegree_eq]) hshift
  have hderiv : StrictInterl p.derivative p :=
    (derivative_interlaces_of_natDegree_ne_zero hp.splits (by
      rw [hp.natDegree_eq]
      lia)).toStrictInterl
  have hpolarPF : IsPFPolynomial (polarTheta d p) :=
    polarTheta_preserves_pf hpf (by rw [hp.natDegree_eq])
  have hpolarPos : HasPosLeadingCoeff (polarTheta d p) :=
    hpolarPF.hasNonnegCoeffs.pos_leadingCoeff hpolar.1.1
  have hderivPos : HasPosLeadingCoeff p.derivative :=
    hp.pos.derivative (by rw [hp.natDegree_eq]; lia)
  have hinter : StrictInterl (lagTwoEulerBridge d p) p := by
    rw [lagTwoEulerBridge_eq]
    exact StrictInterl.add_of_right_of_posLeadingCoeff
      hpolar hderiv hpolarPos hderivPos
  have hno : ∀ r, (lagTwoEulerBridge d p).IsRoot r → ¬ p.IsRoot r := by
    intro r hr hpr
    have hrneg := hp.isRoot_neg hpr
    have heval : (lagTwoEulerBridge d p).eval r =
        (1 - r) * p.derivative.eval r := by
      simp [lagTwoEulerBridge, hpr.eq_zero]
    rw [hr.eq_zero] at heval
    exact mul_ne_zero (by linarith) (hp.simple.eval_derivative_ne_zero hpr) heval.symm
  have hsimple : HasSimpleRoots (lagTwoEulerBridge d p) :=
    (hinter.hasSimpleRoots_of_no_common_root fun r hr ↦ hno r hr.1 hr.2).1
  have hdegree : (lagTwoEulerBridge d p).natDegree = d - 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      by_cases hkd : k = d
      · subst k
        have hz : p.coeff (d + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hp.natDegree_eq]; lia)
        rw [coeff_lagTwoEulerBridge, hz]
        ring
      · have hdk : d < k := by lia
        have hz0 : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hp.natDegree_eq]; lia)
        have hz1 : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hp.natDegree_eq]; lia)
        rw [coeff_lagTwoEulerBridge, hz0, hz1]
        ring
    · rw [coeff_lagTwoEulerBridge]
      have htop : 0 < p.coeff d := by
        simpa [HasPosLeadingCoeff, leadingCoeff, hp.natDegree_eq] using hp.pos
      have hprev : 0 ≤ p.coeff (d - 1) := hp.nonneg _
      have hdreal : (0 : ℝ) < d := by positivity
      have hindex : d - 1 + 1 = d := by lia
      have hcast : (d : ℝ) - (d - 1 : ℕ) = 1 := by
        rw [Nat.cast_sub (by lia)]
        push_cast
        ring
      rw [hindex, hcast]
      nlinarith
  have hnonneg : HasNonnegCoeffs (lagTwoEulerBridge d p) := by
    rw [lagTwoEulerBridge_eq]
    exact (hp.nonneg.polarTheta (by rw [hp.natDegree_eq])).add hp.nonneg.derivative
  have hzero : 0 < (lagTwoEulerBridge d p).coeff 0 := by
    rw [coeff_lagTwoEulerBridge]
    have hdreal : (0 : ℝ) < d := by positivity
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by simpa using hdreal) hp.coeff_zero_pos)
      (mul_nonneg (by positivity) (hp.nonneg 1))
  exact ⟨⟨hdegree, hnonneg.pos_leadingCoeff hsimple.ne_zero, hnonneg,
    hzero, hinter.1.2, hsimple⟩, hinter, hno⟩

private theorem lagTwoEulerBridge_strictInterl_core {d : ℕ} {p : ℝ[X]}
    (hd : 2 ≤ d) (hp : SimpleNegRooted p d) :
    StrictInterl (lagTwoEulerBridge d p) (lagTwoEulerCore d p) := by
  obtain ⟨hh, hhp, hno⟩ := lagTwoEulerBridge_data hd hp
  have hq := hp.lagTwoEulerCore
  have hpf : IsPFPolynomial p :=
    IsPFPolynomial.of_realRooted_nonneg hp.nonneg hp.splits
  have hsignProduct : ∀ r, (lagTwoEulerBridge d p).IsRoot r →
      0 < (lagTwoEulerCore d p).eval r * p.eval r := by
    intro r hr
    have hrneg := hh.isRoot_neg hr
    have hpne : p.eval r ≠ 0 := by
      intro hpzero
      exact hno r hr (by simpa [Polynomial.IsRoot] using hpzero)
    have hrel : (d : ℝ) * p.eval r + (1 - r) * p.derivative.eval r = 0 := by
      simpa [lagTwoEulerBridge] using hr.eq_zero
    let s : ℝ := -r / (1 - r)
    have hden : 1 - r ≠ 0 := by linarith
    have hspos : 0 < s := by
      dsimp [s]
      exact div_pos (by linarith) (by linarith)
    have hslt : s < 1 := by
      dsimp [s]
      rw [div_lt_one (by linarith)]
      linarith
    have hpder : p.derivative.eval r = -(d : ℝ) * p.eval r / (1 - r) := by
      apply (eq_div_iff hden).2
      nlinarith [hrel]
    have htheta : 0 ≤ (thetaLaguerreForm p).eval r :=
      theta_laguerreForm_nonneg_of_isPF hpf r
    have hidentity :
        (lagTwoEulerCore d p).eval r * p.eval r =
          -r * (thetaLaguerreForm p).eval r +
            ((d : ℝ) + 1 + (d : ℝ) ^ 2 * s * (1 - s)) * (p.eval r) ^ 2 := by
      rw [lagTwoEulerCore_eq]
      simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow,
        eval_thetaLaguerreForm]
      rw [hpder]
      dsimp [s]
      field_simp
      ring
    rw [hidentity]
    have hfactor : 0 < (d : ℝ) + 1 + (d : ℝ) ^ 2 * s * (1 - s) := by
      have hsnonneg : 0 ≤ s * (1 - s) :=
        mul_nonneg hspos.le (sub_nonneg.mpr hslt.le)
      positivity
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by linarith) htheta)
      (mul_pos hfactor (sq_pos_of_ne_zero hpne))
  have hsign : ∀ r, (lagTwoEulerBridge d p).IsRoot r →
      (lagTwoEulerCore d p).eval r *
        (lagTwoEulerBridge d p).derivative.eval r < 0 := by
    intro r hr
    have hpSign := hhp.eval_mul_derivative_neg_of_left_root_of_no_common
      hh.pos hp.pos hno hr
    have hqp := hsignProduct r hr
    rcases lt_or_gt_of_ne (show p.eval r ≠ 0 by
      intro hpzero
      exact hno r hr (by simpa [Polynomial.IsRoot] using hpzero)) with hpneg | hppos
    · have hqneg : (lagTwoEulerCore d p).eval r < 0 := by nlinarith
      have hhderpos : 0 < (lagTwoEulerBridge d p).derivative.eval r := by nlinarith
      exact mul_neg_of_neg_of_pos hqneg hhderpos
    · have hqpos : 0 < (lagTwoEulerCore d p).eval r := by nlinarith
      have hhderneg : (lagTwoEulerBridge d p).derivative.eval r < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hqpos hhderneg
  apply strictInterl_of_eval_mul_derivative_neg hh.splits hh.pos hq.pos
  · rw [hh.natDegree_eq]
    lia
  · rw [hh.natDegree_eq, hq.natDegree_eq]
    lia
  · rw [hh.natDegree_eq, hq.natDegree_eq]
    lia
  · exact hsign

private theorem lagTwoEulerBridge_package {d : ℕ} {p : ℝ[X]}
    (hd : 0 < d) (hp : SimpleNegRooted p d) :
    SimpleNegRooted (lagTwoEulerBridge d p) (d - 1) ∧
      StrictInterl (lagTwoEulerBridge d p) (lagTwoEulerCore d p) := by
  rcases eq_or_lt_of_le (show 1 ≤ d by lia) with hdone | hdgt
  · subst d
    have hzero : 0 < (lagTwoEulerBridge 1 p).coeff 0 := by
      rw [coeff_lagTwoEulerBridge]
      have htop : 0 < p.coeff 1 := by
        simpa [HasPosLeadingCoeff, leadingCoeff, hp.natDegree_eq] using hp.pos
      norm_num
      exact add_pos hp.coeff_zero_pos htop
    have hdegree : (lagTwoEulerBridge 1 p).natDegree = 0 := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · rw [natDegree_le_iff_coeff_eq_zero]
        intro k hk
        have hz1 : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hp.natDegree_eq]; lia)
        rw [coeff_lagTwoEulerBridge, hz1]
        by_cases hk1 : k = 1
        · subst k
          norm_num
        · have h1k : 1 < k := by lia
          rw [coeff_eq_zero_of_natDegree_lt (by rw [hp.natDegree_eq]; exact h1k)]
          ring
      · exact hzero.ne'
    have heq : lagTwoEulerBridge 1 p = C ((lagTwoEulerBridge 1 p).coeff 0) :=
      eq_C_of_natDegree_eq_zero hdegree
    have hh : SimpleNegRooted (lagTwoEulerBridge 1 p) 0 := by
      rw [heq]
      simpa using SimpleNegRooted.one.C_mul hzero
    have hq := hp.lagTwoEulerCore
    have hinter : StrictInterl (lagTwoEulerBridge 1 p) (lagTwoEulerCore 1 p) :=
      StrictInterl.of_degree_zero_right_of_degree_one
        hh.pos.ne_zero hh.splits hq.pos.ne_zero hq.splits
        hh.natDegree_eq hq.natDegree_eq
    exact ⟨hh, hinter⟩
  · have hdata := lagTwoEulerBridge_data (by lia) hp
    exact ⟨hdata.1, lagTwoEulerBridge_strictInterl_core (by lia) hp⟩

/-- The auxiliary polynomial strictly precedes the positive Euler successor.
This is the main one-row operator lemma for the lag-two induction. -/
theorem SimpleNegRooted.lagTwoEulerCore_strictInterl_step
    {d : ℕ} {p : ℝ[X]} (hp : SimpleNegRooted p d)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    StrictInterl (RealRooted.lagTwoEulerCore d p) (lagTwoEulerStep d a b p) := by
  cases d with
  | zero =>
      have hpder : p.derivative = 0 := derivative_eq_zero.mpr hp.natDegree_eq
      have hcore : RealRooted.lagTwoEulerCore 0 p = p := by
        change polarTheta 1 (thetaPlusOne p) = p
        simp [thetaPlusOne, polarTheta, theta, hpder]
      have hstep : lagTwoEulerStep 0 a b p = C a * (1 + X) * p := by
        simp [lagTwoEulerStep, theta, hpder]
        ring
      rw [hcore, hstep]
      have hlin : StrictInterl (1 : ℝ[X]) (1 + X) := by
        have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by
          simp [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
        have hne : (1 + X : ℝ[X]) ≠ 0 := by
          intro hzero
          have hcoeff := congrArg (fun q : ℝ[X] ↦ q.coeff 0) hzero
          simp at hcoeff
        exact StrictInterl.of_degree_zero_right_of_degree_one
          one_ne_zero Splits.one hne (Splits.of_natDegree_le_one hdeg.le) (by simp) hdeg
      have hscaled := hlin.mul_common_factor hp.pos.ne_zero hp.splits
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        hscaled.C_mul_right ha.ne'
  | succ d =>
      let D := d + 1
      have hD : 0 < D := by simp [D]
      have hpD : SimpleNegRooted p D := by simpa [D] using hp
      have hq : SimpleNegRooted (RealRooted.lagTwoEulerCore D p) D :=
        hpD.lagTwoEulerCore
      have hpf : IsPFPolynomial p :=
        IsPFPolynomial.of_realRooted_nonneg hpD.nonneg hpD.splits
      have htheta := simpleNegRooted_thetaPlusOne hpD
      have hqR : StrictInterl (RealRooted.lagTwoEulerCore D p) (thetaPlusOne p) := by
        have hshift : 2 ≤ (reciprocalShift (D + 1) (thetaPlusOne p)).natDegree := by
          have hcoeff :
              (reciprocalShift (D + 1) (thetaPlusOne p)).coeff (D + 1) ≠ 0 := by
            simpa using htheta.coeff_zero_pos.ne'
          exact (by lia : 2 ≤ D + 1).trans (le_natDegree_of_ne_zero hcoeff)
        exact strictInterl_polarTheta_self
          (thetaPlusOne_preserves_pf hpf) (by rw [htheta.natDegree_eq]; lia) hshift
      have hpolar := simpleNegRooted_polarTheta_succ hD hpD
      have hqS : StrictInterl (RealRooted.lagTwoEulerCore D p) (X * polarTheta (D + 1) p) := by
        rw [lagTwoEulerCore_eq_derivative_X_mul_polarTheta]
        apply (derivative_interlaces_of_natDegree_ne_zero
          (Splits.X.mul hpolar.splits) ?_).toStrictInterl
        rw [natDegree_mul X_ne_zero hpolar.pos.ne_zero, natDegree_X,
          hpolar.natDegree_eq]
        lia
      obtain ⟨hh, hhq⟩ := lagTwoEulerBridge_package hD hpD
      have hqXh : StrictInterl (RealRooted.lagTwoEulerCore D p)
          (X * lagTwoEulerBridge D p) :=
        strictInterl_mul_X_of_strictInterl_of_nonneg hhq
          hh.nonneg hq.nonneg
      have hRpos : HasPosLeadingCoeff (thetaPlusOne p) := htheta.pos
      have hSpos : HasPosLeadingCoeff (X * polarTheta (D + 1) p) := hpolar.pos.X_mul
      have hXhpos : HasPosLeadingCoeff (X * lagTwoEulerBridge D p) := hh.pos.X_mul
      have hsum : StrictInterl (RealRooted.lagTwoEulerCore D p)
          (weightedSum [(a, thetaPlusOne p),
            (a, X * polarTheta (D + 1) p),
            (b - a, X * lagTwoEulerBridge D p)]) := by
        apply StrictInterl.weightedSum_left_of_common_left
        · simp [ha.le, sub_nonneg.mpr hab]
        · intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl | rfl
          exacts [hqR, hqS, hqXh]
        · exact hq.pos
        · intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl | rfl
          exacts [hRpos, hSpos, hXhpos]
        · exact ⟨(a, thetaPlusOne p), by simp [ha]⟩
      rw [lagTwoEulerStep_eq]
      simpa [weightedSum, weightedSum_cons, lagTwoEulerBridge, D,
        mul_add, add_assoc] using hsum

end RealRooted
