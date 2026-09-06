import RealRooted.AffineFamily
import RealRooted.EulerOperator.Pencil
import RealRooted.EulerOperator.Polar.ProperPosition

/-!
# Proper-position polar Euler pencils

This file develops the proper-position comparisons between the polar Euler
operator `polarTheta`, differentiation, and `thetaPlusOne`. The central
derivative--polar comparison is proved once for the weak degree boundary; the
strict-degree and boundary APIs differ only in how nonvanishing is supplied.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A polar Euler derivative precedes its original polynomial after transport
through a bounded reciprocal shift. -/
theorem prec_polarTheta_self {N : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ N)
    (hshift : 2 ≤ (reciprocalShift N p).natDegree) :
    Prec (polarTheta N p) p := by
  set q := reciprocalShift N p with hq
  have hqpf : IsPFPolynomial q := reciprocalShift_preserves_pf hp hpdeg
  have hqdeg : q.natDegree ≤ N := by
    rw [hq]
    unfold reciprocalShift
    exact (Polynomial.natDegree_reflect_le).trans (max_le le_rfl hpdeg)
  have hbase : Prec q (theta q) := prec_self_theta hqpf hshift
  have htheta_pf : IsPFPolynomial (theta q) := theta_preserves_pf hqpf
  have htheta_deg : (theta q).natDegree ≤ N := by
    have hq0 : q ≠ 0 := by
      intro hzero
      rw [hzero] at hshift
      simp at hshift
    rw [theta, Polynomial.natDegree_mul Polynomial.X_ne_zero
      (q.derivative_ne_zero.mpr (by lia)), q.natDegree_derivative]
    simp only [Polynomial.natDegree_X]
    lia
  have htransport :
      Prec (reciprocalShift N (theta q)) (reciprocalShift N q) :=
    reciprocalShift_reverses_prec hqpf htheta_pf hqdeg htheta_deg hbase
  have hinvol : reciprocalShift N q = p := by
    rw [hq]
    unfold reciprocalShift
    simp
  have hpolar : reciprocalShift N (theta q) = polarTheta N p := by
    rw [hq, ← polarTheta_eq_reciprocalShift_theta_reciprocalShift N p hpdeg]
  simpa [hinvol, hpolar] using htransport

/-- Shared affine-family proof of the derivative--polar comparison. -/
private theorem prec_derivative_polarTheta_of_le
    {M : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : 2 ≤ p.natDegree) (hpM : p.natDegree ≤ M)
    (hpolar0 : polarTheta M p ≠ 0)
    (hpolar_p : Prec (polarTheta M p) p) :
    Prec p.derivative (polarTheta M p) := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp_all
  have hpsplits : p.Splits := (hp.ne_zero_and_splits hp0).2
  have hpnn : HasNonnegCoeffs p := hp.hasNonnegCoeffs
  have hMpos : 0 < M := by lia
  have hdernn : HasNonnegCoeffs p.derivative := hpnn.derivative
  have hder0 : p.derivative ≠ 0 := p.derivative_ne_zero.mpr (by lia)
  have hpolar_pf : IsPFPolynomial (polarTheta M p) :=
    polarTheta_preserves_pf hp hpM
  have hpolar_nn : HasNonnegCoeffs (polarTheta M p) :=
    hpolar_pf.hasNonnegCoeffs
  have htheta_pf : IsPFPolynomial (theta p) := theta_preserves_pf hp
  have htheta0 : theta p ≠ 0 := by
    unfold theta
    exact mul_ne_zero Polynomial.X_ne_zero hder0
  have htheta_splits : (theta p).Splits :=
    (htheta_pf.ne_zero_and_splits htheta0).2
  have hp_theta : Prec p (theta p) := prec_self_theta hp hpdeg
  have hder_theta : Prec p.derivative (theta p) := by
    have hself : Prec p.derivative (X * p.derivative) :=
      prec_self_X_mul_of_nonneg hder0
        (hp.derivative.ne_zero_and_splits hder0).2 hdernn
    simpa [theta] using hself
  refine prec_of_affine_family_nonneg hder0 hpolar0 hdernn hpolar_nn ?_
  intro s t hs ht
  rcases lt_trichotomy s 1 with hs1 | rfl | hs1
  · set fs : List ℝ[X] :=
      [C (s * M) * p, C t * p.derivative,
        C (1 - s) * polarTheta M p]
    have hcommon : HasCommonInterleaver fs := by
      refine ⟨p, ?_⟩
      intro q hq
      simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact prec_C_mul_left (prec_refl hp0 hpsplits) (by positivity)
      · exact prec_C_mul_left
          ((derivative_interlaces hpsplits hpdeg).toPrec) ht.ne'
      · exact prec_C_mul_left hpolar_p (by linarith)
    have hpos : ∀ q ∈ fs, HasPosLeadingCoeff q := by
      intro q hq
      simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hasPosLeadingCoeff_C_mul (by positivity)
          (hpnn.pos_leadingCoeff hp0)
      · exact hasPosLeadingCoeff_C_mul ht
          (hdernn.pos_leadingCoeff hder0)
      · exact hasPosLeadingCoeff_C_mul (by linarith)
          (hpolar_nn.pos_leadingCoeff hpolar0)
    have hsum :=
      isRealRooted_sum_of_commonInterleaver hcommon hpos (by simp [fs])
    have hsum_eq :
        fs.sum = (C s * X + C t) * p.derivative + polarTheta M p := by
      simp only [fs, List.sum_cons, List.sum_nil, add_zero]
      unfold polarTheta theta
      grind
    simpa [hsum_eq] using hsum
  · set fs : List ℝ[X] := [C (M : ℝ) * p, C t * p.derivative]
    have hcommon : HasCommonInterleaver fs := by
      refine ⟨p, ?_⟩
      intro q hq
      simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact prec_C_mul_left (prec_refl hp0 hpsplits) (by positivity)
      · exact prec_C_mul_left
          ((derivative_interlaces hpsplits hpdeg).toPrec) ht.ne'
    have hpos : ∀ q ∈ fs, HasPosLeadingCoeff q := by
      intro q hq
      simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hasPosLeadingCoeff_C_mul (by positivity)
          (hpnn.pos_leadingCoeff hp0)
      · exact hasPosLeadingCoeff_C_mul ht
          (hdernn.pos_leadingCoeff hder0)
    have hsum :=
      isRealRooted_sum_of_commonInterleaver hcommon hpos (by simp [fs])
    have hsum_eq :
        fs.sum = (C (1 : ℝ) * X + C t) * p.derivative + polarTheta M p := by
      simp only [fs, List.sum_cons, List.sum_nil, add_zero]
      unfold polarTheta theta
      grind
    simpa [hsum_eq] using hsum
  · set fs : List ℝ[X] :=
      [C (s - 1) * theta p, C t * p.derivative, C (M : ℝ) * p]
    have hcommon : HasCommonInterleaver fs := by
      refine ⟨theta p, ?_⟩
      intro q hq
      simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact prec_C_mul_left (prec_refl htheta0 htheta_splits) (by linarith)
      · exact prec_C_mul_left hder_theta ht.ne'
      · exact prec_C_mul_left hp_theta (by positivity)
    have hpos : ∀ q ∈ fs, HasPosLeadingCoeff q := by
      intro q hq
      simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hasPosLeadingCoeff_C_mul (by linarith)
          (htheta_pf.hasNonnegCoeffs.pos_leadingCoeff htheta0)
      · exact hasPosLeadingCoeff_C_mul ht
          (hdernn.pos_leadingCoeff hder0)
      · exact hasPosLeadingCoeff_C_mul (by positivity)
          (hpnn.pos_leadingCoeff hp0)
    have hsum :=
      isRealRooted_sum_of_commonInterleaver hcommon hpos (by simp [fs])
    have hsum_eq :
        fs.sum = (C s * X + C t) * p.derivative + polarTheta M p := by
      simp only [fs, List.sum_cons, List.sum_nil, add_zero]
      unfold polarTheta theta
      grind
    simpa [hsum_eq] using hsum

/-- The derivative of a PF polynomial precedes its polar Euler derivative at
a strictly larger index. -/
theorem prec_derivative_polarTheta {M : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : 2 ≤ p.natDegree)
    (hpM : p.natDegree < M) (hpolar_p : Prec (polarTheta M p) p) :
    Prec p.derivative (polarTheta M p) := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp_all
  have hpolar0 : polarTheta M p ≠ 0 := by
    have hlead : p.coeff p.natDegree ≠ 0 := by simp_all
    have hfactor : ((M : ℝ) - (p.natDegree : ℝ)) ≠ 0 := by
      have : (p.natDegree : ℝ) < M := by exact_mod_cast hpM
      positivity
    intro hzero
    have hcoeff := coeff_polarTheta M p p.natDegree
    rw [hzero] at hcoeff
    simp_all
  exact prec_derivative_polarTheta_of_le hp hpdeg (le_of_lt hpM)
    hpolar0 hpolar_p

/-- Boundary form of `prec_derivative_polarTheta`, with nonvanishing supplied
explicitly when the polar operator may drop the leading degree. -/
theorem prec_derivative_polarTheta_boundary {M : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : 2 ≤ p.natDegree)
    (hpM : p.natDegree ≤ M) (hpolar0 : polarTheta M p ≠ 0)
    (hpolar_p : Prec (polarTheta M p) p) :
    Prec p.derivative (polarTheta M p) :=
  prec_derivative_polarTheta_of_le hp hpdeg hpM hpolar0 hpolar_p

/-- The same boundary comparison with zero-aware proper position. -/
theorem prec0_derivative_polarTheta_boundary {M : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : 2 ≤ p.natDegree)
    (hpM : p.natDegree ≤ M) (hpolar_p : Prec0 (polarTheta M p) p) :
    Prec0 p.derivative (polarTheta M p) := by
  by_cases hpolar0 : polarTheta M p = 0
  · simpa [hpolar0] using prec0_zero_right p.derivative
  · have hp0 : p ≠ 0 := by
      intro hzero
      simp_all
    exact (prec_derivative_polarTheta_boundary hp hpdeg hpM hpolar0
      (hpolar_p.toPrec_of_ne hpolar0 hp0)).toPrec0

/-- A polar Euler derivative precedes `thetaPlusOne` at a strictly larger
index. -/
theorem prec_polarTheta_thetaPlusOne {N : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : 2 ≤ p.natDegree)
    (hpN : p.natDegree < N) (hconst : p.coeff 0 ≠ 0) :
    Prec (polarTheta N p) (thetaPlusOne p) := by
  have hp0 : p ≠ 0 := fun hzero ↦ hconst (by simp_all)
  set q := X * p with hq
  have hqpf : IsPFPolynomial q := hp.X_mul
  have hqdeg : q.natDegree = p.natDegree + 1 := by simp_all
  have hqdeg2 : 2 ≤ q.natDegree := by lia
  have hqN : q.natDegree < N + 1 := by lia
  have hshift : 2 ≤ (reciprocalShift (N + 1) q).natDegree := by
    have hcoeff : (reciprocalShift (N + 1) q).coeff N ≠ 0 := by
      simp_all
    exact le_trans (by lia) (le_natDegree_of_ne_zero hcoeff)
  have hpolar_q : Prec (polarTheta (N + 1) q) q :=
    prec_polarTheta_self hqpf (le_of_lt hqN) hshift
  have hstep : Prec q.derivative (polarTheta (N + 1) q) :=
    prec_derivative_polarTheta hqpf hqdeg2 hqN hpolar_q
  have hpolar : polarTheta (N + 1) q = X * polarTheta N p := by
    rw [hq]
    ext k
    cases k with
    | zero => simp [coeff_polarTheta]
    | succ k => simp
  have hderivative : q.derivative = thetaPlusOne p := by
    rw [hq]
    exact (thetaPlusOne_eq_derivative_X_mul p).symm
  rw [hpolar, hderivative] at hstep
  exact prec_of_prec_X_mul_of_nonneg hstep
    (polarTheta_preserves_pf hp (le_of_lt hpN)).hasNonnegCoeffs
    (thetaPlusOne_preserves_pf hp).hasNonnegCoeffs

/-- At the boundary index, `thetaPlusOne p` precedes the `X`-shifted polar
Euler derivative. -/
theorem prec_thetaPlusOne_X_polarTheta_boundary {N : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = N) (hN : 2 ≤ N)
    (hconst : p.coeff 0 ≠ 0) :
    Prec (thetaPlusOne p) (X * polarTheta N p) := by
  have hp0 : p ≠ 0 := fun hzero ↦ hconst (by simp_all)
  set q := X * p with hq
  have hqpf : IsPFPolynomial q := hp.X_mul
  have hqdeg : q.natDegree = N + 1 := by simp_all
  have hpolar : polarTheta (N + 1) q = X * polarTheta N p := by
    rw [hq]
    ext k
    cases k with
    | zero => simp [coeff_polarTheta]
    | succ k => simp
  have hderivative : q.derivative = thetaPlusOne p := by
    rw [hq]
    exact (thetaPlusOne_eq_derivative_X_mul p).symm
  have hpolar0 : polarTheta N p ≠ 0 := by
    intro hzero
    have hcoeff := coeff_polarTheta N p 0
    rw [hzero] at hcoeff
    simp_all
  have hshift : 2 ≤ (reciprocalShift (N + 1) q).natDegree := by
    have hcoeff : (reciprocalShift (N + 1) q).coeff N ≠ 0 := by
      simp_all
    exact le_trans hN (le_natDegree_of_ne_zero hcoeff)
  have hpolar_q : Prec (polarTheta (N + 1) q) q :=
    prec_polarTheta_self hqpf (by lia) hshift
  have hstep : Prec q.derivative (polarTheta (N + 1) q) :=
    prec_derivative_polarTheta_boundary hqpf (by lia) (by lia)
      (by simpa [hpolar] using mul_ne_zero Polynomial.X_ne_zero hpolar0)
      hpolar_q
  simpa [hpolar, hderivative] using hstep

/-- The unshifted boundary counterpart of
`prec_polarTheta_thetaPlusOne`. -/
theorem prec_polarTheta_thetaPlusOne_boundary {N : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = N) (hN : 2 ≤ N)
    (hconst : p.coeff 0 ≠ 0) :
    Prec (polarTheta N p) (thetaPlusOne p) := by
  have hstep :=
    prec_thetaPlusOne_X_polarTheta_boundary hp hpdeg hN hconst
  exact prec_of_prec_X_mul_of_nonneg hstep
    (polarTheta_preserves_pf hp (le_of_eq hpdeg)).hasNonnegCoeffs
    (thetaPlusOne_preserves_pf hp).hasNonnegCoeffs

/-- At the boundary index, every positive Euler pencil precedes the
`X`-shifted polar Euler derivative. -/
theorem prec_self_add_C_mul_theta_X_polarTheta_boundary
    {N : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree = N) (hN : 2 ≤ N)
    (hconst : p.coeff 0 ≠ 0) {b : ℝ} (hb : 0 < b) :
    Prec (p + C b * theta p) (X * polarTheta N p) := by
  have hp0 : p ≠ 0 := fun hzero ↦ hconst (by simp_all)
  have hpolar_pf : IsPFPolynomial (polarTheta N p) :=
    polarTheta_preserves_pf hp (le_of_eq hpdeg)
  have hpolar0 : polarTheta N p ≠ 0 := by
    intro hzero
    have hcoeff := coeff_polarTheta N p 0
    rw [hzero] at hcoeff
    simp_all
  have hshift : 2 ≤ (reciprocalShift N p).natDegree := by
    have hcoeff : (reciprocalShift N p).coeff N ≠ 0 := by simp_all
    exact hN.trans (le_natDegree_of_ne_zero hcoeff)
  have hpolar_p : Prec (polarTheta N p) p :=
    prec_polarTheta_self hp (le_of_eq hpdeg) hshift
  have hp_right : Prec p (X * polarTheta N p) :=
    prec_mul_X_of_prec_of_nonneg hpolar_p
      hpolar_pf.hasNonnegCoeffs hp.hasNonnegCoeffs
  have hder_polar : Prec p.derivative (polarTheta N p) :=
    prec_derivative_polarTheta_boundary hp (by lia)
      (le_of_eq hpdeg) hpolar0 hpolar_p
  have htheta_right : Prec (theta p) (X * polarTheta N p) := by
    simpa [theta] using
      prec_mul_common_factor Polynomial.X_ne_zero Polynomial.Splits.X hder_polar
  have hbtheta_right : Prec (C b * theta p) (X * polarTheta N p) :=
    prec_C_mul_left htheta_right hb.ne'
  have hp_pos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have htheta0 : theta p ≠ 0 := by
    unfold theta
    exact mul_ne_zero Polynomial.X_ne_zero
      (p.derivative_ne_zero.mpr (by lia))
  have hbtheta_pos : HasPosLeadingCoeff (C b * theta p) :=
    hasPosLeadingCoeff_C_mul hb
      ((theta_preserves_pf hp).hasNonnegCoeffs.pos_leadingCoeff htheta0)
  exact prec_add_of_prec_right_of_posLeadingCoeff
    hp_right hbtheta_right hp_pos hbtheta_pos

end RealRooted
