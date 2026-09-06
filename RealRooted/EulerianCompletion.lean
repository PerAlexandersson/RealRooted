import RealRooted.BorceaBranden.Applications.EulerFiniteSymbol
import RealRooted.EulerianMixedCompatibility.Insertion
import RealRooted.EulerOperator

/-!
# Oriented Euler completion

This module proves the oriented derivative-to-zero-boundary relation needed
for crossed Euler completions.  The argument uses the genuine finite
algebraic symbol of the lowering operator

`p ↦ M p + (1 - X) p'`.

The result is operator theory independent of any particular sequence.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The lowering Euler operator used to compare a derivative step with a
zero-boundary insertion step. -/
def loweringEulerStep (M : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (M : ℝ) * p + (1 - X) * p.derivative

@[simp] theorem coeff_loweringEulerStep (M : ℕ) (p : ℝ[X]) (k : ℕ) :
    (loweringEulerStep M p).coeff k =
      ((M : ℝ) - k) * p.coeff k + (k + 1) * p.coeff (k + 1) := by
  rw [show loweringEulerStep M p =
      C (M : ℝ) * p + p.derivative - X * p.derivative by
    simp [loweringEulerStep]
    ring]
  cases k with
  | zero =>
      rw [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul_zero,
        coeff_derivative]
      norm_num
  | succ k =>
      rw [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul,
        coeff_derivative, coeff_derivative]
      push_cast
      ring

theorem loweringEulerStep_nonneg
    {M : ℕ} {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hpdeg : p.natDegree ≤ M) :
    HasNonnegCoeffs (loweringEulerStep M p) := by
  have hshape : loweringEulerStep M p = polarTheta M p + p.derivative := by
    simp [loweringEulerStep, polarTheta, theta]
    ring
  rw [hshape]
  exact (hp.polarTheta hpdeg).add hp.derivative

namespace BorceaBranden

/-- The lowering Euler operator as a real-linear map. -/
def loweringEulerLinearMap (M : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := loweringEulerStep M
  map_add' p q := by
    simp [loweringEulerStep, mul_add]
    ring
  map_smul' c p := by
    simp [loweringEulerStep, smul_eq_C_mul]
    ring

@[simp] theorem loweringEulerLinearMap_apply (M : ℕ) (p : ℝ[X]) :
    loweringEulerLinearMap M p = loweringEulerStep M p := rfl

private theorem polynomialInFirstMv_loweringEulerStep_X_pow
    (M k : ℕ) :
    RealRooted.BorceaBranden.polynomialInFirstMv
        (loweringEulerStep M ((X : ℝ[X]) ^ k)) =
      MvPolynomial.C ((M : ℝ) - k) * MvPolynomial.X 0 ^ k +
        MvPolynomial.C (k : ℝ) * MvPolynomial.X 0 ^ (k - 1) := by
  cases k with
  | zero =>
      simp [loweringEulerStep,
        RealRooted.BorceaBranden.polynomialInFirstMv]
  | succ k =>
      simp only [loweringEulerStep, derivative_pow, derivative_X,
        Nat.cast_add, Nat.cast_one, map_add, map_sub, map_one,
        RealRooted.BorceaBranden.polynomialInFirstMv,
        Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow]
      simp
      ring

/-- The finite algebraic symbol of the lowering Euler operator. -/
theorem loweringEulerSymbol_eq
    (M D : ℕ) (hD : 1 ≤ D) :
    RealRooted.BorceaBranden.finiteAlgebraicSymbol D
        (loweringEulerLinearMap M) =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (D - 1) *
        (MvPolynomial.C ((M : ℝ) - (D : ℝ)) * MvPolynomial.X 0 +
          MvPolynomial.C (M : ℝ) * MvPolynomial.X 1 +
          MvPolynomial.C (D : ℝ)) := by
  let x : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1
  let S : MvPolynomial (Fin 2) ℝ := (x + y) ^ D
  have hS : S = ∑ k ∈ Finset.range (D + 1),
      MvPolynomial.C (D.choose k : ℝ) * x ^ k * y ^ (D - k) := by
    dsimp [S]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    simp
    ring
  have hder : MvPolynomial.pderiv 0 S =
      MvPolynomial.C (D : ℝ) * (x + y) ^ (D - 1) := by
    dsimp [S]
    rw [MvPolynomial.pderiv_pow]
    simp [x, y]
  have hxder : x * MvPolynomial.pderiv 0 S =
      ∑ k ∈ Finset.range (D + 1),
        MvPolynomial.C (D.choose k : ℝ) *
          (MvPolynomial.C (k : ℝ) * x ^ k) * y ^ (D - k) := by
    rw [hS]
    simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_pow]
    simp only [Fin.isValue, zero_mul, map_natCast, MvPolynomial.pderiv_X,
      Pi.single_eq_same, mul_one, zero_add, ne_eq, one_ne_zero,
      not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, x, y]
    cases k with
    | zero => simp
    | succ k =>
        rw [show k + 1 - 1 = k by lia, pow_succ]
        push_cast
        ring
  have hplainDer : MvPolynomial.pderiv 0 S =
      ∑ k ∈ Finset.range (D + 1),
        MvPolynomial.C (D.choose k : ℝ) *
          (MvPolynomial.C (k : ℝ) * x ^ (k - 1)) * y ^ (D - k) := by
    rw [hS]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_pow]
    simp [x, y]
  rw [RealRooted.BorceaBranden.finiteAlgebraicSymbol]
  simp only [loweringEulerLinearMap_apply,
    polynomialInFirstMv_loweringEulerStep_X_pow]
  rw [show (∑ k ∈ Finset.range (D + 1),
      MvPolynomial.C (D.choose k : ℝ) *
        (MvPolynomial.C ((M : ℝ) - k) * x ^ k +
          MvPolynomial.C (k : ℝ) * x ^ (k - 1)) * y ^ (D - k)) =
      MvPolynomial.C (M : ℝ) * S - x * MvPolynomial.pderiv 0 S +
        MvPolynomial.pderiv 0 S by
    rw [hxder, hplainDer, hS]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [map_sub, map_natCast]
    ring]
  rw [hder]
  dsimp [S, x, y]
  have hpow :
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ^ D =
        (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (D - 1) *
          (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    conv_lhs => rw [show D = (D - 1) + 1 by lia, pow_succ]
  rw [hpow]
  simp only [map_sub]
  ring

/-- The residual linear factor in the lowering Euler symbol is stable when
the lowering parameter is strictly above the degree box. -/
theorem loweringEulerResidual_stable
    (M D : ℕ) (hD : 1 ≤ D) (hM : D + 1 ≤ M) :
    MvUpperHalfPlaneStable (complexifyMv
      (MvPolynomial.C ((M : ℝ) - (D : ℝ)) * MvPolynomial.X 0 +
        MvPolynomial.C (M : ℝ) * MvPolynomial.X 1 +
        MvPolynomial.C (D : ℝ) : MvPolynomial (Fin 2) ℝ)) := by
  intro z hz
  simp only [complexifyMv, MvPolynomial.C_sub, map_natCast, Fin.isValue, ne_eq]
  intro hzero
  have him := congrArg Complex.im hzero
  simp [Complex.mul_im] at him
  have hMD : 0 < (M : ℝ) - (D : ℝ) := by
    have hcast : (D : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hMpos : 0 < (M : ℝ) := by
    have hDpos : 0 < D := hD
    exact_mod_cast (lt_of_lt_of_le hDpos (by lia : D ≤ M))
  nlinarith [mul_pos hMD (hz 0), mul_pos hMpos (hz 1)]

/-- The genuine finite algebraic symbol of the lowering Euler operator is
upper-half-plane stable. -/
theorem loweringEulerSymbol_stable
    (M D : ℕ) (hD : 1 ≤ D) (hM : D + 1 ≤ M) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (RealRooted.BorceaBranden.finiteAlgebraicSymbol D
          (loweringEulerLinearMap M))) := by
  rw [loweringEulerSymbol_eq M D hD]
  simpa [complexifyMv] using
    (loweringEulerResidual_stable M D hD hM).mul_X_add_X_pow
      0 1 (D - 1)

end BorceaBranden

/-- On the top degree of its symbol box, the lowering Euler operator retains
degree and a positive leading coefficient. -/
theorem loweringEulerStep_degree_pos
    {M D : ℕ} (hM : D + 1 ≤ M) {p : ℝ[X]}
    (hpdeg : p.natDegree = D) (hpPos : HasPosLeadingCoeff p) :
    (loweringEulerStep M p).natDegree = D ∧
      HasPosLeadingCoeff (loweringEulerStep M p) := by
  have hupper : (loweringEulerStep M p).natDegree ≤ D := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_loweringEulerStep]
    have hpk : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by lia)
    have hpks : p.coeff (k + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by lia)
    simp [hpk, hpks]
  have hpD1 : p.coeff (D + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by lia)
  have htop : p.coeff D = p.leadingCoeff := by
    simpa [hpdeg] using p.coeff_natDegree
  have hweight : 0 < (M : ℝ) - (D : ℝ) := by
    have hcast : (D : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hcoeff : 0 < (loweringEulerStep M p).coeff D := by
    rw [coeff_loweringEulerStep, hpD1, htop]
    simp only [mul_zero, add_zero]
    exact mul_pos hweight hpPos
  have houtdeg := natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeff.ne'
  refine ⟨houtdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, houtdeg]
  exact hcoeff

/-- A lowering Euler operator preserves an oriented PF interlacing pair on
the top degree of a fixed finite-symbol box. -/
theorem loweringEulerStep_prec
    {M D : ℕ} (hD : 1 ≤ D) (hM : D + 1 ≤ M) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpdeg : p.natDegree = D) (hqdeg : q.natDegree = D)
    (hpq : Prec p q) :
    Prec (loweringEulerStep M p) (loweringEulerStep M q) := by
  have hpPos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1
  have hqPos : HasPosLeadingCoeff q :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  have hpout := loweringEulerStep_degree_pos hM hpdeg hpPos
  have hqout := loweringEulerStep_degree_pos hM hqdeg hqPos
  have hprec := BorceaBranden.linearMap_prec_of_finiteSymbol_stable
    (BorceaBranden.loweringEulerSymbol_stable M D hD hM)
    hqdeg.le hpdeg.le hpq hqPos hpPos hqout.2 hpout.2
      (by
        change 1 ≤ (loweringEulerStep M q).natDegree
        rw [hqout.1]
        exact hD)
  simpa only [BorceaBranden.loweringEulerLinearMap_apply] using hprec

/-- The positive-boundary Euler insertion operator preserves an oriented PF
interlacing pair inside a fixed degree box. -/
theorem eulerInsertionStep_one_prec
    {d : ℕ} (hd : 1 ≤ d) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec q p) :
    Prec (eulerInsertionStep 1 d q) (eulerInsertionStep 1 d p) := by
  have hpPos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  have hqPos : HasPosLeadingCoeff q :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1
  have hpout := eulerInsertionStep_degree_pos (c := (1 : ℝ)) hpdeg hpPos
  have hqout := eulerInsertionStep_degree_pos (c := (1 : ℝ)) hqdeg hqPos
  have heq (s : ℝ[X]) :
      BorceaBranden.eulerBidiagonalStepWithConstant 1 d s =
        eulerInsertionStep 1 d s := by
    simp only [BorceaBranden.eulerBidiagonalStepWithConstant,
      eulerInsertionStep]
    ring
  rw [← heq q, ← heq p]
  rw [← heq p] at hpout
  rw [← heq q] at hqout
  exact BorceaBranden.eulerBidiagonalStepWithConstant_prec
    (by norm_num) hd hpdeg hqdeg hpq hpPos hqPos hpout.2 hqout.2
      (by rw [hpout.1]; lia)

theorem loweringEulerStep_theta_eq
    {M : ℕ} (hM : 2 ≤ M) (p : ℝ[X]) :
    loweringEulerStep M (theta p) =
      eulerInsertionStep 1 (M - 2) p.derivative := by
  have hcast : (((M - 2 : ℕ) : ℝ) + 1) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 2 ≤ M)]
    push_cast
    ring
  simp only [loweringEulerStep, theta, eulerInsertionStep, derivative_mul,
    derivative_X, one_mul]
  rw [hcast]
  simp only [map_sub, map_one]
  ring

theorem X_mul_loweringEulerStep_eq
    {M : ℕ} (hM : 1 ≤ M) (p : ℝ[X]) :
    X * loweringEulerStep M p = eulerInsertionStep 0 (M - 1) p := by
  have hcast : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hM)
  simp only [loweringEulerStep, eulerInsertionStep]
  rw [hcast]
  simp
  ring

/-- The oriented derivative-to-zero-boundary Euler relation. -/
theorem eulerInsertionStep_derivative_prec_zeroStep
    {D M : ℕ} (hD : 2 ≤ D) (hM : D + 1 ≤ M) {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = D) :
    Prec (eulerInsertionStep 1 (M - 2) p.derivative)
      (eulerInsertionStep 0 (M - 1) p) := by
  have hp_ne : p ≠ 0 := by
    intro hz
    rw [hz] at hpdeg
    simp at hpdeg
    lia
  have htheta : IsPFPolynomial (theta p) := by
    unfold theta
    exact hp.derivative.X_mul
  have htheta_deg : (theta p).natDegree = D := by
    unfold theta
    rw [natDegree_mul X_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero (by lia)), natDegree_X,
      p.natDegree_derivative, hpdeg]
    lia
  have hbase : Prec p (theta p) := by
    have hder : Prec p.derivative p :=
      (derivative_interlaces (hp.ne_zero_and_splits hp_ne).2
        (by rw [hpdeg]; exact hD)).toPrec
    simpa [theta] using
      prec_mul_X_of_prec_of_nonneg hder
        hp.hasNonnegCoeffs.derivative hp.hasNonnegCoeffs
  have hlower : Prec (loweringEulerStep M p)
      (loweringEulerStep M (theta p)) :=
    loweringEulerStep_prec (by lia) hM hp htheta hpdeg htheta_deg hbase
  have hpM : p.natDegree ≤ M := by rw [hpdeg]; lia
  have hthetaM : (theta p).natDegree ≤ M := by rw [htheta_deg]; lia
  have hlower_p_nn : HasNonnegCoeffs (loweringEulerStep M p) :=
    loweringEulerStep_nonneg hp.hasNonnegCoeffs hpM
  have hlower_theta_nn : HasNonnegCoeffs (loweringEulerStep M (theta p)) :=
    loweringEulerStep_nonneg htheta.hasNonnegCoeffs hthetaM
  have hshift : Prec (loweringEulerStep M (theta p))
      (X * loweringEulerStep M p) :=
    prec_to_prec_mul_X_of_nonneg hlower hlower_p_nn hlower_theta_nn
  rw [loweringEulerStep_theta_eq (by lia : 2 ≤ M),
    X_mul_loweringEulerStep_eq (by lia : 1 ≤ M)] at hshift
  exact hshift

/-- Four crossed Euler completions have one explicit common left
interleaver. -/
theorem crossedEulerCompletion_commonLeftInterleaver
    {D M : ℕ} (hD : 2 ≤ D) (hM : D + 2 ≤ M) {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hp1 : IsPFPolynomial (p + 1))
    (hpdeg : p.natDegree = D) :
    HasCommonLeftInterleaver
      [eulerInsertionStep 1 (M - 2) p,
        eulerInsertionStep 1 (M - 2) (p + 1),
        eulerInsertionStep 0 (M - 1) p,
        eulerInsertionStep 0 (M - 1) (p + 1)] := by
  have hp1deg : (p + 1).natDegree = D := by
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · exact hpdeg
    · rw [natDegree_one, hpdeg]
      lia
  have hp_ne : p ≠ 0 := by
    intro hz
    rw [hz] at hpdeg
    simp at hpdeg
    lia
  have hp1_ne : p + 1 ≠ 0 := by
    intro hz
    rw [hz] at hp1deg
    simp at hp1deg
    lia
  have hp_splits : p.Splits := hp.eq_zero_or_splits.resolve_left hp_ne
  have hp1_splits : (p + 1).Splits := hp1.eq_zero_or_splits.resolve_left hp1_ne
  have hderPF : IsPFPolynomial p.derivative := hp.derivative
  have hder_p : Prec p.derivative p :=
    (derivative_interlaces hp_splits (by rw [hpdeg]; exact hD)).toPrec
  have hder_p1 : Prec p.derivative (p + 1) := by
    have h := (derivative_interlaces hp1_splits
      (by rw [hp1deg]; exact hD)).toPrec
    simpa using h
  have hderdeg : p.derivative.natDegree ≤ M - 2 := by
    rw [p.natDegree_derivative, hpdeg]
    lia
  have hpM : p.natDegree ≤ M - 2 := by rw [hpdeg]; lia
  have hp1M : (p + 1).natDegree ≤ M - 2 := by rw [hp1deg]; lia
  have hT_p : Prec (eulerInsertionStep 1 (M - 2) p.derivative)
      (eulerInsertionStep 1 (M - 2) p) :=
    eulerInsertionStep_one_prec (by lia) hp hderPF hpM hderdeg hder_p
  have hT_p1 : Prec (eulerInsertionStep 1 (M - 2) p.derivative)
      (eulerInsertionStep 1 (M - 2) (p + 1)) :=
    eulerInsertionStep_one_prec (by lia) hp1 hderPF hp1M hderdeg hder_p1
  have hU_p : Prec (eulerInsertionStep 1 (M - 2) p.derivative)
      (eulerInsertionStep 0 (M - 1) p) :=
    eulerInsertionStep_derivative_prec_zeroStep hD (by lia) hp hpdeg
  have hU_p1 : Prec (eulerInsertionStep 1 (M - 2) p.derivative)
      (eulerInsertionStep 0 (M - 1) (p + 1)) := by
    have h := eulerInsertionStep_derivative_prec_zeroStep
      hD (by lia : D + 1 ≤ M) hp1 hp1deg
    simpa using h
  refine ⟨eulerInsertionStep 1 (M - 2) p.derivative, ?_⟩
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact hT_p
  · exact hT_p1
  · exact hU_p
  · exact hU_p1

end RealRooted
