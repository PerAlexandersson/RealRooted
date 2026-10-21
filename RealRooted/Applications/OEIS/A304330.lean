import RealRooted.BorceaBranden.Applications.BidiagonalSymbol.RealConsequences
import RealRooted.Interlacing.WindowInduction
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness

/-!
# The A304330 model

After removing the common factor `X`, the row update is the composition of a
coefficient-bidiagonal stable operator and `thetaPlusOne`.  This gives the
orientation missing from the direct Ma--Wang argument.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS.A304330

/-- Diagonal weights for the first factor of the divided A304330 update. -/
def alpha (k : ℕ) : ℝ := k + 1

/-- Superdiagonal weights for the first factor of the divided A304330 update. -/
def beta (k : ℕ) : ℝ := 4 * k + 6

/-- The first factor of the divided A304330 update. -/
def mOperator (p : ℝ[X]) : ℝ[X] :=
  (1 + C 6 * X) * p + (X + C 4 * X ^ 2) * p.derivative

theorem mOperator_eq_bidiagonalOperator (p : ℝ[X]) :
    mOperator p = bidiagonalOperator alpha beta p := by
  rw [show alpha = fun k : ℕ => 1 + 1 * (k : ℝ) by
    funext k
    unfold alpha
    ring,
    show beta = fun k : ℕ => 6 + 4 * (k : ℝ) by
      funext k
      unfold beta
      ring]
  rw [bidiagonalOperator_affine_weights]
  simp only [mOperator]
  rw [map_one]
  ring

/-- Closed form of the finite algebraic symbol of `mOperator`. -/
theorem affineBidiagonalSymbol_eq (d : ℕ) (hd : 1 ≤ d) :
    RealRooted.BorceaBranden.affineBidiagonalSymbol alpha beta d =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 1) *
        (MvPolynomial.C ((4 * d + 6 : ℕ) : ℝ) * MvPolynomial.X 0 ^ 2 +
          MvPolynomial.C 6 * MvPolynomial.X 0 * MvPolynomial.X 1 +
          MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 +
          MvPolynomial.X 1) := by
  let x : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1
  let S : MvPolynomial (Fin 2) ℝ := (x + y) ^ d
  have hdx : MvPolynomial.pderiv 0 x = 1 := by simp [x]
  have hdy : MvPolynomial.pderiv 0 y = 0 := by simp [y]
  have htermder (k : ℕ) :
      x * MvPolynomial.pderiv 0
          (MvPolynomial.C (d.choose k : ℝ) * x ^ k * y ^ (d - k)) =
        MvPolynomial.C (k : ℝ) *
          (MvPolynomial.C (d.choose k : ℝ) * x ^ k * y ^ (d - k)) := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_pow, hdx, hdy]
    cases k with
    | zero => simp
    | succ k =>
        rw [show k + 1 - 1 = k by lia, pow_succ]
        push_cast
        rw [show MvPolynomial.C ((k : ℝ) + 1) =
          MvPolynomial.C (k : ℝ) + (1 : MvPolynomial (Fin 2) ℝ) by
            rw [map_add, map_one]]
        rw [map_natCast]
        rw [show MvPolynomial.C (k : ℝ) =
          (k : MvPolynomial (Fin 2) ℝ) by exact map_natCast _ k]
        ring
  have hS : S = ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) * x ^ k * y ^ (d - k) := by
    dsimp [S]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    simp
    ring
  have hder : MvPolynomial.pderiv 0 S =
      MvPolynomial.C (d : ℝ) * (x + y) ^ (d - 1) := by
    dsimp [S]
    rw [MvPolynomial.pderiv_pow]
    simp [x, y]
  have hA : ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (alpha k) * x ^ k) * y ^ (d - k) =
      x * MvPolynomial.pderiv 0 S + S := by
    rw [hS]
    simp only [map_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [htermder]
    unfold alpha
    rw [show MvPolynomial.C ((k : ℝ) + 1) =
      MvPolynomial.C (k : ℝ) + (1 : MvPolynomial (Fin 2) ℝ) by
        rw [map_add, map_one]]
    ring
  have hB : ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (beta k) * x ^ (k + 1)) * y ^ (d - k) =
      x * (MvPolynomial.C 4 * (x * MvPolynomial.pderiv 0 S) +
        MvPolynomial.C 6 * S) := by
    rw [hS]
    simp only [map_sum, Finset.mul_sum]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [htermder]
    unfold beta
    rw [pow_succ]
    rw [show MvPolynomial.C ((4 : ℝ) * k + 6) =
      MvPolynomial.C 4 * MvPolynomial.C (k : ℝ) + MvPolynomial.C 6 by
        rw [map_add, map_mul]]
    ring
  rw [RealRooted.BorceaBranden.affineBidiagonalSymbol]
  change (∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (alpha k) * x ^ k +
          MvPolynomial.C (beta k) * x ^ (k + 1)) * y ^ (d - k)) = _
  rw [show (∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (alpha k) * x ^ k +
          MvPolynomial.C (beta k) * x ^ (k + 1)) * y ^ (d - k)) =
      (∑ k ∈ Finset.range (d + 1),
        MvPolynomial.C (d.choose k : ℝ) *
          (MvPolynomial.C (alpha k) * x ^ k) * y ^ (d - k)) +
      (∑ k ∈ Finset.range (d + 1),
        MvPolynomial.C (d.choose k : ℝ) *
          (MvPolynomial.C (beta k) * x ^ (k + 1)) * y ^ (d - k)) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring, hA, hB, hder]
  dsimp [S, x, y]
  push_cast
  have hpow :
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ^ d =
        (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 1) *
          (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by lia, pow_succ]
  rw [hpow]
  rw [show MvPolynomial.C ((d : ℝ) + 1) =
      MvPolynomial.C (d : ℝ) + 1 by rw [map_add, map_one],
    show MvPolynomial.C (4 * (d : ℝ) + 6) =
      MvPolynomial.C 4 * MvPolynomial.C (d : ℝ) + MvPolynomial.C 6 by
        rw [map_add, map_mul]]
  ring

/-- The residual quadratic factor in the A304330 finite symbol is stable. -/
theorem affineBidiagonalResidual_stable (d : ℕ) :
    MvUpperHalfPlaneStable (complexifyMv
      ((MvPolynomial.C ((4 * d + 6 : ℕ) : ℝ) * MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C 6 * MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 +
        MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ))) := by
  intro z hz
  simp only [complexifyMv, Fin.isValue, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, MvPolynomial.C_add, MvPolynomial.C_mul, map_natCast,
    ne_eq]
  intro hzero
  have hb : 0 < (z 0).im := hz 0
  have he : 0 < (z 1).im := hz 1
  have hA : 0 < (4 : ℝ) * d + 6 := by positivity
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp only [Fin.isValue, pow_two, map_add, map_mul, MvPolynomial.map_X,
    map_natCast, MvPolynomial.map_C, Complex.ofRealHom_eq_coe,
    MvPolynomial.eval_X, MvPolynomial.eval_C, Complex.add_re, Complex.mul_re,
    Complex.natCast_re, Complex.add_im, Complex.natCast_im,
    add_zero, zero_mul, sub_zero, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im] at hre him
  have hbracket :
      0 < 6 * ((4 : ℝ) * d + 6) *
          (((z 0).re + 1 / 6) ^ 2 + (z 0).im ^ 2) + (d : ℝ) / 3 := by
    positivity
  have hcombo :
      (z 1).im * ((6 * (z 0).re + 1) ^ 2 + (6 * (z 0).im) ^ 2) +
        (z 0).im *
          (6 * ((4 : ℝ) * d + 6) *
            (((z 0).re + 1 / 6) ^ 2 + (z 0).im ^ 2) + (d : ℝ) / 3) = 0 := by
    linear_combination
      (6 * (z 0).re + 1) * him - 6 * (z 0).im * hre
  have hdenpos :
      0 < (6 * (z 0).re + 1) ^ 2 + (6 * (z 0).im) ^ 2 := by
    nlinarith [sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hb),
      sq_nonneg (6 * (z 0).re + 1)]
  linarith [mul_pos he hdenpos, mul_pos hb hbracket]

/-- The finite algebraic symbol of `mOperator` is stable on every positive box. -/
theorem affineBidiagonalSymbol_stable (d : ℕ) (hd : 1 ≤ d) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (RealRooted.BorceaBranden.finiteAlgebraicSymbol d
          (RealRooted.BorceaBranden.bidiagonalLinearMap alpha beta))) := by
  rw [RealRooted.BorceaBranden.finiteAlgebraicSymbol_bidiagonalLinearMap,
    affineBidiagonalSymbol_eq d hd]
  simpa [complexifyMv] using
    (affineBidiagonalResidual_stable d).mul_X_add_X_pow 0 1 (d - 1)

private theorem mOperator_degree_pos {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    (mOperator p).natDegree = p.natDegree + 1 ∧ HasPosLeadingCoeff (mOperator p) := by
  rw [mOperator_eq_bidiagonalOperator]
  let m := p.natDegree
  have hcoeff : (bidiagonalOperator alpha beta p).coeff (m + 1) =
      ((4 : ℝ) * m + 6) * p.leadingCoeff := by
    rw [coeff_bidiagonalOperator_succ]
    have hzero : p.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simp [m])
    rw [hzero, mul_zero, zero_add, p.coeff_natDegree]
    simp [beta]
  have hcoeff_pos : 0 < (bidiagonalOperator alpha beta p).coeff (m + 1) := by
    rw [hcoeff]
    exact mul_pos (by positivity) hp
  have hdegree : (bidiagonalOperator alpha beta p).natDegree = m + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_bidiagonalOperator_le alpha beta p) hcoeff_pos.ne'
  refine ⟨hdegree, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdegree]
  exact hcoeff_pos

private theorem mOperator_nonneg {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (mOperator p) := by
  rw [mOperator_eq_bidiagonalOperator]
  exact hp.bidiagonalOperator
    (fun k => by unfold alpha; positivity)
    (fun k => by unfold beta; positivity)

/-- The divided A304330 model. -/
def qPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => thetaPlusOne (mOperator (qPolynomial n))

private theorem qPolynomial_invariants : ∀ n : ℕ,
    (qPolynomial n).natDegree = n ∧
      HasNonnegCoeffs (qPolynomial n) ∧
      HasPosLeadingCoeff (qPolynomial n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨by simp [qPolynomial], hasNonnegCoeffs_one, ?_⟩
      simp [qPolynomial, HasPosLeadingCoeff]
  | succ n ih =>
      have hm := mOperator_degree_pos ih.2.2
      have hm0 : mOperator (qPolynomial n) ≠ 0 := hm.2.ne_zero
      have hdeg : (qPolynomial (n + 1)).natDegree = n + 1 := by
        rw [qPolynomial, natDegree_thetaPlusOne_of_ne_zero hm0, hm.1, ih.1]
      refine ⟨hdeg, (mOperator_nonneg ih.2.1).thetaPlusOne, ?_⟩
      rw [HasPosLeadingCoeff, leadingCoeff, hdeg, qPolynomial,
        coeff_thetaPlusOne]
      have hindex : n + 1 = (mOperator (qPolynomial n)).natDegree := by
        rw [hm.1, ih.1]
      rw [hindex, coeff_natDegree]
      exact mul_pos (by positivity) hm.2

private theorem qPolynomial_isPF (n : ℕ) : IsPFPolynomial (qPolynomial n) := by
  induction n with
  | zero => exact IsPFPolynomial.one
  | succ n ih =>
      have hm : IsPFPolynomial (mOperator (qPolynomial n)) := by
        rw [mOperator_eq_bidiagonalOperator]
        apply RealRooted.BorceaBranden.bidiagonalOperator_isPF_of_affineSymbol_stable
          (affineBidiagonalSymbol_stable (n + 1) (by lia))
          (fun k => by unfold alpha; positivity)
          (fun k => by unfold beta; positivity)
          (by rw [(qPolynomial_invariants n).1]; lia) ih
      simpa only [qPolynomial] using thetaPlusOne_preserves_pf hm

/-- Consecutive divided A304330 rows are strictly interlacing. -/
theorem qPolynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (qPolynomial n) (qPolynomial (n + 1)) := by
  induction n with
  | zero =>
      apply (interlaces_one_linear (p := qPolynomial 1) ?_).toStrictInterl
      exact (qPolynomial_invariants 1).1
  | succ n ih =>
      have hm : StrictInterl (mOperator (qPolynomial n))
          (mOperator (qPolynomial (n + 1))) := by
        rw [mOperator_eq_bidiagonalOperator, mOperator_eq_bidiagonalOperator]
        have hpout := (mOperator_degree_pos
          (qPolynomial_invariants (n + 1)).2.2).2
        have hqout := (mOperator_degree_pos
          (qPolynomial_invariants n).2.2).2
        have hpoutdeg : 1 ≤ (mOperator (qPolynomial (n + 1))).natDegree := by
          rw [(mOperator_degree_pos (qPolynomial_invariants (n + 1)).2.2).1]
          lia
        rw [mOperator_eq_bidiagonalOperator] at hpout hqout hpoutdeg
        apply RealRooted.BorceaBranden.bidiagonalOperator_strictInterl_of_affineSymbol_stable
          (affineBidiagonalSymbol_stable (n + 2) (by lia))
          (by rw [(qPolynomial_invariants (n + 1)).1]; lia)
          (by rw [(qPolynomial_invariants n).1]; lia) ih
          (qPolynomial_invariants (n + 1)).2.2
          (qPolynomial_invariants n).2.2 hpout hqout hpoutdeg
      simpa only [qPolynomial] using hm.thetaPlusOne_of_pf
        (by
          rw [mOperator_eq_bidiagonalOperator]
          exact RealRooted.BorceaBranden.bidiagonalOperator_isPF_of_affineSymbol_stable
            (affineBidiagonalSymbol_stable (n + 2) (by lia))
            (fun k => by unfold alpha; positivity)
            (fun k => by unfold beta; positivity)
            (by rw [(qPolynomial_invariants n).1]; lia)
            (qPolynomial_isPF n))
        (by
          rw [mOperator_eq_bidiagonalOperator]
          exact RealRooted.BorceaBranden.bidiagonalOperator_isPF_of_affineSymbol_stable
            (affineBidiagonalSymbol_stable (n + 2) (by lia))
            (fun k => by unfold alpha; positivity)
            (fun k => by unfold beta; positivity)
            (by rw [(qPolynomial_invariants (n + 1)).1]; lia)
            (qPolynomial_isPF (n + 1)))

/-- The A304330 model, with its common `X` factor visible after row zero. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * qPolynomial n

/-- The downstream A304330 update. -/
def nextRow (_n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X ^ 2 + C 4 * X ^ 3) * p.derivative.derivative +
    (X + C 10 * X ^ 2) * p.derivative + C 2 * X * p

private theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) := by
  simp only [polynomial, qPolynomial, nextRow, mOperator, thetaPlusOne, theta,
    derivative_add, derivative_mul, derivative_X, derivative_one, derivative_C,
    derivative_pow, zero_mul, zero_add, one_mul]
  norm_num [map_ofNat]
  ring

/-- Every A304330 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  cases n with
  | zero => simp [polynomial]
  | succ n =>
      rw [polynomial]
      exact Polynomial.Splits.X.mul
        ((qPolynomial_isPF n).eq_zero_or_splits.resolve_left
          (qPolynomial_invariants n).2.2.ne_zero)

/-- Consecutive A304330 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) := by
  cases n with
  | zero =>
      rw [show polynomial 0 = 1 by rfl,
        show polynomial 1 = X by simp [polynomial, qPolynomial]]
      exact interlaces_one_linear (p := X) (by simp)
  | succ n =>
      simp only [polynomial]
      apply (by
        simpa using (qPolynomial_strictInterl_succ n).mul_X_sub_C_both 0 :
          StrictInterl (X * qPolynomial n) (X * qPolynomial (n + 1))).toInterlaces
      rw [natDegree_mul X_ne_zero (qPolynomial_invariants n).2.2.ne_zero,
        natDegree_mul X_ne_zero (qPolynomial_invariants (n + 1)).2.2.ne_zero,
        natDegree_X, (qPolynomial_invariants n).1,
        (qPolynomial_invariants (n + 1)).1]
      lia

private theorem polynomial_zero : polynomial 0 = 1 := rfl

private theorem polynomial_one : polynomial 1 = X := by simp [polynomial, qPolynomial]

private theorem polynomial_two : polynomial 2 = X + 12 * X ^ 2 := by
  simp [polynomial, qPolynomial, mOperator, thetaPlusOne, theta]
  norm_num [map_ofNat]
  ring

/-- A sequence with the A304330 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (_htwo : P 2 = X + 12 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (fun n p => if n = 0 then X else nextRow (n - 1) p)
    (hzero.trans polynomial_zero.symm)
    (fun n => by
      cases n with
      | zero => simpa using hone
      | succ n => simpa using hrec n)
    (fun n => by
      cases n with
      | zero => simpa using polynomial_one
      | succ n => simpa using polynomial_recurrence n)
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows of a sequence with the A304330 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (_htwo : P 2 = X + 12 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (fun n p => if n = 0 then X else nextRow (n - 1) p)
    (hzero.trans polynomial_zero.symm)
    (fun n => by
      cases n with
      | zero => simpa using hone
      | succ n => simpa using hrec n)
    (fun n => by
      cases n with
      | zero => simpa using polynomial_one
      | succ n => simpa using polynomial_recurrence n)
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A304330
