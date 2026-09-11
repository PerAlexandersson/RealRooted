import RealRooted.FiniteFreeAdditive.HalfIntegerConvolution
import RealRooted.FiniteFreeAdditivePreservation
import RealRooted.Mathlib.Algebra.Polynomial.Expand.Splits

/-!
# Half-integer additive convolution root preservation

This module proves zero-aware splitness and nonnegative-root preservation for
the two generalized rectangular additive convolutions at parameters `-1 / 2`
and `1 / 2`.  The inputs are degree-bounded split real polynomials with
nonnegative roots; the output is allowed to be zero.
-/

open Polynomial

namespace RealRooted

noncomputable section

private theorem natDegree_evenLift_le (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    (finiteFreeAdditiveEvenLift p).natDegree ≤ 2 * n := by
  rw [finiteFreeAdditiveEvenLift, natDegree_expand]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hp

private theorem natDegree_oddLift_le (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    (finiteFreeAdditiveOddLift p).natDegree ≤ 2 * n + 1 := by
  unfold finiteFreeAdditiveOddLift
  calc
    (X * finiteFreeAdditiveEvenLift p).natDegree ≤
        X.natDegree + (finiteFreeAdditiveEvenLift p).natDegree := natDegree_mul_le
    _ ≤ 1 + 2 * n := by
      simpa using Nat.add_le_add_left (natDegree_evenLift_le n p hp) 1
    _ = 2 * n + 1 := by ring

/-- The generalized rectangular additive convolution at `-1 / 2` is split
with nonnegative roots when its degree-bounded inputs are split with
nonnegative roots.  The output may be zero. -/
theorem splits_and_forall_roots_nonneg_generalizedRectangularAdditiveConvolution_neg_half
    (n : ℕ) (p q : ℝ[X])
    (hp : p.Splits) (hq : q.Splits)
    (hproots : ∀ r ∈ p.roots, 0 ≤ r)
    (hqroots : ∀ r ∈ q.roots, 0 ≤ r)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n) :
    (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q).Splits ∧
      ∀ r ∈ (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q).roots,
        0 ≤ r := by
  have hpe : (finiteFreeAdditiveEvenLift p).Splits :=
    Polynomial.splits_expand_two_of_splits_of_forall_roots_nonneg p hp hproots
  have hqe : (finiteFreeAdditiveEvenLift q).Splits :=
    Polynomial.splits_expand_two_of_splits_of_forall_roots_nonneg q hq hqroots
  have hconv := splits_finiteFreeAdditiveConvolution (2 * n) hpe hqe
    (natDegree_evenLift_le n p hpdeg) (natDegree_evenLift_le n q hqdeg)
  rw [finiteFreeAdditiveConvolution_evenLift_eq_generalized] at hconv
  exact Polynomial.splits_and_forall_roots_nonneg_of_splits_expand_two _ hconv

/-- The generalized rectangular additive convolution at `1 / 2` is split
with nonnegative roots when its degree-bounded inputs are split with
nonnegative roots.  The output may be zero. -/
theorem splits_and_forall_roots_nonneg_generalizedRectangularAdditiveConvolution_pos_half
    (n : ℕ) (p q : ℝ[X])
    (hp : p.Splits) (hq : q.Splits)
    (hproots : ∀ r ∈ p.roots, 0 ≤ r)
    (hqroots : ∀ r ∈ q.roots, 0 ≤ r)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n) :
    (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q).Splits ∧
      ∀ r ∈ (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q).roots,
        0 ≤ r := by
  have hpe : (finiteFreeAdditiveEvenLift p).Splits :=
    Polynomial.splits_expand_two_of_splits_of_forall_roots_nonneg p hp hproots
  have hqe : (finiteFreeAdditiveEvenLift q).Splits :=
    Polynomial.splits_expand_two_of_splits_of_forall_roots_nonneg q hq hqroots
  have hpo : (finiteFreeAdditiveOddLift p).Splits :=
    Splits.X.mul hpe
  have hqo : (finiteFreeAdditiveOddLift q).Splits :=
    Splits.X.mul hqe
  have hconv := splits_finiteFreeAdditiveConvolution (2 * n + 1) hpo hqo
    (natDegree_oddLift_le n p hpdeg) (natDegree_oddLift_le n q hqdeg)
  rw [finiteFreeAdditiveConvolution_oddLift_eq_generalized] at hconv
  exact Polynomial.splits_and_forall_roots_nonneg_of_splits_X_mul_expand_two _ hconv

end

end RealRooted
