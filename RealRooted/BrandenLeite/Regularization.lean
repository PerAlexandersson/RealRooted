import RealRooted.Mathlib.Topology.Algebra.Polynomial
import RealRooted.PFPolynomial
import RealRooted.PolyaFrequencyConvolution.Basic

/-!
# Finite binomial regularization of PF sequences

This file isolates the sequence-level regularization used in the
zero-constant Brändén--Saud Leite theorem.  Convolution with the coefficient
sequence of a shifted power preserves the PF property, has positive zeroth
entry for a positive shift, and converges coefficientwise to insertion of a
finite zero prefix as the shift tends to zero.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted.BrandenLeite

/-- Coefficients of the regularizing polynomial (X + ε)^r. -/
def shiftedPowerCoeffs (r : ℕ) (ε : ℝ) : ℕ → ℝ :=
  fun n => ((X + C ε : ℝ[X]) ^ r).coeff n

/-- Convolution of a sequence with the coefficients of (X + ε)^r. -/
def regularizedSequence (r : ℕ) (u : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ :=
  natCauchyConvolution (shiftedPowerCoeffs r ε) u

/-- Nonnegative binomial shifts preserve the PF property after convolution. -/
theorem regularizedSequence_isPolyaFreqSeq
    {u : ℕ → ℝ} (hu : IsPolyaFreqSeq u) (r : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsPolyaFreqSeq (regularizedSequence r u ε) := by
  apply IsPolyaFreqSeq.natCauchyConvolution _ hu
  exact ((isPFPolynomial_X_add_C hε).pow r).to_sequence

/-- The zeroth regularized coefficient is ε^r times the zeroth tail
coefficient. -/
theorem regularizedSequence_zero
    (r : ℕ) (u : ℕ → ℝ) (ε : ℝ) :
    regularizedSequence r u ε 0 = ε ^ r * u 0 := by
  simp only [regularizedSequence, natCauchyConvolution, Nat.zero_add,
    Finset.range_one, Finset.sum_singleton, Nat.zero_sub, shiftedPowerCoeffs]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- A positive shift and a positive initial tail coefficient give a positive
zeroth regularized coefficient. -/
theorem regularizedSequence_zero_pos
    {r : ℕ} {u : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) (hu0 : 0 < u 0) :
    0 < regularizedSequence r u ε 0 := by
  rw [regularizedSequence_zero]
  exact mul_pos (pow_pos hε r) hu0

/-- At shift zero, regularization inserts exactly r leading zeros. -/
theorem regularizedSequence_at_zero
    (r : ℕ) (u : ℕ → ℝ) (n : ℕ) :
    regularizedSequence r u 0 n =
      if r ≤ n then u (n - r) else 0 := by
  simp [regularizedSequence, natCauchyConvolution, shiftedPowerCoeffs,
    Polynomial.coeff_X_pow]

/-- Each regularized coefficient converges to the corresponding coefficient
of the zero-prefixed tail as the shift tends to zero. -/
theorem tendsto_regularizedSequence
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (r : ℕ) (u : ℕ → ℝ) (n : ℕ) :
    Tendsto (fun k => regularizedSequence r u (ε k) n) l
      (𝓝 (if r ≤ n then u (n - r) else 0)) := by
  rw [← regularizedSequence_at_zero]
  unfold regularizedSequence natCauchyConvolution
  apply tendsto_finsetSum
  intro i _
  apply Tendsto.mul_const
  simpa [shiftedPowerCoeffs, Function.comp_def] using
    ((Polynomial.continuous_coeff_comp_X_add_C (X ^ r) i).continuousAt.tendsto.comp hε)

end RealRooted.BrandenLeite
