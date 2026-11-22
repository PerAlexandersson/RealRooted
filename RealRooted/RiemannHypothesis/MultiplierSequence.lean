module

public import RealRooted.RiemannHypothesis
import RealRooted.RiemannHypothesis.Inequalities
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.MultiplierSequence.JensenDerivative
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Positive xi multiplier sequences and negative Jensen roots

Unconditional coefficient positivity gives exact degrees and excludes all
nonnegative real roots. Under RH the Jensen polynomials split and the xi
coefficients form a PF multiplier sequence. Shifts and pointwise products then
give further real-rootedness preservers.
-/

public section

open Polynomial

namespace RealRooted

/-- Every coefficient through the degree parameter is strictly positive. -/
theorem coeff_riemannXiJensenPolynomial_pos (d n k : ℕ) (hk : k ≤ d) :
    0 < (riemannXiJensenPolynomial d n).coeff k := by
  rw [coeff_riemannXiJensenPolynomial, ite_eq_left hk]
  exact mul_pos (by exact_mod_cast Nat.choose_pos hk) (riemannXiCoeff_pos _)

/-- All xi Jensen polynomials have nonnegative coefficients, unconditionally. -/
theorem hasNonnegCoeffs_riemannXiJensenPolynomial (d n : ℕ) :
    HasNonnegCoeffs (riemannXiJensenPolynomial d n) :=
  hasNonnegCoeffs_jensenPolynomial (n := d) (fun k => (riemannXiCoeff_pos (n + k)).le)

/-- The degree parameter is exact; no RH assumption is needed. -/
theorem natDegree_riemannXiJensenPolynomial (d n : ℕ) :
    (riemannXiJensenPolynomial d n).natDegree = d :=
  natDegree_jensenPolynomial (riemannXiCoeff_pos (n + d)).ne'

/-- Xi Jensen polynomials are nonzero, including in degree zero. -/
theorem riemannXiJensenPolynomial_ne_zero (d n : ℕ) :
    riemannXiJensenPolynomial d n ≠ 0 := by
  intro h
  have hp := coeff_riemannXiJensenPolynomial_pos d n 0 (Nat.zero_le _)
  simp [h] at hp

/-- Every real root is strictly negative. RH additionally says that all roots are real. -/
theorem riemannXiJensenPolynomial_roots_neg (d n : ℕ) :
    ∀ x ∈ (riemannXiJensenPolynomial d n).roots, x < 0 :=
  roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (hasNonnegCoeffs_riemannXiJensenPolynomial d n)
    (coeff_riemannXiJensenPolynomial_pos d n 0 (Nat.zero_le _)).ne'

/-- Under RH the xi Jensen polynomials are PF polynomials. -/
theorem riemannXiJensenPolynomial_isPF (hRH : RiemannHypothesis) (d n : ℕ) :
    IsPFPolynomial (riemannXiJensenPolynomial d n) :=
  IsPFPolynomial.of_realRooted_nonneg (hasNonnegCoeffs_riemannXiJensenPolynomial d n)
    (riemannXiJensenPolynomial_splits hRH d n)

/-- The normalized xi coefficients form a PF multiplier sequence under RH. -/
theorem isPFMultiplierSequence_riemannXiCoeff (hRH : RiemannHypothesis) :
    IsPFMultiplierSequence riemannXiCoeff := by
  apply isPFMultiplierSequence_iff_jensenPolynomial_isPF.mpr
  intro d
  simpa only [riemannXiJensenPolynomial, Nat.zero_add] using
    riemannXiJensenPolynomial_isPF hRH d 0

/-- In particular, diagonal multiplication by xi coefficients preserves real-rootedness. -/
theorem isMultiplierSequence_riemannXiCoeff (hRH : RiemannHypothesis) :
    IsMultiplierSequence riemannXiCoeff :=
  (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
    (isPFMultiplierSequence_riemannXiCoeff hRH)).1

/-- Every forward shift of the xi sequence is a PF multiplier sequence under RH. -/
theorem isPFMultiplierSequence_riemannXiCoeff_shift (hRH : RiemannHypothesis) (n : ℕ) :
    IsPFMultiplierSequence (fun k => riemannXiCoeff (n + k)) := by
  simpa only [Nat.add_comm] using (isPFMultiplierSequence_riemannXiCoeff hRH).shift n

/-- Pointwise multiplication by any PF multiplier sequence gives another such sequence. -/
theorem isPFMultiplierSequence_riemannXiCoeff_mul (hRH : RiemannHypothesis)
    {delta : ℕ → ℝ} (hdelta : IsPFMultiplierSequence delta) :
    IsPFMultiplierSequence (fun k => riemannXiCoeff k * delta k) :=
  (isPFMultiplierSequence_riemannXiCoeff hRH).mul hdelta

/-- The xi diagonal operator preserves splitting over the reals under RH. -/
theorem diagonalOperator_riemannXiCoeff_splits (hRH : RiemannHypothesis)
    {p : ℝ[X]} (hp : p.Splits) : (diagonalOperator riemannXiCoeff p).Splits := by
  rcases (isMultiplierSequence_riemannXiCoeff hRH).diagonalOperator_eq_zero_or_splits hp
    with h | h
  · rw [h]
    exact Splits.zero
  · exact h

/-- The xi diagonal operator preserves the PF polynomial cone under RH. -/
theorem diagonalOperator_riemannXiCoeff_isPF (hRH : RiemannHypothesis)
    {p : ℝ[X]} (hp : IsPFPolynomial p) : IsPFPolynomial (diagonalOperator riemannXiCoeff p) :=
  (isPFMultiplierSequence_riemannXiCoeff hRH).diagonalOperator_isPF hp

/-- Consecutive shifted xi Jensen polynomials have weakly interleaving root lists
with degree gap one. This does not assert distinct roots. -/
theorem riemannXiJensenPolynomial_shift_interlaces (hRH : RiemannHypothesis) (d n : ℕ) :
    Interlaces (riemannXiJensenPolynomial d (n + 1))
      (riemannXiJensenPolynomial (d + 1) n) := by
  have h := (riemannXiJensenPolynomial_shift_interl hRH d n).toStrictInterl_of_ne
    (riemannXiJensenPolynomial_ne_zero _ _) (riemannXiJensenPolynomial_ne_zero _ _)
  exact h.toInterlaces (by simp only [natDegree_riemannXiJensenPolynomial])

end RealRooted
