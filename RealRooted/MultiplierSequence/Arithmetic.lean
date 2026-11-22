module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.ArithmeticSection
import RealRooted.MultiplierSequence.PolyaSchur.Factorial
import RealRooted.MultiplierSequence.PolyaSchur.Limit
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.PFPolynomial.Closure

/-!
# Arithmetic subsequences of positive multiplier sequences

Pólya's arithmetic-section theorem preserves the Type-I Laguerre--Pólya
class. Equivalently, every arithmetic subsequence of a PF multiplier
sequence is again a PF multiplier sequence. Arbitrary starting indices are
allowed. A zero stride gives a constant sequence, hence an exponential.

Reference: G. Pólya, *Über einen Satz von Laguerre*, JDMV 38 (1929),
161--168, §4(b).
-/

public section

open Polynomial Filter Topology

namespace RealRooted

/-- The zero-start arithmetic subsequence of a PF multiplier sequence remains PF. -/
private theorem isPFMultiplierSequence_mul {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (r : ℕ) :
    IsPFMultiplierSequence (fun k => gamma (r * k)) := by
  by_cases hr : r = 0
  · simpa [hr] using isPFMultiplierSequence_const_sequence (hgamma.nonneg 0)
  let p : ℕ → ℝ[X] := fun n => exponentialSection r (rescaledJensenPolynomial (n + 1) gamma)
  have hp (n : ℕ) : IsPFPolynomial (p n) :=
    (hgamma.isPFPolynomial_rescaledJensenPolynomial (n + 1)).exponentialSection r
  apply isPFMultiplierSequence_of_tendsto
    (gamma := fun n k => (k.factorial : ℝ) * (p n).coeff k)
    (fun n => (hp n).isPFMultiplierSequence_factorial_mul_coeff)
  intro k
  have he (n : ℕ) : (k.factorial : ℝ) * (p n).coeff k =
      ((r * k).factorial : ℝ) * (rescaledJensenPolynomial (n + 1) gamma).coeff (r * k) := by
    dsimp only [p]
    rw [coeff_exponentialSection hr]
    field_simp
  simp_rw [he]
  have hl := ((tendsto_coeff_rescaledJensenPolynomial gamma (r * k)).comp
    (tendsto_add_atTop_nat 1)).const_mul ((r * k).factorial : ℝ)
  simpa only [Function.comp_def,
    mul_div_cancel₀ _ (by positivity : ((r * k).factorial : ℝ) ≠ 0)] using hl

/-- Every arithmetic subsequence of a PF multiplier sequence is again a PF
multiplier sequence. The zero stride gives the constant sequence at the start index. -/
theorem IsPFMultiplierSequence.arithmetic {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (r s : ℕ) :
    IsPFMultiplierSequence (fun k => gamma (s + r * k)) := by
  simpa only [Nat.add_comm] using isPFMultiplierSequence_mul (hgamma.shift s) r

/-- The exponential generating function of every arithmetic subsequence
belongs to the positive Type-I Laguerre--Pólya class. -/
theorem IsPFMultiplierSequence.isLaguerrePolyaTypeI_arithmetic {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (r s : ℕ) :
    IsLaguerrePolyaTypeI (complexExpGeneratingFunction (fun k => gamma (s + r * k))) :=
  (hgamma.arithmetic r s).isLaguerrePolyaTypeI_complexExpGeneratingFunction

/-- The factorial-normalized coefficients of a PF multiplier sequence form
a Pólya-frequency sequence. -/
theorem IsPFMultiplierSequence.isPolyaFreqSeq_div_factorial {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) :
    IsPolyaFreqSeq (fun k => gamma k / k.factorial) :=
  IsPolyaFreqSeq.of_tendsto
    (fun n => (hgamma.isPFPolynomial_rescaledJensenPolynomial (n + 1)).to_sequence)
    (fun k => (tendsto_coeff_rescaledJensenPolynomial gamma k).comp (tendsto_add_atTop_nat 1))

end RealRooted
