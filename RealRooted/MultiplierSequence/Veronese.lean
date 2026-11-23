module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PolyaSchur.Factorial
import RealRooted.MultiplierSequence.PolyaSchur.Limit
import RealRooted.VeroneseSection

/-!
# Ordinary coefficient sections of positive Type-I entire functions

The coefficient section with stride `r` and residue `s < r` takes ordinary
Taylor coefficients, whereas arithmetic sections take raw derivatives. In
exponential Taylor normalization its multiplier sequence is
`k! * gamma (s + r*k) / (s + r*k)!`.

The constant sequence specializes to the Mittag--Leffler series
`sum z^k / (s + r*k)!`. For `s = 0`, these are the functions used by
Kim--Kim (2015), Proposition 2.4. Strict Jensen roots are a separate result.
-/

public section

open Polynomial Filter Topology

namespace RealRooted

/-- Ordinary coefficient sections of a PF exponential series give PF multiplier
sequences after restoring the exponential normalization. The residue is strictly
smaller than the stride; arbitrary ordinary coefficient tails need not be PF. -/
theorem IsPFMultiplierSequence.veronese {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) {r s : ℕ} (hs : s < r) :
    IsPFMultiplierSequence (fun k ↦
      (k.factorial : ℝ) * gamma (s + r * k) / (s + r * k).factorial) := by
  have hr : 0 < r := (Nat.zero_le s).trans_lt hs
  let p : ℕ → ℝ[X] := fun n ↦
    veroneseSectionPolynomial r s (rescaledJensenPolynomial n gamma)
  have hp (n : ℕ) : IsPFPolynomial (p n) :=
    IsPFPolynomial.of_polyaFreqSeq
      (isPolyaFreqSeq_veroneseSectionPolynomial_coeff
        (hgamma.isPFPolynomial_rescaledJensenPolynomial n).to_sequence hr hs)
  apply isPFMultiplierSequence_of_tendsto
    (gamma := fun n k ↦ (k.factorial : ℝ) * (p n).coeff k)
    (fun n ↦ (hp n).isPFMultiplierSequence_factorial_mul_coeff)
  intro k
  simpa only [p, coeff_veroneseSectionPolynomial hr, mul_div_assoc] using
    (tendsto_coeff_rescaledJensenPolynomial gamma (s + r * k)).const_mul
      (k.factorial : ℝ)

/-- Every ordinary coefficient section of a positive Type-I exponential
series is again an entire positive Type-I function. -/
theorem IsPFMultiplierSequence.isLaguerrePolyaTypeI_veronese {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) {r s : ℕ} (hs : s < r) :
    IsLaguerrePolyaTypeI (complexExpGeneratingFunction (fun k ↦
      (k.factorial : ℝ) * gamma (s + r * k) / (s + r * k).factorial)) :=
  (hgamma.veronese hs).isLaguerrePolyaTypeI_complexExpGeneratingFunction

/-- The factorial ratios `k! / (s + r*k)!` are PF multiplier sequences for
all residues `s < r`, including `r = 1, s = 0`. -/
theorem isPFMultiplierSequence_factorial_veronese {r s : ℕ} (hs : s < r) :
    IsPFMultiplierSequence (fun k ↦ (k.factorial : ℝ) / (s + r * k).factorial) := by
  simpa only [mul_one] using
    (isPFMultiplierSequence_const_sequence (zero_le_one : (0 : ℝ) ≤ 1)).veronese hs

/-- Integer-stride Mittag--Leffler series, in exponential Taylor notation,
are positive Type-I entire functions at every residue below the stride. -/
theorem isLaguerrePolyaTypeI_factorial_veronese {r s : ℕ} (hs : s < r) :
    IsLaguerrePolyaTypeI (complexExpGeneratingFunction
      (fun k ↦ (k.factorial : ℝ) / (s + r * k).factorial)) :=
  (isPFMultiplierSequence_factorial_veronese hs).isLaguerrePolyaTypeI_complexExpGeneratingFunction

end RealRooted
