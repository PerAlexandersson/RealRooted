import RealRooted.MultiplierSequence.PolyaSchur.Growth
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros

/-!
# Pólya--Schur challenge entry point

Human statement: a pointwise nonnegative (PF) multiplier sequence has a
Laguerre--Pólya exponential-generating function, and every non-real zero of a
nonzero such function is excluded (issue #563, partial).

The first assertion is the checked forward endpoint
`IsPFMultiplierSequence.isLaguerrePolya_complexExpGeneratingFunction`; the
real-zero conclusion is the checked zero-closure endpoint
`IsLaguerrePolya.im_eq_zero_of_eq_zero`.  The full analytic Pólya--Schur
classification, including its converse and canonical product description,
remains outside this challenge facade.
-/

namespace RealRooted
namespace Challenges
namespace PolyaSchur

/-- The complex exponential-generating function attached to a real sequence. -/
noncomputable abbrev ComplexExponentialGeneratingFunction (gamma : ℕ → ℝ) : ℂ → ℂ :=
  complexExpGeneratingFunction gamma

/-- A PF multiplier sequence has a zero-aware Laguerre--Pólya complex EGF. -/
theorem pfMultiplier_egf_isLaguerrePolya
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) :
    IsLaguerrePolya (ComplexExponentialGeneratingFunction gamma) := by
  exact hgamma.isLaguerrePolya_complexExpGeneratingFunction

/-- Every zero of a nonzero PF-multiplier EGF lies on the real axis. -/
theorem pfMultiplier_egf_real_zero
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hne : ComplexExponentialGeneratingFunction gamma ≠ 0)
    {z : ℂ} (hz : ComplexExponentialGeneratingFunction gamma z = 0) :
    z.im = 0 := by
  exact (pfMultiplier_egf_isLaguerrePolya hgamma).im_eq_zero_of_eq_zero hne hz

/-- Alternating the signs of a PF multiplier sequence gives the reflected
Laguerre--Pólya EGF, corresponding to precomposition by `z ↦ -z`. -/
theorem pfMultiplier_alternating_egf_isLaguerrePolya
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) :
    IsLaguerrePolya
      (complexExpGeneratingFunction (fun k => (-1 : ℝ) ^ k * gamma k)) := by
  exact hgamma.isLaguerrePolya_complexExpGeneratingFunction_alternating

end PolyaSchur
end Challenges
end RealRooted
