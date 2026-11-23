module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.RiemannHypothesis.MultiplierSequence
import RealRooted.MultiplierSequence.Veronese
import RealRooted.MultiplierSequence.Arithmetic
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Ordinary coefficient sections of shifted xi under RH

These derived consequences use ordinary Taylor sections of every derivative
of the normalized xi function. They differ from arithmetic subsequences of
its raw Taylor derivatives by the indicated factorial ratio.
-/

public section

namespace RealRooted

/-- Under RH, every ordinary Taylor section of each xi derivative defines a
PF multiplier sequence after restoring exponential Taylor normalization. -/
theorem isPFMultiplierSequence_riemannXiCoeff_veronese
    (hRH : RiemannHypothesis) (n : ℕ) {r s : ℕ} (hs : s < r) :
    IsPFMultiplierSequence (fun k ↦
      (k.factorial : ℝ) * riemannXiCoeff (n + (s + r * k)) /
        (s + r * k).factorial) := by
  simpa only [Nat.add_comm _ n] using
    ((isPFMultiplierSequence_riemannXiCoeff hRH).shift n).veronese hs

/-- Under RH, every ordinary Taylor section of each xi derivative is an
entire positive Type-I Laguerre--Pólya function. -/
theorem isLaguerrePolyaTypeI_riemannXiCoeff_veronese
    (hRH : RiemannHypothesis) (n : ℕ) {r s : ℕ} (hs : s < r) :
    IsLaguerrePolyaTypeI (complexExpGeneratingFunction (fun k ↦
      (k.factorial : ℝ) * riemannXiCoeff (n + (s + r * k)) /
        (s + r * k).factorial)) :=
  IsPFMultiplierSequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction
    (isPFMultiplierSequence_riemannXiCoeff_veronese hRH n hs)

/-- Under RH, the ordinary section coefficients of every xi derivative
have a totally nonnegative Toeplitz matrix. -/
theorem isPolyaFreqSeq_riemannXiCoeff_veronese
    (hRH : RiemannHypothesis) (n : ℕ) {r s : ℕ} (hs : s < r) :
    IsPolyaFreqSeq (fun k ↦
      riemannXiCoeff (n + (s + r * k)) / (s + r * k).factorial) := by
  have h := IsPFMultiplierSequence.isPolyaFreqSeq_div_factorial
    (isPFMultiplierSequence_riemannXiCoeff_veronese hRH n hs)
  convert h using 1
  funext k
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hd : ((s + r * k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hk, hd]

end RealRooted
