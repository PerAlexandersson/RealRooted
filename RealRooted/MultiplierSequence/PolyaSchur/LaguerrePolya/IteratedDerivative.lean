module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Iterated derivatives of Laguerre--Pólya functions

Every finite complex derivative of a zero-aware Laguerre--Pólya function
remains in the class.
-/

public section

namespace RealRooted

/-- The Laguerre--Pólya class is closed under every iterated complex derivative. -/
theorem IsLaguerrePolya.iteratedDeriv {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (n : ℕ) :
    IsLaguerrePolya (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

end RealRooted
