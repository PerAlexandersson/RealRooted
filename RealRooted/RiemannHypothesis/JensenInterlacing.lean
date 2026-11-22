module

public import RealRooted.RiemannHypothesis
import RealRooted.RiemannHypothesis.MultiplierSequence
import RealRooted.RiemannHypothesis.JensenSimple
import RealRooted.MultiplierSequence.JensenPositiveInterlacing
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity

/-!
# Strict separation of consecutive xi Jensen degrees

Under RH, positive xi multiplier coefficients give interlacing at each fixed
coefficient shift. Simplicity and the Jensen Euler identity exclude common
roots, so the root inequalities are strict. These are unshifted adjacent
degrees, distinct from the derivative relation that also changes the shift.
-/

public section

namespace RealRooted

/-- Under RH, consecutive xi Jensen degrees at a fixed shift are in directed interlacing. -/
theorem strictInterl_riemannXiJensenPolynomial_succ
    (hRH : RiemannHypothesis) (d n : ℕ) :
    StrictInterl (riemannXiJensenPolynomial d n) (riemannXiJensenPolynomial (d + 1) n) := by
  exact strictInterl_jensenPolynomial_succ_of_pos
    (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_riemannXiCoeff_shift hRH n)).1
    (fun k => riemannXiCoeff_pos (n + k)) d

/-- Consecutive xi Jensen degrees at a fixed shift have interleaving real root lists under RH. -/
theorem interlaces_riemannXiJensenPolynomial_succ
    (hRH : RiemannHypothesis) (d n : ℕ) :
    Interlaces (riemannXiJensenPolynomial d n) (riemannXiJensenPolynomial (d + 1) n) := by
  apply (strictInterl_riemannXiJensenPolynomial_succ hRH d n).toInterlaces
  simp only [natDegree_riemannXiJensenPolynomial]

/-- RH excludes a common root in consecutive xi Jensen degrees at a fixed shift. -/
theorem riemannXiJensenPolynomial_succ_no_common_root
    (hRH : RiemannHypothesis) (d n : ℕ) (r : ℝ) :
    ¬ ((riemannXiJensenPolynomial d n).IsRoot r ∧
      (riemannXiJensenPolynomial (d + 1) n).IsRoot r) := by
  exact jensenPolynomial_succ_no_common_root (by simpa using (riemannXiCoeff_pos n).ne') d
    (isSimpleRealRooted_riemannXiJensenPolynomial hRH (d + 1) n).2.2 r

end RealRooted
