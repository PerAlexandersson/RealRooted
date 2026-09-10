import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Mathlib.Analysis.Polynomial.Asymptotics

/-!
# Eventually polynomial Pólya-frequency sequences

This file records eventual positivity for a Pólya-frequency sequence whose
tail is given by evaluations of a nonzero polynomial.
-/

open Filter Polynomial

namespace RealRooted

/-- A Pólya-frequency sequence which eventually agrees with evaluations of a
nonzero real polynomial is eventually strictly positive. -/
theorem IsPolyaFreqSeq.eventually_pos_of_eventually_polynomial
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) :
    ∀ᶠ n in atTop, 0 < a n :=
  Polynomial.eventually_pos_of_eventually_nonneg_of_eventually_eq_eval_nat hp
    (Eventually.of_forall ha.nonneg) hap

end RealRooted
