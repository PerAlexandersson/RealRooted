import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner

/-!
# Common Combinatorial Example Lemmas

Shared coefficient, leading-coefficient, and elementary interlacing helpers for
the combinatorial example files.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma roots_neg_of_nonnegCoeffs_of_eval_zero_pos {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.Splits) (hnn : HasNonnegCoeffs p) (hzero : 0 < p.eval 0) :
    ∀ r ∈ p.roots, r < 0 := by
  intro r hr
  have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hrr hnn r hr
  by_contra hnot
  have hr_zero : r = 0 := by
    linarith
  have hroot0 : p.IsRoot 0 := by
    simpa [hr_zero] using (mem_roots hrr.1).mp hr
  have hEval0 : p.eval 0 = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot0
  linarith

end RealRooted
