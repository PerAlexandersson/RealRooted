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
    (hrr : p.Splits) (hnn : HasNonnegCoeffs p) (hzero : 0 < p.eval 0) :
    ∀ r ∈ p.roots, r < 0 := by
  intro r hr
  have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hrr hnn r hr
  by_contra hnot
  have hr_zero : r = 0 := le_antisymm hr_nonpos (not_lt.mp hnot)
  simp_all

end RealRooted
