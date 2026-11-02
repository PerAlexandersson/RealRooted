module

public import RealRooted.CombinatorialExamples.BorosMoll.Basic
public import RealRooted.NarayanaTransformation.Coefficients

/-!
# The Boros–Moll Narayana polynomial is `narayanaPolynomial 1 n`

`RealRooted.BorosMoll.narayanaN` is defined in `BorosMoll.Basic` by the explicit coefficients
`(1 / (i + 1)) * C(n, i) * C(n + 1, i)`, so that file imports little.  This module identifies it
with the generalized Narayana polynomial `RealRooted.narayanaPolynomial 1 n`, so that results of
the `NarayanaTransformation` library apply to `narayanaN`.
-/

public section

open Polynomial

namespace RealRooted.BorosMoll

/-- The `m = 1` generalized Narayana coefficient is `(1 / (k + 1)) * C(n, k) * C(n + 1, k)`. -/
theorem narayanaTransformCoeff_one_eq (n k : ℕ) :
    narayanaTransformCoeff 1 n k =
      (1 / ((k : ℝ) + 1)) * (n.choose k : ℝ) * ((n + 1).choose k : ℝ) := by
  unfold narayanaTransformCoeff
  rw [show Nat.choose (1 + k) k = k + 1 by
    simp [add_comm, Nat.choose_succ_self_right]]
  push_cast
  field_simp

/-- The Boros–Moll Narayana polynomial `N_n` is the generalized Narayana polynomial, `m = 1`. -/
theorem narayanaN_eq_narayanaPolynomial (n : ℕ) : narayanaN n = narayanaPolynomial 1 n := by
  unfold narayanaN narayanaPolynomial
  exact Finset.sum_congr rfl fun k _ => by rw [narayanaTransformCoeff_one_eq]

end RealRooted.BorosMoll
