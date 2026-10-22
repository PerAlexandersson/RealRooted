import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# Row-refined Ferrers-tiling polynomials

This file formalizes the univariate specialization in
Ahlberg--Alexandersson, *Polynomials from tilings of rectangles*,
Theorem 7.1.  The multivariate tiling model is deferred to layer 2.
-/

open Finset Polynomial

namespace RealRooted
namespace FerrersTiling

noncomputable section

/-- The specialization `S_((k,k),d,n)(s,1,...,1)`, defined by the closed
form in Ahlberg--Alexandersson, Theorem 7.1. -/
def rowRefinedSpecialization (d n : ℕ) : ℝ[X] :=
  (pathPowerCliquePolynomial 2 n).comp (X + C ((d - 1 : ℕ) : ℝ))

/-- The closed form
`sum_j binom (n-j) j (s+d-1)^j` for the row-refined specialization. -/
theorem rowRefinedSpecialization_eq_sum (d n : ℕ) :
    rowRefinedSpecialization d n =
      ∑ j ∈ range (n + 1),
        C (Nat.choose (n - j) j : ℝ) *
          (X + C ((d - 1 : ℕ) : ℝ)) ^ j := by
  rw [rowRefinedSpecialization, pathPowerCliquePolynomial]
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  congr 1
  funext j
  norm_num

/-- Every row-refined univariate specialization is real-rooted. -/
theorem rowRefinedSpecialization_splits (d n : ℕ) :
    (rowRefinedSpecialization d n).Splits := by
  apply (splits_pathPowerCliquePolynomial 2 n).comp_of_natDegree_le_one
  compute_degree

end

end FerrersTiling
end RealRooted
