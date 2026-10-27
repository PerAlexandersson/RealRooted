module

import RealRooted.CombinatorialExamples.PathPowerIndependence
import RealRooted.Interlacing.VariableDelay
import RealRooted.ReciprocalShift.ProperPosition
public import RealRooted.AffineFamily.Basic
public import RealRooted.PFPolynomial
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Interlacing cliques for powers of paths

We prove that the binomial polynomials

`Q(k, N) = ∑_i C(N - (k - 1)i, i) X^i`

form interlacing cliques of width `k`.  We then transfer every subsequence of
step at most `k` through degree-padded reciprocal shifts.  The last theorem is
the order-three row recurrence obtained from the third Graeffe transform; it
is the recurrence used by OEIS A193636.
-/

@[expose] public section

open Finset Polynomial RealRooted.Graph

noncomputable section

namespace RealRooted

/-- The path-power polynomial `Q(k, N) = ∑_i C(N - (k - 1)i, i) X^i`.
For `k ≥ 2`, this is the independence polynomial associated with the
`(k - 1)`-st power of a path. -/
def pathPowerCliquePolynomial (k N : ℕ) : ℝ[X] :=
  ∑ i ∈ range (N + 1), C (((N - (k - 1) * i).choose i : ℕ) : ℝ) * X ^ i

/-- Coefficients of `pathPowerCliquePolynomial`. -/
@[simp]
theorem coeff_pathPowerCliquePolynomial (k N i : ℕ) :
    (pathPowerCliquePolynomial k N).coeff i =
      ((N - (k - 1) * i).choose i : ℕ) := by
  simp only [pathPowerCliquePolynomial, finsetSum_coeff, coeff_C_mul_X_pow,
    Finset.sum_ite_eq, mem_range]
  split_ifs with hi
  · norm_cast
  · rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero]

/-- Every path-power polynomial has nonnegative coefficients. -/
theorem hasNonnegCoeffs_pathPowerCliquePolynomial (k N : ℕ) :
    HasNonnegCoeffs (pathPowerCliquePolynomial k N) := by
  intro i
  rw [coeff_pathPowerCliquePolynomial]
  positivity

/-- The constant coefficient of every path-power polynomial is one. -/
theorem pathPowerCliquePolynomial_coeff_zero (k N : ℕ) :
    (pathPowerCliquePolynomial k N).coeff 0 = 1 := by
  simp

/-- A path-power polynomial is nonzero. -/
theorem pathPowerCliquePolynomial_ne_zero (k N : ℕ) :
    pathPowerCliquePolynomial k N ≠ 0 := by
  intro hzero
  have := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
  simp at this

/-- A path-power polynomial has positive leading coefficient. -/
theorem hasPosLeadingCoeff_pathPowerCliquePolynomial (k N : ℕ) :
    HasPosLeadingCoeff (pathPowerCliquePolynomial k N) :=
  (hasNonnegCoeffs_pathPowerCliquePolynomial k N).pos_leadingCoeff
    (pathPowerCliquePolynomial_ne_zero k N)

/-- The binomial path-power polynomial is real-rooted. -/
theorem splits_pathPowerCliquePolynomial (k N : ℕ) :
    (pathPowerCliquePolynomial k N).Splits := by
  simpa [pathPowerCliquePolynomial] using splits_sum_choose_sub_mul (k - 1) N

/-- The binomial path-power polynomial is a PF polynomial. -/
theorem isPFPolynomial_pathPowerCliquePolynomial (k N : ℕ) :
    IsPFPolynomial (pathPowerCliquePolynomial k N) :=
  IsPFPolynomial.of_realRooted_nonneg
    (hasNonnegCoeffs_pathPowerCliquePolynomial k N)
    (splits_pathPowerCliquePolynomial k N)

private theorem pathPowerCliquePolynomial_eq_one_of_lt {k N : ℕ}
    (hk : 2 ≤ k) (hN : N < k) :
    pathPowerCliquePolynomial k N = 1 := by
  ext i
  rw [coeff_pathPowerCliquePolynomial]
  rcases i with _ | i
  · simp
  simp only [coeff_one, Nat.succ_ne_zero, ite_false]
  norm_cast
  apply Nat.choose_eq_zero_of_lt
  have hmul : k - 1 ≤ (k - 1) * (i + 1) := by
    exact Nat.le_mul_of_pos_right (k - 1) (Nat.succ_pos i)
  lia

private theorem pathPowerCliquePolynomial_eq_indepPolyOn {k N : ℕ} (hk : 2 ≤ k) :
    pathPowerCliquePolynomial k N =
      indepPolyOn (pathPowerGraph (k - 1)) (range (N - (k - 1))) := by
  by_cases hsmall : N < k - 1
  · rw [pathPowerCliquePolynomial_eq_one_of_lt hk (by lia)]
    have hzero : N - (k - 1) = 0 := by lia
    rw [hzero, range_zero, indepPolyOn_empty]
  · ext i
    rw [coeff_pathPowerCliquePolynomial,
      coeff_indepPolyOn_pathPowerGraph_range]
    congr 2
    lia

/-- The defining lag recurrence
`Q(k, N + k) = Q(k, N + k - 1) + X Q(k, N)`. -/
theorem pathPowerCliquePolynomial_add_lag (k N : ℕ) (hk : 2 ≤ k) :
    pathPowerCliquePolynomial k (N + k) =
      pathPowerCliquePolynomial k (N + k - 1) +
        X * pathPowerCliquePolynomial k N := by
  rw [pathPowerCliquePolynomial_eq_indepPolyOn hk,
    pathPowerCliquePolynomial_eq_indepPolyOn hk,
    pathPowerCliquePolynomial_eq_indepPolyOn hk]
  have hleft : N + k - (k - 1) = N + 1 := by lia
  have htop : N + k - 1 - (k - 1) = N := by lia
  rw [hleft, htop, indepPolyOn_pathPowerGraph_range_succ]

/-- **Path-power clique.** If `k ≥ 2`, then `Q(k, N)` strictly interlaces
`Q(k, N + j)` for every gap `1 ≤ j ≤ k`. -/
theorem strictInterl_pathPowerCliquePolynomial_add (k N j : ℕ)
    (hk : 2 ≤ k) (hjpos : 1 ≤ j) (hj : j ≤ k) :
    StrictInterl (pathPowerCliquePolynomial k N)
      (pathPowerCliquePolynomial k (N + j)) := by
  let P := pathPowerCliquePolynomial k
  let w : ℕ → ℝ := fun n ↦ if k ≤ n then 1 else 0
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    dsimp [w]
    split <;> norm_num
  have hP0 : P 0 = 1 := pathPowerCliquePolynomial_eq_one_of_lt hk (by lia)
  have hrec : ∀ n, P (n + 1) = P n + C (w (n + 1)) * X * P (n + 1 - k) := by
    intro n
    by_cases hkn : k ≤ n + 1
    · have hlag := pathPowerCliquePolynomial_add_lag k (n + 1 - k) hk
      have htop : n + 1 - k + k = n + 1 := by lia
      have hprev : n + 1 - k + k - 1 = n := by lia
      simpa [P, w, hkn, htop, hprev] using hlag
    · have hn : n < k := by lia
      have hns : n + 1 < k := by lia
      rw [show P (n + 1) = 1 by
        exact pathPowerCliquePolynomial_eq_one_of_lt hk hns]
      rw [show P n = 1 by
        exact pathPowerCliquePolynomial_eq_one_of_lt hk hn]
      simp [w, hkn]
  exact strictInterl_of_fixedDelay_recurrence P w k (by lia) hw hP0 hrec
    (Nat.lt_add_of_pos_right hjpos).le (Nat.add_le_add_left hj N)

/-- Along a subsequence whose step is at most `k`, degrees grow by at most one. -/
theorem pathPowerCliquePolynomial_subsequence_natDegree_le (k p c n : ℕ)
    (hk : 2 ≤ k) (hp : 1 ≤ p) (hpk : p ≤ k) :
    (pathPowerCliquePolynomial k (p * n + c)).natDegree ≤
      (pathPowerCliquePolynomial k c).natDegree + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hinter := strictInterl_pathPowerCliquePolynomial_add k (p * n + c) p hk hp hpk
      have hdegree := hinter.natDegree_le_succ
      rw [Nat.mul_succ]
      lia

private theorem reciprocalShift_succ_eq_X_mul {D : ℕ} {p : ℝ[X]}
    (hdegree : p.natDegree ≤ D) :
    reciprocalShift (D + 1) p = X * reciprocalShift D p := by
  ext i
  cases i with
  | zero =>
      rw [reciprocalShift, Polynomial.coeff_reflect, Polynomial.revAt_zero,
        coeff_X_mul_zero]
      exact coeff_eq_zero_of_natDegree_lt (by lia)
  | succ i =>
      rw [reciprocalShift, Polynomial.coeff_reflect, coeff_X_mul,
        reciprocalShift, Polynomial.coeff_reflect]
      by_cases hi : i ≤ D
      · simp_all
      · have hDi : D < i := by lia
        rw [Polynomial.revAt_eq_self_of_lt hDi,
          Polynomial.revAt_eq_self_of_lt (by lia : D + 1 < i + 1),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hDi),
          coeff_eq_zero_of_natDegree_lt (by lia)]

/-- Reflected path-power subsequences are strictly interlacing.  The padding
starts at the degree of the offset row and increases by one at each step, so
this statement applies to every `1 ≤ p ≤ k` and every offset `c`. -/
theorem strictInterl_reciprocalShift_pathPowerCliquePolynomial
    (k p c n : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p) (hpk : p ≤ k) :
    StrictInterl
      (reciprocalShift ((pathPowerCliquePolynomial k c).natDegree + n)
        (pathPowerCliquePolynomial k (p * n + c)))
      (reciprocalShift ((pathPowerCliquePolynomial k c).natDegree + (n + 1))
        (pathPowerCliquePolynomial k (p * (n + 1) + c))) := by
  let D := (pathPowerCliquePolynomial k c).natDegree + n
  let q := pathPowerCliquePolynomial k (p * n + c)
  let Q := pathPowerCliquePolynomial k (p * (n + 1) + c)
  have hinter : StrictInterl q Q := by
    simpa [q, Q, Nat.mul_succ, add_assoc, add_left_comm, add_comm] using
      strictInterl_pathPowerCliquePolynomial_add k (p * n + c) p hk hp hpk
  have hqdeg : q.natDegree ≤ D := by
    exact pathPowerCliquePolynomial_subsequence_natDegree_le k p c n hk hp hpk
  have hQdeg : Q.natDegree ≤ D + 1 := by
    have := pathPowerCliquePolynomial_subsequence_natDegree_le k p c (n + 1) hk hp hpk
    simpa [D, Q, add_assoc] using this
  have hshift : StrictInterl (reciprocalShift (D + 1) Q)
      (reciprocalShift (D + 1) q) :=
    reciprocalShift_reverses_strictInterl
      (isPFPolynomial_pathPowerCliquePolynomial k (p * n + c))
      (isPFPolynomial_pathPowerCliquePolynomial k (p * (n + 1) + c))
      (by lia) hQdeg hinter
  rw [reciprocalShift_succ_eq_X_mul hqdeg] at hshift
  have hresult := strictInterl_of_strictInterl_X_mul_of_nonneg hshift
    (HasNonnegCoeffs.reciprocalShift
      (hasNonnegCoeffs_pathPowerCliquePolynomial k (p * n + c)))
    (HasNonnegCoeffs.reciprocalShift
      (hasNonnegCoeffs_pathPowerCliquePolynomial k (p * (n + 1) + c)))
  simpa [D, q, Q, add_assoc] using hresult

/-- Reflected path-power subsequences are real-rooted. -/
theorem splits_reciprocalShift_pathPowerCliquePolynomial
    (k p c n : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p) (hpk : p ≤ k) :
    (reciprocalShift ((pathPowerCliquePolynomial k c).natDegree + n)
      (pathPowerCliquePolynomial k (p * n + c))).Splits :=
  (strictInterl_reciprocalShift_pathPowerCliquePolynomial k p c n hk hp hpk).1.2

/-- The trisection rows of `1 / (1 - s - X s^3)` satisfy the recurrence
coming from the third Graeffe transform:
`R(n+3) = (1+3X)R(n+2) - 3X^2 R(n+1) + X^3 R(n)`.
These are the unreflected rows of OEIS A193636. -/
theorem pathPowerCliquePolynomial_three_trisection_add_three (n : ℕ) :
    pathPowerCliquePolynomial 3 (3 * (n + 3)) =
      (1 + 3 * X) * pathPowerCliquePolynomial 3 (3 * (n + 2)) -
        3 * X ^ 2 * pathPowerCliquePolynomial 3 (3 * (n + 1)) +
          X ^ 3 * pathPowerCliquePolynomial 3 (3 * n) := by
  have hrec (m : ℕ) : pathPowerCliquePolynomial 3 (m + 3) =
      pathPowerCliquePolynomial 3 (m + 2) + X * pathPowerCliquePolynomial 3 m := by
    simpa using pathPowerCliquePolynomial_add_lag 3 m (by norm_num)
  have h0 := hrec (3 * n)
  have h2 := hrec (3 * n + 2)
  have h3 := hrec (3 * n + 3)
  have h4 := hrec (3 * n + 4)
  have h5 := hrec (3 * n + 5)
  have h6 := hrec (3 * n + 6)
  linear_combination h6 + h5 + h4 - 2 * X * h3 - X * h2 + X ^ 2 * h0

end RealRooted
