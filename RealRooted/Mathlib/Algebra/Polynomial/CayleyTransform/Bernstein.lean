import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra

/-!
# Bernstein expansion through the finite-degree Cayley transform

The degree-`n` Cayley transform sends the Bernstein basis element
`X ^ k * (1 + X) ^ (n - k)` to `X ^ k`. This file packages the inverse
expansion.
-/

open Polynomial BigOperators

noncomputable section

namespace Polynomial

/-- Reconstruct a polynomial from its degree-`n` Bernstein coefficients. -/
def bernsteinExpansion {R : Type*} [Semiring R]
    (n : ℕ) (q : R[X]) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k))

theorem natDegree_bernsteinExpansion_le {R : Type*} [Semiring R] [Nontrivial R]
    (n : ℕ) (q : R[X]) :
    (bernsteinExpansion n q).natDegree ≤ n := by
  unfold bernsteinExpansion
  refine natDegree_sum_le_of_forall_le (Finset.range (n + 1))
    (fun k => C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k))) ?_
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k))).natDegree ≤
        (X ^ k * (1 + X) ^ (n - k) : R[X]).natDegree :=
      natDegree_C_mul_le _ _
    _ ≤ (X ^ k : R[X]).natDegree +
        ((1 + X) ^ (n - k) : R[X]).natDegree := natDegree_mul_le
    _ ≤ k + (n - k) := by
      gcongr
      · simp
      · rw [show (1 + X : R[X]) = X + C 1 by simp [add_comm],
          natDegree_pow_X_add_C]
    _ = n := Nat.add_sub_of_le hkn

/-- The Cayley transform reads a degree-`n` Bernstein expansion as an
ordinary coefficient expansion. -/
theorem cayleyTransform_bernsteinExpansion
    {K : Type*} [Field K] {n : ℕ} {q : K[X]} (hq : q.natDegree ≤ n) :
    cayleyTransform n (bernsteinExpansion n q) = q := by
  rw [bernsteinExpansion, cayleyTransform_finset_sum]
  rw [q.as_sum_range_C_mul_X_pow' (n := n + 1) (by lia)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkcoeff :
      (∑ i ∈ Finset.range (n + 1), C (q.coeff i) * X ^ i).coeff k =
        q.coeff k := by
    simp [Finset.mem_range.mp hk]
  rw [hkcoeff, cayleyTransform_C_mul,
    cayleyTransform_binomialBasisRaw
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

end Polynomial
