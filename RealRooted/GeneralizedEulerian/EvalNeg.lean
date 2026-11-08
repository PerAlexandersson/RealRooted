module

public import RealRooted.GeneralizedEulerian
import RealRooted.PFPolynomial.LowCoefficients

/-!
# Positivity of Eulerian polynomials near zero

The Eulerian polynomial `generalizedEulerian 1 n` is PF with constant coefficient `1` and linear
coefficient `2 ^ (n + 1) - n - 2`.  The linear lower bound
`IsPFPolynomial.eval_neg_pos_of_mul_coeff_one_lt` therefore shows that it is positive at `-q` as
soon as `q * 2 ^ (n + 1) ≤ 1`.
-/

public section

namespace RealRooted

/-- **Positivity of a generalized Eulerian polynomial near zero.**  The Eulerian polynomial
`generalizedEulerian 1 n` is positive at `-q` whenever `q > 0` and `q * 2 ^ (n + 1) ≤ 1`.
It is PF with constant coefficient `1` and linear coefficient `2 ^ (n + 1) - n - 2`. -/
theorem eval_neg_generalizedEulerian_one_pos {n : ℕ} {q : ℝ} (hq : 0 < q)
    (h : q * 2 ^ (n + 1) ≤ 1) : 0 < (generalizedEulerian 1 n).eval (-q) := by
  obtain ⟨-, hnn, hsplits⟩ := generalizedEulerian_invariants (c := 1) one_pos n
  have hp := IsPFPolynomial.of_realRooted_nonneg hnn hsplits
  refine hp.eval_neg_pos_of_mul_coeff_one_lt (by simp) hq.le ?_
  rw [coeff_generalizedEulerian_one, coeff_zero_generalizedEulerian]
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **First-mode exclusion for Eulerian polynomials.**  If `q > 0` and
`k ^ (n + 1) * q ^ k ≤ q` for every `k : ℕ` (the case `k = 2` suffices), then
`generalizedEulerian 1 n` does not vanish at `-q`. -/
theorem eval_neg_generalizedEulerian_one_pos_of_pow_mul_pow_le {n : ℕ} {q : ℝ} (hq : 0 < q)
    (h : ∀ k : ℕ, (k : ℝ) ^ (n + 1) * q ^ k ≤ q) :
    0 < (generalizedEulerian 1 n).eval (-q) := by
  refine eval_neg_generalizedEulerian_one_pos hq (le_of_mul_le_mul_right ?_ hq)
  simpa [sq, mul_assoc, mul_comm, mul_left_comm] using h 2

end RealRooted
