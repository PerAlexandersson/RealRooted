module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import RealRooted.SimpleRoots
import RealRooted.Laguerre.Roots
import RealRooted.Interlacing.Reversal
import Mathlib.Tactic

/-!
# The balanced matching seed for bipartite heat deformation

The matching polynomial `Mₙ(v) = ∑ₖ binom(n,k)² k! vᵏ` is the reversed
monic sign-reversed Laguerre polynomial. Source: the unpublished heat argument
in https://github.com/PerAlexandersson/RealRooted/issues/2646.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.BipartiteHeat

/-- The matching seed on a balanced complete bipartite graph, in Laguerre normalization. -/
def matchingSeed (n : ℕ) : ℝ[X] := (generalizedLaguerre n (0 : ℝ)).reverse

/-- The coefficient of the matching seed counts choices of endpoints and a bijection. -/
theorem coeff_matchingSeed (n k : ℕ) :
    (matchingSeed n).coeff k = (n.choose k : ℝ) ^ 2 * k.factorial := by
  rw [matchingSeed, coeff_reverse, natDegree_generalizedLaguerre]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, coeff_generalizedLaguerre, ite_eq_left (by lia), Nat.choose_symm hk]
    have he : (ascPochhammer ℝ (n - (n - k))).eval ((0 : ℝ) + (n - k : ℕ) + 1) =
        (n.descFactorial k : ℝ) := by
      rw [Nat.sub_sub_self hk]
      have harg : (0 : ℝ) + (n - k : ℕ) + 1 = ((n - k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [harg, ascPochhammer_nat_eq_natCast_descFactorial]
      rw [show n - k + 1 + k - 1 = n by lia]
    rw [he, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  · rw [revAt_eq_self_of_lt (by lia), coeff_generalizedLaguerre, ite_eq_right hk,
      Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, zero_pow (by decide), zero_mul]

/-- The seed has degree exactly its index. -/
theorem matchingSeed_natDegree (n : ℕ) : (matchingSeed n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (reverse_natDegree_le _).trans (natDegree_generalizedLaguerre_le _ _)
  · rw [coeff_matchingSeed, Nat.choose_self, Nat.cast_one, one_pow, one_mul]
    exact_mod_cast Nat.factorial_ne_zero n

/-- The Laguerre seed is exactly the usual finite matching-polynomial formula. -/
theorem matchingSeed_eq_sum (n : ℕ) :
    matchingSeed n = ∑ k ∈ Finset.range (n + 1),
      C ((n.choose k : ℝ) ^ 2 * k.factorial) * X ^ k := by
  simpa only [matchingSeed_natDegree, coeff_matchingSeed] using
    (matchingSeed n).as_sum_range_C_mul_X_pow

/-- The seed has unit constant term. -/
@[simp] theorem matchingSeed_coeff_zero (n : ℕ) : (matchingSeed n).coeff 0 = 1 := by
  simp only [coeff_matchingSeed, Nat.choose_zero_right, Nat.cast_one, one_pow,
    Nat.factorial_zero, mul_one]

/-- Every seed coefficient is nonnegative. -/
theorem matchingSeed_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (matchingSeed n) := by
  intro k
  rw [coeff_matchingSeed]
  positivity

/-- Differentiating the next matching seed gives the square-index multiple of this seed. -/
theorem derivative_matchingSeed (n : ℕ) :
    (matchingSeed (n + 1)).derivative = C ((n + 1 : ℝ) ^ 2) * matchingSeed n := by
  ext k
  rw [coeff_derivative, coeff_matchingSeed, coeff_C_mul, coeff_matchingSeed]
  have h := congrArg (fun m : ℕ => (m : ℝ)) (Nat.add_one_mul_choose_eq n k)
  push_cast at h
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = (((n + 1).choose (k + 1) : ℝ) * (k + 1)) ^ 2 * k.factorial := by ring
    _ = ((n + 1 : ℝ) * n.choose k) ^ 2 * k.factorial := by rw [← h]
    _ = _ := by ring

/-- Consecutive matching seeds interlace. -/
theorem matchingSeed_interlaces (n : ℕ) :
    Interlaces (matchingSeed n) (matchingSeed (n + 1)) := by
  exact interlaces_reverse_of_roots_neg
    (generalizedLaguerre_interlaces_succ n (by norm_num))
    (generalizedLaguerre_roots_neg (n + 1) (by norm_num))
    (generalizedLaguerre_roots_neg n (by norm_num))

/-- Every matching seed is nonzero, split, and has only simple real roots. -/
theorem matchingSeed_isSimpleRealRooted (n : ℕ) : IsSimpleRealRooted (matchingSeed n) := by
  have hne := (matchingSeed_interlaces n).2.1.1
  have hs := (matchingSeed_interlaces n).2.1.2
  refine ⟨hne, hs, HasSimpleRoots.of_roots_nodup hne ?_⟩
  have h₀ : (generalizedLaguerre n (0 : ℝ)).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, generalizedLaguerre_eval_zero, zero_add,
      ← Nat.cast_factorial]
    exact_mod_cast Nat.factorial_ne_zero n
  rw [matchingSeed, roots_reverse_eq_map_inv
    (generalizedLaguerre_splits n (by norm_num)) h₀]
  exact (generalizedLaguerre_roots_nodup_of_neg_one_lt n (by norm_num)).map
    (fun _ _ h => inv_injective h)

/-- Consecutive matching seeds have no common real root. -/
theorem matchingSeed_no_common_root (n : ℕ) (x : ℝ) :
    ¬ ((matchingSeed n).IsRoot x ∧ (matchingSeed (n + 1)).IsRoot x) := by
  rintro ⟨hn, hs⟩
  have hd := (matchingSeed_isSimpleRealRooted (n + 1)).2.2.eval_derivative_ne_zero hs
  rw [derivative_matchingSeed, eval_mul, eval_C, hn.eq_zero, mul_zero] at hd
  exact hd rfl

end RealRooted.BipartiteHeat
