import RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure
import RealRooted.AissenSchoenbergWhitney

/-!
# Causal forward differences after a finite zero prefix

This leaf combines the positive-initial-value causal closure with the existing
Pólya-frequency prefix and tail operations.
-/

open Filter Polynomial Topology

namespace RealRooted

/-- A Pólya-frequency sequence with a nonzero eventual polynomial tail has a
Pólya-frequency causal forward difference. -/
theorem IsPolyaFreqSeq.causalFwdDiff_of_eventually_polynomial
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ k in atTop, a k = p.eval (k : ℝ)) :
    IsPolyaFreqSeq (Function.causalFwdDiff a) := by
  have hpos : ∀ᶠ n in atTop, 0 < a n :=
    ha.eventually_pos_of_eventually_polynomial hp hap
  rcases (eventually_atTop.1 hpos) with ⟨n, hn⟩
  have hexists : ∃ n, a n ≠ 0 := ⟨n, ne_of_gt (hn n le_rfl)⟩
  let s : ℕ := Nat.find hexists
  have hsne : a s ≠ 0 := Nat.find_spec hexists
  have hspos : 0 < a s := lt_of_le_of_ne (ha.nonneg s) (Ne.symm hsne)
  have hzero : ∀ k < s, a k = 0 := by
    intro k hk
    by_contra hk0
    exact (Nat.not_lt_of_ge (Nat.find_min' hexists hk0)) hk
  let b : ℕ → ℝ := fun n => a (n + s)
  have hpfb : IsPolyaFreqSeq b := ha.tail_of_zeros s hzero
  have hpcomp : p.comp (X + C (s : ℝ)) ≠ 0 :=
    Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hapcomp : ∀ᶠ n in atTop, b n =
      (p.comp (X + C (s : ℝ))).eval (n : ℝ) := by
    simpa [b] using Polynomial.eventually_eq_eval_nat_add hap s
  have hdiffb : IsPolyaFreqSeq (Function.causalFwdDiff b) :=
    hpfb.causalFwdDiff_of_eventually_polynomial_of_pos_zero hpcomp hapcomp (by
      simpa [b] using hspos)
  have haeq : a = fun n => if s ≤ n then b (n - s) else 0 := by
    funext m
    by_cases hsm : s ≤ m
    · rw [if_pos hsm]
      simp [b, Nat.sub_add_cancel hsm]
    · rw [if_neg hsm]
      exact hzero m (Nat.lt_of_not_ge hsm)
  rw [haeq, Function.causalFwdDiff_prefix]
  exact hdiffb.prefix_zeros s

end RealRooted
