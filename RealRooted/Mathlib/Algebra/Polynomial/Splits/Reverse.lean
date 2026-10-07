import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits

/-!
# Reversal preserves splitting

Over a field, the reversal `p.reverse` and the reflections `reflect N p` with
`p.natDegree ≤ N` of a split polynomial split.
-/

namespace Polynomial

/-- The reversal of a polynomial that splits over a field splits. -/
theorem Splits.reverse {K : Type*} [Field K] {f : K[X]} (hf : f.Splits) :
    f.reverse.Splits := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [reverse_C]
      exact Splits.C c
    · exact Splits.of_natDegree_le_one ((reverse_natDegree_le _).trans (natDegree_X_add_C c).le)
  | one =>
    rw [← C_1, reverse_C]
    exact Splits.C 1
  | mul x y _ _ hx hy =>
    rw [reverse_mul_of_domain]
    exact hx.mul hy

/-- `reflect N f` splits whenever `f` splits over a field and `f.natDegree ≤ N`. -/
theorem Splits.reflect {K : Type*} [Field K] {f : K[X]} (hf : f.Splits) {N : ℕ}
    (hN : f.natDegree ≤ N) : (reflect N f).Splits := by
  have h := reflect_mul f 1 le_rfl (natDegree_one.trans_le (Nat.zero_le (N - f.natDegree)))
  rw [mul_one, reflect_one, Nat.add_sub_cancel' hN] at h
  rw [h]
  exact hf.reverse.mul (Splits.X_pow _)

end Polynomial
