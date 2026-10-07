import RealRooted.Hadamard.SchurSzegoMultiplicity

/-!
# Regression examples for the finite Schur–Szegő composition

* `schurSzegoComp_one_add_X_pow`: `(1 + X)ᴺ` is the identity symbol of `*_N`.
* `schurSzegoComp_X_sq_example`: the nonzero-root hypothesis of
  `rootMultiplicity_schurSzegoComp` is necessary (Kostov 2010).  For `n = 2`, `f = X²` (root `0`
  of multiplicity `2`) and `g = (X + 1)(X + 2)` (root `-1` of multiplicity `1`), the composition
  is `X²`, so `0 = -(0 * (-1))` has multiplicity `2`, not `m + l - n = 1`.
-/

open Polynomial

namespace RealRooted

/-- `(1 + X)ᴺ` is the identity for the degree-`N` Schur–Szegő composition. -/
theorem schurSzegoComp_one_add_X_pow {N : ℕ} {g : ℝ[X]} (hg : g.natDegree ≤ N) :
    schurSzegoComp N ((1 + X) ^ N) g = g := by
  ext k
  rw [coeff_schurSzegoComp_eq_div, coeff_one_add_X_pow]
  rcases le_or_gt k N with hk | hk
  · have hc : (N.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    field_simp
  · rw [Nat.choose_eq_zero_of_lt hk, coeff_eq_zero_of_natDegree_lt (hg.trans_lt hk)]
    simp

/-- The composition `X² *₂ (X + 1)(X + 2)` equals `X²`. -/
theorem schurSzegoComp_X_sq_example :
    schurSzegoComp 2 (X ^ 2) ((X + 1) * (X + 2)) = X ^ 2 := by
  ext k
  rw [coeff_schurSzegoComp_eq_div]
  rcases k with _ | _ | _ | k <;> simp [coeff_X_pow, coeff_X, mul_add, add_mul]

/-- With the zero root `a = 0` the Kostov–Shapiro multiplicity formula fails: the
multiplicity of `0` in `X² *₂ (X + 1)(X + 2)` is `2`, whereas `m + l - n = 2 + 1 - 2 = 1`. -/
example : (schurSzegoComp 2 (X ^ 2) ((X + 1) * (X + 2))).rootMultiplicity 0 = 2 := by
  rw [schurSzegoComp_X_sq_example, ← sub_zero (X : ℝ[X]), ← C_0, rootMultiplicity_X_sub_C_pow]

end RealRooted
