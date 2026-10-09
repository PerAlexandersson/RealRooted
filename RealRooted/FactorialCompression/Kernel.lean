import RealRooted.MaWang.Strong
import RealRooted.FactorialCompression.CommonKernel

/-!
# Geometry of the degree-changing kernel

For `ℓ ≤ N`, `N ≠ 0` and `a > 0` the coefficients of `kernel N ℓ a` are positive on its support,
its degree is `(N + ℓ + 1) / 2`, and (when `N + ℓ ≥ 2`) the common kernel `h_{N+ℓ}` and
`kernel N ℓ a` strictly interlace, have no common root, and all roots of the kernel are negative
(Zhang, SSRN 7510941).  The case `N + ℓ = 1` is left to the constant/linear argument of the
main theorem.
-/

open Polynomial

namespace RealRooted.FactorialCompression

private theorem kernelBeta_pos {N ℓ : ℕ} {a : ℝ} (hℓ : ℓ ≤ N) (ha : 0 < a) :
    0 < kernelBeta N ℓ a := by
  unfold kernelBeta
  have hcast : (ℓ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hℓ
  refine mul_pos (by linarith) ?_
  have hdiv : 0 < a / (((N + ℓ : ℕ) : ℝ) + 1) := div_pos ha (by positivity)
  linarith

/-- Every supported coefficient of the kernel is strictly positive, at both parity endpoints.
The bound `ℓ ≤ N` gives the factor `N + 1 - k > 0`. -/
theorem coeff_kernel_pos {N ℓ : ℕ} {a : ℝ} {k : ℕ} (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a)
    (hk : 2 * k ≤ N + ℓ + 1) : 0 < (kernel N ℓ a).coeff k := by
  rw [coeff_kernel_of_le N ℓ a k hN hk]
  have hcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show k ≤ N by lia)
  have hlinear : 0 < (N : ℝ) + 1 - (k : ℝ) := by linarith
  have hak : 0 < a + (k : ℝ) := by positivity
  exact mul_pos (mul_pos (by positivity) hlinear) hak

/-- The kernel has nonnegative coefficients. -/
theorem hasNonnegCoeffs_kernel {N ℓ : ℕ} {a : ℝ} (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a) :
    HasNonnegCoeffs (kernel N ℓ a) := by
  intro k
  by_cases hk : 2 * k ≤ N + ℓ + 1
  · exact (coeff_kernel_pos hN hℓ ha hk).le
  · rw [coeff_kernel N ℓ a k hN, ite_eq_right hk]

/-- The kernel is nonzero. -/
theorem kernel_ne_zero {N ℓ : ℕ} {a : ℝ} (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a) :
    kernel N ℓ a ≠ 0 := by
  intro hz
  have hpos := coeff_kernel_pos (k := 0) hN hℓ ha (by lia)
  simp [hz] at hpos

/-- The kernel has a positive leading coefficient. -/
theorem hasPosLeadingCoeff_kernel {N ℓ : ℕ} {a : ℝ} (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a) :
    HasPosLeadingCoeff (kernel N ℓ a) :=
  (hasNonnegCoeffs_kernel hN hℓ ha).pos_leadingCoeff (kernel_ne_zero hN hℓ ha)

/-- The degree of the kernel `K_{N,ℓ,a}` is `⌊(N + ℓ + 1) / 2⌋`. -/
theorem natDegree_kernel {N ℓ : ℕ} {a : ℝ} (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a) :
    (kernel N ℓ a).natDegree = (N + ℓ + 1) / 2 := by
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_kernel N ℓ a k hN, ite_eq_right (by lia)]
  · exact le_natDegree_of_ne_zero (coeff_kernel_pos hN hℓ ha (k := (N + ℓ + 1) / 2) (by lia)).ne'

/-- At a root `s` of `h_{r+1}`, the previous kernel `h_r` takes the value
`-(2 / (r + 1)) s h_{r+1}'(s)`. -/
private theorem eval_commonKernel_of_isRoot_succ (r : ℕ) {s : ℝ}
    (hs : (commonKernel (r + 1)).IsRoot s) :
    (commonKernel r).eval s =
      -(2 / ((r : ℝ) + 1)) * s * (commonKernel (r + 1)).derivative.eval s := by
  rw [commonKernel_eq_sub_derivative r]
  simp only [eval_sub, eval_mul, eval_C, eval_X, hs.eq_zero]
  ring

/-- For `ℓ ≤ N`, `N ≠ 0`, `a > 0` and `N + ℓ ≥ 2`, the common kernel `h_{N+ℓ}` and `K_{N,ℓ,a}`
strictly interlace, have no common root, and all roots of the kernel are negative
(Zhang, SSRN 7510941). -/
theorem strictInterl_commonKernel_kernel {N ℓ : ℕ} {a : ℝ} (hN : N ≠ 0) (hℓ : ℓ ≤ N)
    (ha : 0 < a) (hm : 2 ≤ N + ℓ) :
    StrictInterl (commonKernel (N + ℓ)) (kernel N ℓ a) ∧
      (∀ r, (commonKernel (N + ℓ)).IsRoot r → ¬ (kernel N ℓ a).IsRoot r) ∧
      ∀ r ∈ (kernel N ℓ a).roots, r < 0 := by
  have hsimple := hasSimpleRoots_commonKernel hm
  refine strictInterl_and_noCommonRoot_of_eval_mul_derivative_neg (splits_commonKernel hm)
    (hasPosLeadingCoeff_commonKernel _) (by rw [natDegree_commonKernel]; lia)
    (hasNonnegCoeffs_kernel hN hℓ ha) (coeff_kernel_pos (k := 0) hN hℓ ha (by lia))
    (by rw [natDegree_kernel hN hℓ ha, natDegree_commonKernel]; lia) ?_
  intro s hs
  have hd := hsimple.eval_derivative_ne_zero hs
  have hsneg := lt_zero_of_isRoot_commonKernel hs
  have hs' : (commonKernel (N + ℓ - 1 + 1)).IsRoot s := by
    rwa [show N + ℓ - 1 + 1 = N + ℓ by lia]
  have hprev := eval_commonKernel_of_isRoot_succ (N + ℓ - 1) hs'
  rw [show N + ℓ - 1 + 1 = N + ℓ by lia] at hprev
  have heval : (kernel N ℓ a).eval s =
      (kernelBeta N ℓ a * s - 1 / 4) * (commonKernel (N + ℓ - 1)).eval s := by
    simp [kernel, hs.eq_zero]
  have hbeta : kernelBeta N ℓ a * s < 0 := mul_neg_of_pos_of_neg (kernelBeta_pos hℓ ha) hsneg
  have hc : 0 < 2 / (((N + ℓ - 1 : ℕ) : ℝ) + 1) := by positivity
  have hsq : 0 < (commonKernel (N + ℓ)).derivative.eval s ^ 2 := by positivity
  rw [heval, hprev]
  have hfac : (kernelBeta N ℓ a * s - 1 / 4) *
      (-(2 / (((N + ℓ - 1 : ℕ) : ℝ) + 1)) * s) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by nlinarith)
  calc (kernelBeta N ℓ a * s - 1 / 4) *
        (-(2 / (((N + ℓ - 1 : ℕ) : ℝ) + 1)) * s * (commonKernel (N + ℓ)).derivative.eval s) *
          (commonKernel (N + ℓ)).derivative.eval s
      = (kernelBeta N ℓ a * s - 1 / 4) *
          (-(2 / (((N + ℓ - 1 : ℕ) : ℝ) + 1)) * s) *
          (commonKernel (N + ℓ)).derivative.eval s ^ 2 := by ring
    _ < 0 := mul_neg_of_neg_of_pos hfac hsq

end RealRooted.FactorialCompression
