import RealRooted.FactorialCompression.Compression
import RealRooted.FactorialCompression.RootGeometry

/-!
# Exact kernel geometry for the final factorial-compression manuscript

The coefficients, degree, and strict root order are proved for all admissible
levels `ell ≤ N` and all positive real parameters `a`. The root sign calculation
uses the manuscript's derivative identity. The exceptional `N + ell = 1`
case belongs to the main theorem's constant/linear argument.
-/

open Polynomial RealRooted

noncomputable section
namespace RealRooted.FactorialCompression

private theorem beta_pos (N ell : ℕ) (a : ℝ) (hell : ell ≤ N) (ha : 0 < a) :
    0 < beta N ell a := by
  unfold beta
  have hcast : (ell : ℝ) ≤ (N : ℝ) := by exact_mod_cast hell
  apply mul_pos
  · linarith
  · have hdiv : 0 < a / (((N + ell : ℕ) : ℝ) + 1) :=
      div_pos ha (by positivity)
    linarith

/-- Every supported coefficient is strictly positive, including both parity
endpoints. The bound `ell ≤ N` gives the required factor `N + 1 - k > 0`. -/
theorem kernel_coeff_pos (N ell : ℕ) (a : ℝ) (k : ℕ)
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a)
    (hk : 2 * k ≤ N + ell + 1) : 0 < (kernel N ell a).coeff k := by
  rw [coeff_kernel_of_le N ell a k hN hk]
  have hkN : k ≤ N := by lia
  have hcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  have hlinear : 0 < (N : ℝ) + 1 - (k : ℝ) := by linarith
  have hak : 0 < a + (k : ℝ) := by positivity
  exact mul_pos (mul_pos (by positivity) hlinear) hak

theorem kernel_nonneg (N ell : ℕ) (a : ℝ)
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a) :
    HasNonnegCoeffs (kernel N ell a) := by
  intro k
  by_cases hk : 2 * k ≤ N + ell + 1
  · exact le_of_lt (kernel_coeff_pos N ell a k hN hell ha hk)
  · rw [coeff_kernel N ell a k hN, if_neg hk]

theorem kernel_ne_zero (N ell : ℕ) (a : ℝ)
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a) : kernel N ell a ≠ 0 := by
  intro hz
  have hpos := kernel_coeff_pos N ell a 0 hN hell ha (by lia)
  simp [hz] at hpos

theorem kernel_pos_leading (N ell : ℕ) (a : ℝ)
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a) :
    0 < (kernel N ell a).leadingCoeff :=
  (kernel_nonneg N ell a hN hell ha).pos_leadingCoeff
    (kernel_ne_zero N ell a hN hell ha)

theorem kernel_natDegree (N ell : ℕ) (a : ℝ)
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a) :
    (kernel N ell a).natDegree = (N + ell + 1) / 2 := by
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_kernel N ell a k hN, if_neg (by lia)]
  · apply le_natDegree_of_ne_zero
    exact ne_of_gt (kernel_coeff_pos N ell a ((N + ell + 1) / 2)
      hN hell ha (by lia))

/-- Exact root quotient from equation (3.3), without assuming a quotient sign
or interlacing as a new premise. -/
private theorem h_previous_root_ratio (r : ℕ) (hr : 2 ≤ r) (s : ℝ)
    (hs : (h r).IsRoot s) :
    (h (r - 1)).eval s / (h r).derivative.eval s = -2 * s / (r : ℝ) := by
  have hsimple := h_simple_negative r hr
  have hdne := hsimple.hasSimpleRoots.eval_derivative_ne_zero hs
  have hrne : (r : ℝ) ≠ 0 := by positivity
  have heval : (h (r - 1)).eval s =
      -(2 / (r : ℝ)) * s * (h r).derivative.eval s := by
    rw [h_previous_derivative r (by lia)]
    simp only [eval_sub, eval_mul, eval_C, eval_X, hs.eq_zero]
    ring
  rw [heval]
  field_simp

/-- The full manuscript Lemma 3.3, including simplicity and strict negativity
of every kernel root. -/
theorem kernel_strictRootGeometry (N ell : ℕ) (a : ℝ)
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a) (hm : 2 ≤ N + ell) :
    SimpleNegativeRoots (kernel N ell a) ∧
      StrictRootInterl (h (N + ell)) (kernel N ell a) := by
  have hf := h_simple_negative (N + ell) hm
  apply root_sign_criterion hf (h_pos_leading (N + ell))
    (by rw [h_natDegree]; lia) (kernel_nonneg N ell a hN hell ha)
    (kernel_coeff_pos N ell a 0 hN hell ha (by lia))
    (kernel_pos_leading N ell a hN hell ha)
    (by rw [kernel_natDegree N ell a hN hell ha, h_natDegree]; lia)
  intro s hs
  have hsneg : s < 0 := hf.2.2.2 s ((mem_roots hf.1).mpr hs)
  have hratio : 0 < (h (N + ell - 1)).eval s /
      (h (N + ell)).derivative.eval s := by
    rw [h_previous_root_ratio (N + ell) hm s hs]
    exact div_pos (by linarith) (by positivity)
  have heval : (kernel N ell a).eval s =
      (beta N ell a * s - 1 / 4) * (h (N + ell - 1)).eval s := by
    simp [kernel, hs.eq_zero]
  rw [heval, mul_div_assoc]
  have hbetas : beta N ell a * s < 0 :=
    mul_neg_of_pos_of_neg (beta_pos N ell a hell ha) hsneg
  exact mul_neg_of_neg_of_pos (by linarith) hratio

end RealRooted.FactorialCompression
