module

public import RealRooted.EvenDerivative.Basic
public import RealRooted.PFPolynomial
import RealRooted.EvenDerivative.Stability
import RealRooted.Mathlib.Algebra.Polynomial.Splits.FinRoots
import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import RealRooted.ClassicalHurwitzMatrix.Stability.HermiteBiehler

/-!
# Finite-degree criterion for even-derivative PF preservers

For `T_c f = ∑ₖ cₖ xᵏ f^{(2k)}` with `c 0 = 1` and `cₖ ≥ 0`, and every `N`, the following are
equivalent (`RealRooted.EvenDerivative.isPFPolynomial_tfae`):

1. `T_c` maps PF polynomials of degree at most `N` to PF polynomials;
2. the single image `T_c(uᴺ)` is real-rooted;
3. the test polynomial `p_N(z) = ∑_{k ≤ N/2} (-1)ᵏ cₖ (N)_{2k} z^{N-2k}` is real-rooted.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

variable {c : ℕ → ℝ}

/-- The test polynomials are real-rooted in all degrees below a real-rooted one:
`p_N^{(N-n)} = (N)_{N-n} p_n`. -/
theorem splits_evenDerivativeTest_of_le {n N : ℕ} (hn : n ≤ N)
    (h : (evenDerivativeTest c N).Splits) : (evenDerivativeTest c n).Splits := by
  have h1 := h.iterate_derivative (N - n)
  rw [iterate_derivative_evenDerivativeTest hn] at h1
  have hne : (C (N.descFactorial (N - n) : ℝ) : ℝ[X]) ≠ 0 := by
    simp [(Nat.descFactorial_pos.2 (Nat.sub_le N n)).ne']
  exact (splits_mul_iff_right hne (Splits.C _)).1 h1

/-- **Sufficiency.**  If the test polynomial `p_N` is real-rooted, then `T_c` maps every PF
polynomial of degree at most `N` to a PF polynomial. -/
theorem isPFPolynomial_evenDerivativeOperator (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) {N : ℕ}
    (htest : (evenDerivativeTest c N).Splits) {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hdeg : f.natDegree ≤ N) : IsPFPolynomial (evenDerivativeOperator c f) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simpa using IsPFPolynomial.zero
  refine IsPFPolynomial.of_realRooted_nonneg (HasNonnegCoeffs.evenDerivativeOperator hc
    hf.hasNonnegCoeffs) ?_
  obtain ⟨r, hr, hfr⟩ := Polynomial.Splits.exists_fin_eq_C_mul_prod hf.splits
  have hrnonpos : ∀ i, r i ≤ 0 := fun i => hf.roots_nonpos _ (by rw [← hr]; simp)
  have hf' : f = C f.leadingCoeff * ∏ i, (X + C (-r i)) := by
    simpa [sub_eq_add_neg] using hfr
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
  rw [hf', evenDerivativeOperator_C_mul hlc]
  exact (splits_evenDerivativeOperator_prod hc0
    (splits_evenDerivativeTest_of_le hdeg htest) _ fun i => neg_nonneg.2 (hrnonpos i)).C_mul _

/-- If the single image `T_c(uᴺ)` is real-rooted, so is the test polynomial `p_N`. -/
theorem splits_evenDerivativeTest_of_splits_operator_X_pow (hc : ∀ k, 0 ≤ c k)
    {N : ℕ} (h : (evenDerivativeOperator c (X ^ N)).Splits) :
    (evenDerivativeTest c N).Splits := by
  have hnn := HasNonnegCoeffs.evenDerivativeOperator hc (hasNonnegCoeffs_X.pow N)
  have hroots := (IsPFPolynomial.of_realRooted_nonneg hnn h).roots_nonpos
  have h1 := Polynomial.Splits.comp_neg_X_sq_of_roots_nonpos h hroots
  rw [evenDerivativeOperator_X_pow_comp] at h1
  have hne : (C ((-1 : ℝ) ^ N) * X ^ N : ℝ[X]) ≠ 0 := by simp
  exact (splits_mul_iff_right hne ((Splits.C _).mul (Splits.X_pow N))).1 h1

/-- If the test polynomial `p_N` is real-rooted, so is the single image `T_c(uᴺ)`. -/
theorem splits_evenDerivativeOperator_X_pow_of_splits_test (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k)
    {N : ℕ} (h : (evenDerivativeTest c N).Splits) :
    (evenDerivativeOperator c (X ^ N)).Splits :=
  (isPFPolynomial_evenDerivativeOperator hc0 hc h (isPFPolynomial_X_pow N)
    (by simp)).splits

/-- If the single image `T_c(uᴺ)` is real-rooted, then `T_c` maps PF polynomials of degree at most
`N` to PF polynomials. -/
theorem isPFPolynomial_evenDerivativeOperator_of_splits_X_pow (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k)
    {N : ℕ} (h : (evenDerivativeOperator c (X ^ N)).Splits) {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hdeg : f.natDegree ≤ N) : IsPFPolynomial (evenDerivativeOperator c f) :=
  isPFPolynomial_evenDerivativeOperator hc0 hc
    (splits_evenDerivativeTest_of_splits_operator_X_pow hc h) hf hdeg

/-- **Finite-degree criterion.**  For `c 0 = 1` and `cₖ ≥ 0`, the following are equivalent:
`T_c` maps PF polynomials of degree at most `N` to PF polynomials; the single image `T_c(uᴺ)`
is real-rooted; the test polynomial `p_N` is real-rooted. -/
theorem EvenDerivative.isPFPolynomial_tfae (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) (N : ℕ) :
    List.TFAE
      [∀ f : ℝ[X], IsPFPolynomial f → f.natDegree ≤ N → IsPFPolynomial (evenDerivativeOperator c f),
       (evenDerivativeOperator c (X ^ N)).Splits,
       (evenDerivativeTest c N).Splits] := by
  tfae_have 1 → 2 := fun h => (h _ (isPFPolynomial_X_pow N) (by simp)).splits
  tfae_have 2 → 3 := splits_evenDerivativeTest_of_splits_operator_X_pow hc
  tfae_have 3 → 1 := fun h f hf hdeg => isPFPolynomial_evenDerivativeOperator hc0 hc h hf hdeg
  tfae_finish

end RealRooted
