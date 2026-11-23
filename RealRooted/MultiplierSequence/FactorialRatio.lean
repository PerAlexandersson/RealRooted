module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PochhammerConvolution
import RealRooted.MultiplierSequence.Laguerre
import RealRooted.MultiplierSequence.Arithmetic
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# A factorial-ratio multiplier sequence

The sequence `(2k)! / (3k)!` is a PF multiplier sequence. Its arithmetic
subsequences therefore give entire positive Type-I functions at every stride
and starting index. These are Craven--Csordas (2006), Theorem 3.13 and
Corollary 3.16, with the zero-stride boundary included.

The proof uses the reciprocal-Pochhammer convolution and an Euler factor,
so no quotient of Gamma values at poles occurs.
-/

public section

open Polynomial

namespace RealRooted

/-- Tripling the index splits a factorial into its three residue classes. -/
private theorem factorial_three_mul (n : ℕ) :
    ((3 * n).factorial : ℝ) = (27 : ℝ) ^ n *
      (ascPochhammer ℝ n).eval (1 / 3) *
      (ascPochhammer ℝ n).eval (2 / 3) * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by lia,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ,
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ, pow_succ]
    push_cast
    rw [ih]
    ring

/-- The Euler factor cancels the shifted Pochhammer parameter exactly. -/
private theorem factorial_ratio_eq_pochhammerConvolution (n : ℕ) :
    ((2 * n).factorial : ℝ) / (3 * n).factorial =
      3 * (1 / 27 : ℝ) ^ n * ((n : ℝ) + 1 / 3) *
        ((ascPochhammer ℝ n).eval ((4 / 3 : ℝ) + 2 / 3 + n - 1) /
          ((ascPochhammer ℝ n).eval (4 / 3) *
            (ascPochhammer ℝ n).eval (2 / 3))) := by
  have hfac := factorial_mul_ascPochhammer ℝ n n
  rw [← two_mul n] at hfac
  have hshift := ascPochhammer_eval_succ n (1 / 3 : ℝ)
  rw [show (1 / 3 : ℝ) + 1 = 4 / 3 by norm_num] at hshift
  rw [show (4 / 3 : ℝ) + 2 / 3 + n - 1 = n + 1 by ring,
    factorial_three_mul]
  have h₁ := (ascPochhammer_pos n (1 / 3 : ℝ) (by norm_num)).ne'
  have h₂ := (ascPochhammer_pos n (2 / 3 : ℝ) (by norm_num)).ne'
  have h₄ := (ascPochhammer_pos n (4 / 3 : ℝ) (by norm_num)).ne'
  rw [one_div_pow]
  field_simp
  linear_combination -(ascPochhammer ℝ n).eval (4 / 3) * hfac +
    3 * (n.factorial : ℝ) *
      (ascPochhammer ℝ n).eval ((n : ℝ) + 1) * hshift

/-- The factorial ratios `(2k)! / (3k)!` form a PF multiplier sequence
(Craven--Csordas, 2006, Theorem 3.13). -/
theorem isPFMultiplierSequence_factorial_two_mul_div_three_mul :
    IsPFMultiplierSequence (fun k => ((2 * k).factorial : ℝ) / (3 * k).factorial) := by
  have hbase := (isPFMultiplierSequence_natCast_add (by norm_num : (0 : ℝ) ≤ 1 / 3)).mul
    (isPFMultiplierSequence_pochhammerConvolution
      (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (0 : ℝ) < 2 / 3))
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  intro d
  have hp₀ := isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hbase d
  have hp₁ := hp₀.comp_C_mul_X_add_C (by norm_num : (0 : ℝ) < 1 / 27) le_rfl
  have hp := hp₁.const_mul (by norm_num : (0 : ℝ) < 3)
  convert hp using 1
  ext k
  rw [coeff_jensenPolynomial, coeff_C_mul]
  simp only [C_0, add_zero, comp_C_mul_X_coeff, coeff_jensenPolynomial]
  split_ifs
  · rw [factorial_ratio_eq_pochhammerConvolution]
    ring
  · ring

/-- Every arithmetic subsequence of the factorial ratios is a PF multiplier
sequence, extending Craven--Csordas (2006), Corollary 3.16. -/
theorem isPFMultiplierSequence_factorial_ratio_arithmetic (r s : ℕ) :
    IsPFMultiplierSequence (fun k =>
      ((2 * (s + r * k)).factorial : ℝ) / (3 * (s + r * k)).factorial) :=
  isPFMultiplierSequence_factorial_two_mul_div_three_mul.arithmetic r s

/-- Every arithmetic factorial-ratio exponential generating function belongs
to the positive Type-I Laguerre--Pólya class, with actual entire convergence. -/
theorem isLaguerrePolyaTypeI_factorial_ratio_arithmetic (r s : ℕ) :
    IsLaguerrePolyaTypeI (complexExpGeneratingFunction (fun k =>
      ((2 * (s + r * k)).factorial : ℝ) / (3 * (s + r * k)).factorial)) :=
  IsPFMultiplierSequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction
    (isPFMultiplierSequence_factorial_ratio_arithmetic r s)

end RealRooted
